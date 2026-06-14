// csd-asic-proxy/src/main.rs
//
// Stratum v1 proxy: S21/S9 ASIC <-> CSD stratum node.
//
// Key insight from stratum.rs validate_and_submit:
//   1. coinbase = coinbase1 || worker.extranonce1 || en2 || coinbase2
//   2. cb_tx = bincode::deserialize(coinbase)
//   3. cb_txid = sha256d(bincode::serialize(stripped_cb_tx))
//      For coinbase, script_sig is NOT stripped (is_coinbase_input = true)
//      So cb_txid = sha256d(bincode::serialize(cb_tx))
//   4. merkle = merkle_root_txids([cb_txid, ...branch...])
//   5. hdr = BlockHeader { version, prev, merkle, time: ntime as u64, bits, nonce }
//   6. h = header_hash(hdr) = sha256d(84-byte buf)
//
// stratum_prev_hash does word-swap on send. Proxy receives already-swapped prev_hash.
// We must un-swap it before putting into the header.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

fn sha256d(data: &[u8]) -> [u8; 32] {
    Sha256::digest(Sha256::digest(data)).into()
}

fn from_hex(s: &str) -> Vec<u8> {
    let s = s.trim();
    (0..s.len() / 2 * 2)
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap_or(0))
        .collect()
}

fn to_hex(data: &[u8]) -> String {
    data.iter().map(|b| format!("{:02x}", b)).collect()
}

fn bits_to_target(bits: u32) -> [u8; 32] {
    let exp = ((bits >> 24) & 0xff) as usize;
    let mant = bits & 0x00ff_ffff;
    let mut target = [0u8; 32];
    if exp == 0 || mant == 0 || (mant & 0x0080_0000) != 0 || exp > 32 { return target; }
    let off = 32usize.saturating_sub(exp);
    if off + 3 <= 32 {
        target[off]     = ((mant >> 16) & 0xff) as u8;
        target[off + 1] = ((mant >>  8) & 0xff) as u8;
        target[off + 2] = ( mant        & 0xff) as u8;
    }
    target
}

fn hash_meets_target(hash: &[u8; 32], target: &[u8; 32]) -> bool {
    hash <= target
}

// stratum_prev_hash does word-swap. We receive swapped bytes, must un-swap.
fn unswap_prev_hash(swapped: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    if swapped.len() != 32 { return out; }
    for i in 0..8 {
        out[i*4]   = swapped[i*4+3];
        out[i*4+1] = swapped[i*4+2];
        out[i*4+2] = swapped[i*4+1];
        out[i*4+3] = swapped[i*4  ];
    }
    out
}

// For sending to ASIC â apply the Bitcoin word-swap (same as stratum_prev_hash)
fn btc_prev_hash_hex(h: &[u8; 32]) -> String {
    let mut out = [0u8; 32];
    for i in 0..8 {
        out[i*4]   = h[i*4+3];
        out[i*4+1] = h[i*4+2];
        out[i*4+2] = h[i*4+1];
        out[i*4+3] = h[i*4  ];
    }
    to_hex(&out)
}

// ââ Consensus types matching src/types/mod.rs âââââââââââââââââââââââââââââââââ
// Must match exactly for bincode serialization to produce same txid.

#[derive(Clone, Serialize, Deserialize)]
struct OutPoint {
    txid: [u8; 32],
    vout: u32,
}

#[derive(Clone, Serialize, Deserialize)]
struct TxIn {
    prevout: OutPoint,
    #[serde(with = "serde_bytes")]
    script_sig: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize)]
struct TxOut {
    value: u64,
    script_pubkey: [u8; 20],
}

#[derive(Clone, Serialize, Deserialize)]
enum AppPayload {
    None,
    Propose {
        domain: String,
        payload_hash: [u8; 32],
        uri: String,
        expires_epoch: u64,
    },
    Attest {
        proposal_id: [u8; 32],
        score: u32,
        confidence: u32,
    },
}

#[derive(Clone, Serialize, Deserialize)]
struct Transaction {
    version: u32,
    inputs: Vec<TxIn>,
    outputs: Vec<TxOut>,
    locktime: u32,
    app: AppPayload,
}

fn consensus_opts() -> impl bincode::Options {
    use bincode::Options;
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
}

fn coinbase_txid(cb_bytes: &[u8]) -> Option<[u8; 32]> {
    let tx: Transaction = consensus_opts().deserialize(cb_bytes).ok()?;
    // For coinbase (prevout.txid=[0;32], vout=u32::MAX), script_sig is NOT stripped
    let serialized = consensus_opts().serialize(&tx).ok()?;
    Some(sha256d(&serialized))
}

fn merkle_root(txids: &[[u8; 32]]) -> [u8; 32] {
    if txids.is_empty() { return [0u8; 32]; }
    let mut layer = txids.to_vec();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity((layer.len() + 1) / 2);
        let mut i = 0;
        while i < layer.len() {
            let l = layer[i];
            let r = if i + 1 < layer.len() { layer[i+1] } else { layer[i] };
            let mut buf = [0u8; 64];
            buf[..32].copy_from_slice(&l);
            buf[32..].copy_from_slice(&r);
            next.push(sha256d(&buf));
            i += 2;
        }
        layer = next;
    }
    layer[0]
}

fn build_csd_header(
    version: u32, prev: &[u8; 32], merkle: &[u8; 32],
    ntime32: u32, bits: u32, nonce_u32: u32,
) -> [u8; 84] {
    let mut hdr = [0u8; 84];
    hdr[0..4].copy_from_slice(&version.to_le_bytes());
    hdr[4..36].copy_from_slice(prev);
    hdr[36..68].copy_from_slice(merkle);
    // time = ntime as u64 (from validate_and_submit: time: ntime as u64)
    hdr[68..76].copy_from_slice(&(ntime32 as u64).to_le_bytes());
    hdr[76..80].copy_from_slice(&bits.to_le_bytes());
    hdr[80..84].copy_from_slice(&nonce_u32.to_le_bytes());
    hdr
}

fn send_msg(w: &Arc<Mutex<TcpStream>>, v: Value) {
    let mut line = serde_json::to_string(&v).unwrap();
    line.push('\n');
    let _ = w.lock().unwrap().write_all(line.as_bytes());
}

#[derive(Clone, Debug)]
struct Job {
    proxy_job_id:  String,
    csd_job_id:    String,
    target:        [u8; 32],
    ntime_hex:     String,
    coinbase1:     Vec<u8>,
    coinbase2:     Vec<u8>,
    merkle_branch: Vec<[u8; 32]>,
    version:       u32,
    bits:          u32,
    // Real prev hash (unswapped, ready for header_hash)
    prev:          [u8; 32],
    // prev hash swapped for sending to ASIC
    prev_swapped_hex: String,
}

fn make_notify(job: &Job, clean: bool) -> Value {
    json!({
        "id": null,
        "method": "mining.notify",
        "params": [
            job.proxy_job_id,
            job.prev_swapped_hex,
            to_hex(&job.coinbase1),
            to_hex(&job.coinbase2),
            job.merkle_branch.iter().map(|b| to_hex(b)).collect::<Vec<_>>(),
            format!("{:08x}", job.version),
            format!("{:08x}", job.bits),
            job.ntime_hex,
            clean
        ]
    })
}

fn main() {
    let upstream_addr  = std::env::var("CSD_UPSTREAM").unwrap_or_else(|_| "127.0.0.1:3333".to_string());
    let listen_addr    = std::env::var("PROXY_LISTEN").unwrap_or_else(|_| "0.0.0.0:3334".to_string());
    let proxy_password = std::env::var("PROXY_PASSWORD").ok();

    println!("[proxy] upstream:  {}", upstream_addr);
    println!("[proxy] listening: {}", listen_addr);

    let current_job: Arc<Mutex<Option<Job>>> = Arc::new(Mutex::new(None));
    let recent_jobs: Arc<Mutex<HashMap<String, Job>>> = Arc::new(Mutex::new(HashMap::new()));
    let asic_clients: Arc<Mutex<Vec<Arc<Mutex<TcpStream>>>>> = Arc::new(Mutex::new(Vec::new()));
    let upstream_en1: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(vec![0u8; 4]));
    let upstream_en2_size: Arc<Mutex<usize>> = Arc::new(Mutex::new(4));

    let up_stream = TcpStream::connect(&upstream_addr).expect("cannot connect to CSD upstream");
    let up_writer = Arc::new(Mutex::new(up_stream.try_clone().unwrap()));

    {
        let mut w = up_writer.lock().unwrap();
        for msg in [
            json!({"id":1,"method":"mining.subscribe","params":["csd-asic-proxy/1.0"]}),
            json!({"id":2,"method":"mining.authorize","params":["asic-proxy","x"]}),
        ] {
            let mut s = serde_json::to_string(&msg).unwrap(); s.push('\n');
            w.write_all(s.as_bytes()).unwrap();
        }
    }

    {
        let current_job       = current_job.clone();
        let recent_jobs       = recent_jobs.clone();
        let asic_clients      = asic_clients.clone();
        let upstream_en1      = upstream_en1.clone();
        let upstream_en2_size = upstream_en2_size.clone();
        let up_reader         = up_stream;

        thread::spawn(move || {
            let reader = BufReader::new(up_reader);
            let mut seq: u64 = 0;

            for line in reader.lines() {
                let line = match line { Ok(l) => l, Err(_) => break };
                if line.trim().is_empty() { continue; }
                let msg: Value = match serde_json::from_str(&line) { Ok(v) => v, Err(_) => continue };
                let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");

                if method.is_empty() {
                    if let Some(arr) = msg.get("result").and_then(|v| v.as_array()) {
                        if arr.len() >= 3 {
                            let en1_hex  = arr[1].as_str().unwrap_or("").to_string();
                            let en2_size = arr[2].as_u64().unwrap_or(4) as usize;
                            println!("[upstream] en1={} en2_size={}", en1_hex, en2_size);
                            *upstream_en1.lock().unwrap() = from_hex(&en1_hex);
                            *upstream_en2_size.lock().unwrap() = en2_size;
                        }
                    }
                    continue;
                }

                if method == "mining.set_difficulty" {
                    let fwd = serde_json::to_string(&msg).unwrap() + "\n";
                    let mut cs = asic_clients.lock().unwrap();
                    cs.retain(|c| c.lock().unwrap().write_all(fwd.as_bytes()).is_ok());
                    continue;
                }

                if method != "mining.notify" { continue; }

                let p = match msg.get("params").and_then(|v| v.as_array()) {
                    Some(p) if p.len() >= 9 => p.clone(), _ => continue,
                };

                let csd_job_id      = p[0].as_str().unwrap_or("").to_string();
                let prev_hash_hex   = p[1].as_str().unwrap_or("");
                let coinbase1       = from_hex(p[2].as_str().unwrap_or(""));
                let coinbase2       = from_hex(p[3].as_str().unwrap_or(""));
                let version         = u32::from_str_radix(p[5].as_str().unwrap_or("1"), 16).unwrap_or(1);
                let bits            = u32::from_str_radix(p[6].as_str().unwrap_or("0"), 16).unwrap_or(0);
                let ntime_str       = p[7].as_str().unwrap_or("0").to_string();
                let clean           = p[8].as_bool().unwrap_or(false);

                // prev_hash from stratum is already word-swapped.
                // Un-swap to get the real prev hash for header construction.
                let prev_swapped_bytes = from_hex(prev_hash_hex);
                let mut prev_swapped = [0u8; 32];
                if prev_swapped_bytes.len() == 32 { prev_swapped.copy_from_slice(&prev_swapped_bytes); }
                let prev = unswap_prev_hash(&prev_swapped);

                let merkle_branch: Vec<[u8; 32]> = p[4].as_array().unwrap_or(&vec![])
                    .iter().filter_map(|v| {
                        let b = from_hex(v.as_str().unwrap_or(""));
                        if b.len() == 32 { let mut a = [0u8;32]; a.copy_from_slice(&b); Some(a) } else { None }
                    }).collect();

                let target   = bits_to_target(bits);
                let en2_size = *upstream_en2_size.lock().unwrap();
                let _ = en2_size;

                seq += 1;
                let proxy_job_id = format!("{:08x}", seq);

                let job = Job {
                    proxy_job_id: proxy_job_id.clone(),
                    csd_job_id:   csd_job_id.clone(),
                    target,
                    ntime_hex:    ntime_str,
                    coinbase1,
                    coinbase2,
                    merkle_branch,
                    version,
                    bits,
                    prev,
                    prev_swapped_hex: prev_hash_hex.to_string(),
                };

                println!("[upstream] job={} bits={:08x}", csd_job_id, bits);

                let notify_str = serde_json::to_string(&make_notify(&job, clean)).unwrap() + "\n";
                let mut cs = asic_clients.lock().unwrap();
                cs.retain(|c| c.lock().unwrap().write_all(notify_str.as_bytes()).is_ok());

                *current_job.lock().unwrap() = Some(job.clone());
                recent_jobs.lock().unwrap().insert(proxy_job_id, job);
            }

            eprintln!("[upstream] disconnected");
            std::process::exit(1);
        });
    }

    let listener = TcpListener::bind(&listen_addr).expect("bind failed");
    println!("[proxy] ready");

    for stream in listener.incoming() {
        let stream = match stream { Ok(s) => s, Err(_) => continue };
        let peer = stream.peer_addr().map(|a| a.to_string()).unwrap_or_default();
        println!("[proxy] ASIC connected: {}", peer);

        let w            = Arc::new(Mutex::new(stream.try_clone().unwrap()));
        let w_clone      = w.clone();
        asic_clients.lock().unwrap().push(w.clone());

        let current_job  = current_job.clone();
        let recent_jobs  = recent_jobs.clone();
        let up_writer    = up_writer.clone();
        let proxy_pass   = proxy_password.clone();
        let upstream_en1 = upstream_en1.clone();
        let peer_str     = peer.clone();

        thread::spawn(move || {
            let reader = BufReader::new(stream);
            let mut msg_id: u64 = 100;
            let mut authorized = false;

            for line in reader.lines() {
                let line = match line { Ok(l) => l, Err(_) => break };
                if line.trim().is_empty() { continue; }
                let msg: Value = match serde_json::from_str(&line) {
                    Ok(v) => v, Err(e) => { eprintln!("[proxy] {peer_str} bad JSON: {e}"); continue; }
                };

                let id     = msg.get("id").cloned().unwrap_or(Value::Null);
                let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");
                let params = msg.get("params").and_then(|v| v.as_array()).cloned().unwrap_or_default();

                match method {
                    "mining.subscribe" => {
                        let en1     = upstream_en1.lock().unwrap().clone();
                        let en1_hex = to_hex(&en1);
                        send_msg(&w_clone, json!({
                            "id": id,
                            "result": [[["mining.set_difficulty","d"],["mining.notify","n"]], en1_hex, 4],
                            "error": null
                        }));
                        send_msg(&w_clone, json!({"id":null,"method":"mining.set_difficulty","params":[1000000.0]}));
                        if let Some(job) = current_job.lock().unwrap().as_ref() {
                            send_msg(&w_clone, make_notify(job, true));
                        }
                        println!("[proxy] {peer_str} subscribed en1={}", to_hex(&upstream_en1.lock().unwrap()));
                    }

                    "mining.authorize" => {
                        let pw = params.get(1).and_then(|v| v.as_str()).unwrap_or("");
                        if let Some(ref req) = proxy_pass {
                            if pw != req {
                                send_msg(&w_clone, json!({"id":id,"result":false,"error":[24,"Unauthorized",null]}));
                                break;
                            }
                        }
                        authorized = true;
                        send_msg(&w_clone, json!({"id":id,"result":true,"error":null}));
                        println!("[proxy] {peer_str} authorized");
                    }

                    "mining.extranonce.subscribe" => {
                        send_msg(&w_clone, json!({"id":id,"result":true,"error":null}));
                    }

                    "mining.submit" => {
                        if !authorized {
                            send_msg(&w_clone, json!({"id":id,"result":false,"error":[24,"Unauthorized",null]}));
                            continue;
                        }
                        if params.len() < 5 {
                            send_msg(&w_clone, json!({"id":id,"result":false,"error":[20,"bad params",null]}));
                            continue;
                        }

                        let proxy_job_id = params[1].as_str().unwrap_or("").to_string();
                        let en2_hex      = params[2].as_str().unwrap_or("").to_string();
                        let ntime_hex    = params[3].as_str().unwrap_or("").to_string();
                        let nonce_hex    = params[4].as_str().unwrap_or("").to_string();

                        // Always accept from ASIC
                        send_msg(&w_clone, json!({"id":id,"result":true,"error":null}));

                        let job = match recent_jobs.lock().unwrap().get(&proxy_job_id).cloned() {
                            Some(j) => j, None => continue,
                        };

                        let en1     = upstream_en1.lock().unwrap().clone();
                        let en2     = from_hex(&en2_hex);
                        let ntime32 = u32::from_str_radix(&ntime_hex, 16).unwrap_or(0);
                        let nonce_u32 = u32::from_str_radix(&nonce_hex, 16).unwrap_or(0);

                        // Reconstruct coinbase bytes
                        let mut cb_bytes = Vec::new();
                        cb_bytes.extend_from_slice(&job.coinbase1);
                        cb_bytes.extend_from_slice(&en1);
                        cb_bytes.extend_from_slice(&en2);
                        cb_bytes.extend_from_slice(&job.coinbase2);

                        // Compute coinbase txid using bincode (matching validate_and_submit)
                        let cb_txid = match coinbase_txid(&cb_bytes) {
                            Some(t) => t,
                            None => {
                                eprintln!("[proxy] {peer_str} failed to deserialize coinbase");
                                continue;
                            }
                        };

                        // Build merkle root
                        let mut all_txids = vec![cb_txid];
                        all_txids.extend_from_slice(&job.merkle_branch);
                        let merkle_root = merkle_root(&all_txids);

                        // Build 84-byte CSD header
                        let csd_hdr = build_csd_header(
                            job.version, &job.prev, &merkle_root, ntime32, job.bits, nonce_u32
                        );
                        let hash = sha256d(&csd_hdr);

                        println!("[submit] nonce={} hash={} target={}",
                            nonce_hex, to_hex(&hash), to_hex(&job.target));

                        if hash_meets_target(&hash, &job.target) {
                            println!("[BLOCK!] hash={}", to_hex(&hash));

                            let mut s = serde_json::to_string(&json!({
                                "id": msg_id,
                                "method": "mining.submit",
                                "params": [
                                    "asic-proxy",
                                    job.csd_job_id,
                                    en2_hex,
                                    ntime_hex,
                                    format!("{:08x}", nonce_u32)
                                ]
                            })).unwrap();
                            s.push('\n');
                            msg_id += 1;
                            let _ = up_writer.lock().unwrap().write_all(s.as_bytes());
                        }
                    }

                    _ => {
                        send_msg(&w_clone, json!({"id":id,"result":null,"error":[20,"unknown",null]}));
                    }
                }
            }

            println!("[proxy] ASIC disconnected: {}", peer_str);
        });
    }
}
