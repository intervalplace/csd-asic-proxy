// csd-asic-proxy/src/main.rs
//
// Stratum v1 proxy: sits between an S21/S9 ASIC and a CSD stratum node.
//
// CSD header (84 bytes):
//   [0..4]   version  u32 LE
//   [4..36]  prev     [u8;32]
//   [36..68] merkle   [u8;32]
//   [68..76] time     u64 LE  <- extra 4 bytes vs Bitcoin
//   [76..80] bits     u32 LE
//   [80..84] nonce    u32 LE
//
// Strategy:
//   Forward jobs to ASIC using standard stratum format.
//   For every nonce the ASIC returns, reconstruct full 84-byte CSD header
//   and check SHA-256d against CSD target.
//   Valid -> submit upstream. Invalid -> silently accept.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

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
    let mut t = [0u8; 32];
    let exp = ((bits >> 24) & 0xff) as usize;
    let mant = bits & 0x00ffffff;
    if exp < 3 || exp > 32 || mant == 0 { return t; }
    let off = 32 - exp;
    if off + 3 <= 32 {
        t[off]     = ((mant >> 16) & 0xff) as u8;
        t[off + 1] = ((mant >>  8) & 0xff) as u8;
        t[off + 2] = ( mant        & 0xff) as u8;
    }
    t
}

fn hash_meets_target(hash: &[u8; 32], target: &[u8; 32]) -> bool {
    hash <= target
}

// Bitcoin stratum prev_hash: each 4-byte word byte-reversed
fn btc_prev_hash(h: &[u8; 32]) -> String {
    let mut out = [0u8; 32];
    for i in 0..8 {
        out[i*4]   = h[i*4+3];
        out[i*4+1] = h[i*4+2];
        out[i*4+2] = h[i*4+1];
        out[i*4+3] = h[i*4  ];
    }
    to_hex(&out)
}

#[derive(Clone, Debug)]
struct Job {
    proxy_job_id:  String,
    csd_job_id:    String,
    target:        [u8; 32],
    en2_hex:       String,   // zeros, for upstream submit
    ntime_hex:     String,
    coinbase1:     Vec<u8>,
    coinbase2:     Vec<u8>,
    merkle_branch: Vec<[u8; 32]>,
    version:       u32,
    bits:          u32,
    prev:          [u8; 32],
    time64:        u64,
}

fn make_notify(job: &Job, clean: bool) -> Value {
    json!({
        "id": null,
        "method": "mining.notify",
        "params": [
            job.proxy_job_id,
            btc_prev_hash(&job.prev),
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

fn reconstruct_merkle(job: &Job, en1: &[u8], en2: &[u8]) -> [u8; 32] {
    let mut cb = Vec::new();
    cb.extend_from_slice(&job.coinbase1);
    cb.extend_from_slice(en1);
    cb.extend_from_slice(en2);
    cb.extend_from_slice(&job.coinbase2);
    let mut cur = sha256d(&cb);
    for sib in &job.merkle_branch {
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(&cur);
        buf[32..].copy_from_slice(sib);
        cur = sha256d(&buf);
    }
    cur
}

fn build_csd_header(job: &Job, merkle: &[u8; 32], ntime32: u32, nonce: u32) -> [u8; 84] {
    let mut hdr = [0u8; 84];
    hdr[0..4].copy_from_slice(&job.version.to_le_bytes());
    hdr[4..36].copy_from_slice(&job.prev);
    hdr[36..68].copy_from_slice(merkle);
    let time_hi = (job.time64 >> 32) as u32;
    let time64 = ((time_hi as u64) << 32) | (ntime32 as u64);
    hdr[68..76].copy_from_slice(&time64.to_le_bytes());
    hdr[76..80].copy_from_slice(&job.bits.to_le_bytes());
    hdr[80..84].copy_from_slice(&nonce.to_le_bytes());
    hdr
}

fn send_msg(w: &Arc<Mutex<TcpStream>>, v: Value) {
    let mut line = serde_json::to_string(&v).unwrap();
    line.push('\n');
    let _ = w.lock().unwrap().write_all(line.as_bytes());
}

fn main() {
    let upstream_addr  = std::env::var("CSD_UPSTREAM").unwrap_or_else(|_| "127.0.0.1:3333".to_string());
    let listen_addr    = std::env::var("PROXY_LISTEN").unwrap_or_else(|_| "0.0.0.0:3334".to_string());
    let proxy_password = std::env::var("csdproxy2").ok();

    println!("[proxy] upstream:  {}", upstream_addr);
    println!("[proxy] listening: {}", listen_addr);

    let current_job: Arc<Mutex<Option<Job>>> = Arc::new(Mutex::new(None));
    let recent_jobs: Arc<Mutex<HashMap<String, Job>>> = Arc::new(Mutex::new(HashMap::new()));
    let asic_clients: Arc<Mutex<Vec<Arc<Mutex<TcpStream>>>>> = Arc::new(Mutex::new(Vec::new()));

    // Connect upstream
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

    // Upstream reader thread
    {
        let current_job  = current_job.clone();
        let recent_jobs  = recent_jobs.clone();
        let asic_clients = asic_clients.clone();
        let up_reader    = up_stream;

        thread::spawn(move || {
            let reader = BufReader::new(up_reader);
            let mut en1_hex  = String::new();
            let mut en2_size = 4usize;
            let mut seq: u64 = 0;

            for line in reader.lines() {
                let line = match line { Ok(l) => l, Err(_) => break };
                if line.trim().is_empty() { continue; }
                let msg: Value = match serde_json::from_str(&line) { Ok(v) => v, Err(_) => continue };
                let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");

                if method.is_empty() {
                    if let Some(arr) = msg.get("result").and_then(|v| v.as_array()) {
                        if arr.len() >= 3 {
                            en1_hex  = arr[1].as_str().unwrap_or("").to_string();
                            en2_size = arr[2].as_u64().unwrap_or(4) as usize;
                            println!("[upstream] en1={} en2_size={}", en1_hex, en2_size);
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

                let csd_job_id = p[0].as_str().unwrap_or("").to_string();
                let prev_bytes = from_hex(p[1].as_str().unwrap_or(""));
                let coinbase1  = from_hex(p[2].as_str().unwrap_or(""));
                let coinbase2  = from_hex(p[3].as_str().unwrap_or(""));
                let version    = u32::from_str_radix(p[5].as_str().unwrap_or("1"), 16).unwrap_or(1);
                let bits       = u32::from_str_radix(p[6].as_str().unwrap_or("0"), 16).unwrap_or(0);
                let ntime32    = u32::from_str_radix(p[7].as_str().unwrap_or("0"), 16).unwrap_or(0);
                let clean      = p[8].as_bool().unwrap_or(false);

                let mut prev = [0u8; 32];
                if prev_bytes.len() == 32 { prev.copy_from_slice(&prev_bytes); }

                let merkle_branch: Vec<[u8; 32]> = p[4].as_array().unwrap_or(&vec![])
                    .iter().filter_map(|v| {
                        let b = from_hex(v.as_str().unwrap_or(""));
                        if b.len() == 32 { let mut a = [0u8;32]; a.copy_from_slice(&b); Some(a) } else { None }
                    }).collect();

                // Compute merkle using en1+zeros for en2 (template)
                let en1 = from_hex(&en1_hex);
                let en2 = vec![0u8; en2_size];
                let mut cb_tmp = Vec::new();
                cb_tmp.extend_from_slice(&coinbase1);
                cb_tmp.extend_from_slice(&en1);
                cb_tmp.extend_from_slice(&en2);
                cb_tmp.extend_from_slice(&coinbase2);
                let mut merkle_root = sha256d(&cb_tmp);
                for sib in &merkle_branch {
                    let mut buf = [0u8; 64];
                    buf[..32].copy_from_slice(&merkle_root);
                    buf[32..].copy_from_slice(sib);
                    merkle_root = sha256d(&buf);
                }

                seq += 1;
                let proxy_job_id = format!("{:08x}", seq);
                let target = bits_to_target(bits);

                let job = Job {
                    proxy_job_id: proxy_job_id.clone(),
                    csd_job_id:   csd_job_id.clone(),
                    target,
                    en2_hex:      to_hex(&en2),
                    ntime_hex:    format!("{:08x}", ntime32),
                    coinbase1,
                    coinbase2,
                    merkle_branch,
                    version,
                    bits,
                    prev,
                    time64:       ntime32 as u64,
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
    println!("[proxy] ready â waiting for ASICs");

    for stream in listener.incoming() {
        let stream = match stream { Ok(s) => s, Err(_) => continue };
        let peer = stream.peer_addr().map(|a| a.to_string()).unwrap_or_default();
        println!("[proxy] ASIC connected: {}", peer);

        let w       = Arc::new(Mutex::new(stream.try_clone().unwrap()));
        let w_job   = w.clone();
        asic_clients.lock().unwrap().push(w.clone());

        let current_job = current_job.clone();
        let recent_jobs = recent_jobs.clone();
        let up_writer   = up_writer.clone();
        let proxy_pass  = proxy_password.clone();
        let peer_str    = peer.clone();

        thread::spawn(move || {
            let reader = BufReader::new(stream);
            let mut msg_id: u64 = 100;
            let mut authorized = false;
            let en1: Vec<u8> = vec![0x00, 0x00, 0x00, 0x01];
            let en1_hex = to_hex(&en1);

            for line in reader.lines() {
                let line = match line { Ok(l) => l, Err(_) => break };
                if line.trim().is_empty() { continue; }
                let msg: Value = match serde_json::from_str(&line) {
                    Ok(v) => v,
                    Err(e) => { eprintln!("[proxy] {peer_str} bad JSON: {e}"); continue; }
                };

                let id     = msg.get("id").cloned().unwrap_or(Value::Null);
                let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");
                let params = msg.get("params").and_then(|v| v.as_array()).cloned().unwrap_or_default();

                println!("[proxy] {peer_str} {method}");

                match method {
                    "mining.subscribe" => {
                        send_msg(&w_job, json!({
                            "id": id,
                            "result": [[["mining.set_difficulty","d"],["mining.notify","n"]], en1_hex, 4],
                            "error": null
                        }));

send_msg(&w_job, json!({"id":null,"method":"mining.set_difficulty","params":[1000000.0]}));

                        if let Some(job) = current_job.lock().unwrap().as_ref() {
                            send_msg(&w_job, make_notify(job, true));
                        }
                    }

                    "mining.authorize" => {
                        let pw = params.get(1).and_then(|v| v.as_str()).unwrap_or("");
                        if let Some(ref req) = proxy_pass {
                            if pw != req {
                                eprintln!("[proxy] {peer_str} bad password");
                                send_msg(&w_job, json!({"id":id,"result":false,"error":[24,"Unauthorized",null]}));
                                break;
                            }
                        }
                        authorized = true;
                        send_msg(&w_job, json!({"id":id,"result":true,"error":null}));
                    }

                    "mining.extranonce.subscribe" => {
                        send_msg(&w_job, json!({"id":id,"result":true,"error":null}));
                    }

                    "mining.submit" => {
                        if !authorized {
                            send_msg(&w_job, json!({"id":id,"result":false,"error":[24,"Unauthorized",null]}));
                            continue;
                        }
                        if params.len() < 5 {
                            send_msg(&w_job, json!({"id":id,"result":false,"error":[20,"bad params",null]}));
                            continue;
                        }

                        let proxy_job_id = params[1].as_str().unwrap_or("").to_string();
                        let en2_hex      = params[2].as_str().unwrap_or("").to_string();
                        let ntime_hex    = params[3].as_str().unwrap_or("").to_string();
                        let nonce_hex    = params[4].as_str().unwrap_or("").to_string();

                        // Always accept from ASIC
                        send_msg(&w_job, json!({"id":id,"result":true,"error":null}));

                        let job = match recent_jobs.lock().unwrap().get(&proxy_job_id).cloned() {
                            Some(j) => j,
                            None => { println!("[proxy] stale {}", proxy_job_id); continue; }
                        };

                        let en2    = from_hex(&en2_hex);
                        let ntime32 = u32::from_str_radix(&ntime_hex, 16).unwrap_or(0);
                        let nb     = from_hex(&nonce_hex);

let nonce_le = if nb.len() == 4 {
    u32::from_le_bytes([nb[0],nb[1],nb[2],nb[3]])
} else { 0 };

                        let merkle  = reconstruct_merkle(&job, &en1, &en2);
                        let csd_hdr = build_csd_header(&job, &merkle, ntime32, nonce_le);
                        let hash    = sha256d(&csd_hdr);

                        if hash_meets_target(&hash, &job.target) {
                            println!("[BLOCK!] hash={}", to_hex(&hash));
                            let nonce_le = to_hex(&nonce_le.to_le_bytes());
                            let mut s = serde_json::to_string(&json!({
                                "id": msg_id,
                                "method": "mining.submit",
                                "params": ["asic-proxy", job.csd_job_id, job.en2_hex, job.ntime_hex, nonce_le]
                            })).unwrap();
                            s.push('\n');
                            msg_id += 1;
                            let _ = up_writer.lock().unwrap().write_all(s.as_bytes());
                        }
                    }

                    _ => {
                        send_msg(&w_job, json!({"id":id,"result":null,"error":[20,"unknown",null]}));
                    }
                }
            }

            println!("[proxy] ASIC disconnected: {}", peer_str);
        });
    }
}
