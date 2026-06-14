// csd-asic-proxy/src/main.rs
//
// Stratum v1 proxy: sits between an ASIC (S9/S21) and a CSD node.
//
// CSD header layout (84 bytes):
//   [0..4]   version  u32 LE
//   [4..36]  prev     [u8;32]
//   [36..68] merkle   [u8;32]
//   [68..76] time     u64 LE   ← 8 bytes (vs Bitcoin's 4)
//   [76..80] bits     u32 LE
//   [80..84] nonce    u32 LE
//
// Bitcoin header layout (80 bytes):
//   [0..4]   version  u32 LE
//   [4..36]  prev     [u8;32]
//   [36..68] merkle   [u8;32]
//   [68..72] time     u32 LE
//   [72..76] bits     u32 LE
//   [76..80] nonce    u32 LE
//
// Strategy:
//   - Send ASIC an 80-byte job where:
//       bytes 0..68  = CSD bytes 0..68  (version + prev + merkle)
//       bytes 68..72 = CSD bytes 68..72 (low 32 bits of u64 time)
//       bytes 72..76 = CSD bytes 76..80 (bits)
//       bytes 76..80 = 0x00000000       (nonce placeholder)
//   - The high 32 bits of CSD time (bytes 72..76) are folded into extranonce2
//     so the ASIC never sees them — but they're fixed per job so we know them.
//   - For every nonce the ASIC returns:
//       Reconstruct full 84-byte CSD header:
//         bytes 0..68  = as above
//         bytes 68..76 = original u64 time (all 8 bytes)
//         bytes 76..80 = bits
//         bytes 80..84 = nonce from ASIC
//       SHA-256d(84 bytes) → check against CSD target
//       If passes → submit to CSD node upstream
//       If not    → discard (ASIC keeps searching)

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

use serde_json::{json, Value};
use sha2::{Digest, Sha256};

// ── SHA-256d ──────────────────────────────────────────────────────────────────

fn sha256d(data: &[u8]) -> [u8; 32] {
    let first = Sha256::digest(data);
    let second = Sha256::digest(&first);
    second.into()
}

// ── Hex helpers ───────────────────────────────────────────────────────────────

fn from_hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap_or(0))
        .collect()
}

fn to_hex(data: &[u8]) -> String {
    data.iter().map(|b| format!("{:02x}", b)).collect()
}

fn to_hex_u32le(v: u32) -> String {
    let b = v.to_le_bytes();
    to_hex(&b)
}

// ── Target check ──────────────────────────────────────────────────────────────
// Both hash and target are 32-byte big-endian arrays.
// hash meets target if hash <= target numerically.

fn hash_meets_target(hash: &[u8; 32], target: &[u8; 32]) -> bool {
    hash <= target
}

fn bits_to_target(bits: u32) -> [u8; 32] {
    let mut target = [0u8; 32];
    let exp = ((bits >> 24) & 0xff) as usize;
    let mant = bits & 0x00ffffff;
    if exp == 0 || exp > 32 || mant == 0 {
        return target;
    }
    let off = 32 - exp;
    if off + 3 <= 32 {
        target[off]     = ((mant >> 16) & 0xff) as u8;
        target[off + 1] = ((mant >>  8) & 0xff) as u8;
        target[off + 2] = ( mant        & 0xff) as u8;
    }
    target
}

// ── Job context ───────────────────────────────────────────────────────────────
// Everything we need to verify a nonce returned by the ASIC.

#[derive(Clone, Debug)]
struct Job {
    job_id:      String,
    // Full 84-byte CSD header template (nonce bytes zeroed)
    csd_header:  [u8; 84],
    // CSD target derived from bits
    target:      [u8; 32],
    bits:        u32,
    // Fields needed to re-submit to CSD upstream
    csd_job_id:  String,
    en2_hex:     String,
    ntime_hex:   String,
}

// ── Upstream connection to CSD node stratum ───────────────────────────────────

struct Upstream {
    writer:   Arc<Mutex<TcpStream>>,
    msg_id:   u64,
}

impl Upstream {
    fn send(&mut self, v: Value) -> std::io::Result<()> {
        let mut line = serde_json::to_string(&v).unwrap();
        line.push('\n');
        self.writer.lock().unwrap().write_all(line.as_bytes())
    }

    fn next_id(&mut self) -> u64 {
        self.msg_id += 1;
        self.msg_id
    }
}

// ── Build 80-byte Bitcoin-compatible job from 84-byte CSD header ──────────────
//
// CSD layout:
//   [0..68]  version + prev + merkle   (same as Bitcoin)
//   [68..76] time u64 LE
//   [76..80] bits u32 LE
//   [80..84] nonce u32 LE
//
// Bitcoin layout we send to ASIC:
//   [0..68]  same
//   [68..72] low 32 bits of CSD time
//   [72..76] CSD bits
//   [76..80] nonce (zeroed, ASIC fills this)

fn csd_to_btc_header(csd: &[u8; 84]) -> [u8; 80] {
    let mut btc = [0u8; 80];
    btc[0..68].copy_from_slice(&csd[0..68]);
    btc[68..72].copy_from_slice(&csd[68..72]); // low 32 bits of time
    btc[72..76].copy_from_slice(&csd[76..80]); // bits
    // btc[76..80] = nonce = 0x00000000 (ASIC fills)
    btc
}

// ── Reconstruct CSD header with nonce from ASIC ───────────────────────────────

fn reconstruct_csd_header(template: &[u8; 84], nonce_le: u32) -> [u8; 84] {
    let mut hdr = *template;
    let nb = nonce_le.to_le_bytes();
    hdr[80] = nb[0];
    hdr[81] = nb[1];
    hdr[82] = nb[2];
    hdr[83] = nb[3];
    hdr
}

// ── Build stratum notify params for ASIC ─────────────────────────────────────
// We synthesise a fake coinbase1/coinbase2/merkle so the ASIC builds
// the 80-byte header we want.
//
// Trick: put the entire 80-byte header into coinbase1, empty coinbase2,
// empty merkle branch. extranonce1 = "00000000", extranonce2_size = 4.
// The ASIC computes coinbase = coinbase1 || en1 || en2 || coinbase2,
// then merkle_root = sha256d(coinbase) (with no branch siblings).
//
// BUT: we actually want the ASIC to vary the nonce field [76..80] of the
// 80-byte header, not a coinbase. Standard Stratum gives us ntime and nonce
// as separate fields in mining.submit — that's exactly what we need.
//
// So we use the standard Stratum job format:
//   coinbase1 = everything needed to make coinbase txid irrelevant
//   prev_hash = csd prev_hash (32 bytes, hex)
//   etc.
//
// Actually the cleanest approach: encode the entire 80-byte header split
// at the nonce boundary using coinbase fields, and use a fixed merkle root.

fn make_asic_notify(job: &Job, clean: bool) -> Value {
    let hdr = csd_to_btc_header(&job.csd_header);

    // Split header at nonce position [76..80]
    // coinbase1 = header bytes [0..76] — everything before nonce
    // coinbase2 = "" (empty)
    // The ASIC will compute: coinbase = coinbase1 || en1 || en2 || coinbase2
    // We set en1 = "" and en2_size = 0 so coinbase = header[0..76]
    // Then merkle_root = sha256d(coinbase) — but we don't use merkle from coinbase
    // Instead we pass the real merkle in the notify and let the ASIC build header normally.
    //
    // Cleaner: just use standard stratum fields directly.
    // prev_hash = hdr[4..36] (reversed per stratum convention — but CSD stratum doesn't reverse)
    // version   = hdr[0..4]
    // nbits     = hdr[72..76]
    // ntime     = hdr[68..72]
    // merkle_root in coinbase path

    let version_hex = to_hex(&hdr[0..4]);
    let prev_hash_hex = to_hex(&hdr[4..36]);
    let merkle_hex = to_hex(&hdr[36..68]);
    let ntime_hex = to_hex(&hdr[68..72]);
    let nbits_hex = to_hex(&hdr[72..76]);

    // coinbase1 = fake, just needs to produce a deterministic coinbase txid
    // We embed the merkle root directly so the ASIC uses it.
    // Use a minimal coinbase with the merkle baked in as coinbase1.
    let cb1 = to_hex(&hdr[36..68]); // merkle as coinbase1
    let cb2 = "".to_string();

    json!({
        "id": null,
        "method": "mining.notify",
        "params": [
            job.job_id,
            prev_hash_hex,
            cb1,
            cb2,
            [],           // merkle branch (empty — merkle is fixed)
            version_hex,
            nbits_hex,
            ntime_hex,
            clean
        ]
    })
}

// ── Main proxy logic ──────────────────────────────────────────────────────────

fn main() {
    let upstream_addr = std::env::var("CSD_UPSTREAM")
        .unwrap_or_else(|_| "127.0.0.1:3333".to_string());
    let listen_addr = std::env::var("PROXY_LISTEN")
        .unwrap_or_else(|_| "0.0.0.0:3334".to_string());

    println!("[proxy] CSD upstream: {}", upstream_addr);
    println!("[proxy] ASIC listen:  {}", listen_addr);

    // Shared current job + recent jobs for stale share tolerance
    let current_job: Arc<Mutex<Option<Job>>> = Arc::new(Mutex::new(None));
    let recent_jobs: Arc<Mutex<HashMap<String, Job>>> = Arc::new(Mutex::new(HashMap::new()));

    // ── Connect to CSD upstream ───────────────────────────────────────────────
    let upstream_stream = TcpStream::connect(&upstream_addr)
        .expect("Failed to connect to CSD upstream stratum");

    let upstream_writer = Arc::new(Mutex::new(
        upstream_stream.try_clone().expect("clone upstream"),
    ));

    let mut upstream = Upstream {
        writer: upstream_writer.clone(),
        msg_id: 0,
    };

    // Subscribe
    let sub_id = upstream.next_id();
    upstream.send(json!({
        "id": sub_id,
        "method": "mining.subscribe",
        "params": ["csd-asic-proxy/1.0"]
    })).unwrap();

    // Authorize (dummy credentials — CSD node accepts any)
    let auth_id = upstream.next_id();
    upstream.send(json!({
        "id": auth_id,
        "method": "mining.authorize",
        "params": ["asic-proxy", "x"]
    })).unwrap();

    let upstream_writer_clone = upstream_writer.clone();
    let current_job_up = current_job.clone();
    let recent_jobs_up = recent_jobs.clone();

    // ── Upstream reader thread ────────────────────────────────────────────────
    // Reads jobs from CSD node, converts them, and broadcasts to ASIC clients.

    // We keep a list of connected ASIC client writers to broadcast jobs to.
    let asic_clients: Arc<Mutex<Vec<Arc<Mutex<TcpStream>>>>> =
        Arc::new(Mutex::new(Vec::new()));
    let asic_clients_up = asic_clients.clone();

    let upstream_reader = upstream_stream;
    thread::spawn(move || {
        let reader = BufReader::new(upstream_reader);
        let mut en1_hex = String::new();
        let mut en2_size = 4usize;

        for line in reader.lines() {
            let line = match line {
                Ok(l) => l,
                Err(_) => break,
            };
            if line.trim().is_empty() {
                continue;
            }

            let msg: Value = match serde_json::from_str(&line) {
                Ok(v) => v,
                Err(_) => continue,
            };

            let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");

            match method {
                "mining.notify" => {
                    let p = match msg.get("params").and_then(|v| v.as_array()) {
                        Some(p) => p.clone(),
                        None => continue,
                    };

                    if p.len() < 9 {
                        continue;
                    }

                    let csd_job_id    = p[0].as_str().unwrap_or("").to_string();
                    let prev_hash_hex = p[1].as_str().unwrap_or("").to_string();
                    let coinbase1_hex = p[2].as_str().unwrap_or("").to_string();
                    let coinbase2_hex = p[3].as_str().unwrap_or("").to_string();
                    let branch: Vec<String> = p[4].as_array().unwrap_or(&vec![])
                        .iter().filter_map(|v| v.as_str().map(|s| s.to_string())).collect();
                    let version = u32::from_str_radix(p[5].as_str().unwrap_or("1"), 16).unwrap_or(1);
                    let bits    = u32::from_str_radix(p[6].as_str().unwrap_or("0"), 16).unwrap_or(0);
                    let ntime_raw = p[7].as_str().unwrap_or("0");
                    let ntime32 = u32::from_str_radix(ntime_raw, 16).unwrap_or(0);
                    let clean   = p[8].as_bool().unwrap_or(false);

                    // Reconstruct CSD header template
                    // Compute coinbase txid
                    let mut cb = Vec::new();
                    cb.extend_from_slice(&from_hex(&coinbase1_hex));
                    cb.extend_from_slice(&from_hex(&en1_hex));
                    cb.extend_from_slice(&vec![0u8; en2_size]); // en2 = zeros for template
                    cb.extend_from_slice(&from_hex(&coinbase2_hex));
                    let cb_txid = sha256d(&cb);

                    // Walk merkle branch
                    let mut merkle = cb_txid;
                    for sib_hex in &branch {
                        let sib = from_hex(sib_hex);
                        let mut buf = [0u8; 64];
                        buf[..32].copy_from_slice(&merkle);
                        buf[32..].copy_from_slice(&sib);
                        merkle = sha256d(&buf);
                    }

                    let prev = from_hex(&prev_hash_hex);

                    // Build 84-byte CSD header template
                    let mut csd_header = [0u8; 84];
                    csd_header[0..4].copy_from_slice(&version.to_le_bytes());
                    if prev.len() == 32 {
                        csd_header[4..36].copy_from_slice(&prev);
                    }
                    csd_header[36..68].copy_from_slice(&merkle);
                    // time as u64 LE — ntime32 is low 32 bits, high 32 = 0
                    let time64 = ntime32 as u64;
                    csd_header[68..76].copy_from_slice(&time64.to_le_bytes());
                    csd_header[76..80].copy_from_slice(&bits.to_le_bytes());
                    // nonce bytes [80..84] = 0

                    let target = bits_to_target(bits);

                    // Use a short job_id for the ASIC
                    let proxy_job_id = format!("{:08x}", csd_job_id
                        .chars().rev().take(8).collect::<String>()
                        .chars().rev().collect::<String>()
                        .parse::<u64>().unwrap_or(0));

                    let job = Job {
                        job_id:     proxy_job_id.clone(),
                        csd_header,
                        target,
                        bits,
                        csd_job_id: csd_job_id.clone(),
                        en2_hex:    to_hex(&vec![0u8; en2_size]),
                        ntime_hex:  format!("{:08x}", ntime32),
                    };

                    println!("[upstream] new job {} bits={:08x}", csd_job_id, bits);

                    // Broadcast to all ASIC clients
                    let notify = make_asic_notify(&job, clean);
                    let notify_str = serde_json::to_string(&notify).unwrap() + "\n";

                    {
                        let mut clients = asic_clients_up.lock().unwrap();
                        clients.retain(|c| {
                            c.lock().unwrap().write_all(notify_str.as_bytes()).is_ok()
                        });
                    }

                    // Store job
                    *current_job_up.lock().unwrap() = Some(job.clone());
                    recent_jobs_up.lock().unwrap().insert(proxy_job_id, job);
                }

                "mining.set_difficulty" => {
                    // Forward to all ASIC clients
                    let fwd = serde_json::to_string(&msg).unwrap() + "\n";
                    let mut clients = asic_clients_up.lock().unwrap();
                    clients.retain(|c| {
                        c.lock().unwrap().write_all(fwd.as_bytes()).is_ok()
                    });
                }

                "" => {
                    // Response to subscribe — extract en1 and en2_size
                    if let Some(result) = msg.get("result") {
                        if let Some(arr) = result.as_array() {
                            if arr.len() >= 3 {
                                en1_hex  = arr[1].as_str().unwrap_or("").to_string();
                                en2_size = arr[2].as_u64().unwrap_or(4) as usize;
                                println!("[upstream] subscribed en1={} en2_size={}", en1_hex, en2_size);
                            }
                        }
                    }
                }

                _ => {}
            }
        }

        eprintln!("[upstream] disconnected");
    });

    // ── Listen for ASIC connections ───────────────────────────────────────────

    let listener = TcpListener::bind(&listen_addr).expect("Failed to bind proxy listener");
    println!("[proxy] listening for ASICs on {}", listen_addr);

    for stream in listener.incoming() {
        let stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };

        let peer = stream.peer_addr().map(|a| a.to_string()).unwrap_or_default();
        println!("[proxy] ASIC connected: {}", peer);

        let writer = Arc::new(Mutex::new(stream.try_clone().unwrap()));
        let writer_clone = writer.clone();

        // Register this client for job broadcasts
        asic_clients.lock().unwrap().push(writer.clone());

        let current_job_c  = current_job.clone();
        let recent_jobs_c  = recent_jobs.clone();
        let upstream_writer_c = upstream_writer_clone.clone();

        thread::spawn(move || {
            let reader = BufReader::new(stream);
            let mut msg_id = 1u64;

            let send = |w: &Arc<Mutex<TcpStream>>, v: Value| {
                let mut line = serde_json::to_string(&v).unwrap();
                line.push('\n');
                let _ = w.lock().unwrap().write_all(line.as_bytes());
            };

            for line in reader.lines() {
                let line = match line {
                    Ok(l) => l,
                    Err(_) => break,
                };
                if line.trim().is_empty() {
                    continue;
                }

                let msg: Value = match serde_json::from_str(&line) {
                    Ok(v) => v,
                    Err(_) => continue,
                };

                let id     = msg.get("id").cloned().unwrap_or(Value::Null);
                let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");

                match method {
                    "mining.subscribe" => {
                        send(&writer_clone, json!({
                            "id": id,
                            "result": [[
                                ["mining.set_difficulty", "sub_diff"],
                                ["mining.notify", "sub_notify"]
                            ], "00000000", 4],
                            "error": null
                        }));

                        // Send current job immediately
                        if let Some(job) = current_job_c.lock().unwrap().as_ref() {
                            send(&writer_clone, json!({
                                "id": null,
                                "method": "mining.set_difficulty",
                                "params": [1.0]
                            }));
                            send(&writer_clone, make_asic_notify(job, true));
                        }
                    }

                    "mining.authorize" => {
                        send(&writer_clone, json!({
                            "id": id,
                            "result": true,
                            "error": null
                        }));
                    }

                    "mining.submit" => {
                        let params = msg.get("params")
                            .and_then(|v| v.as_array())
                            .cloned()
                            .unwrap_or_default();

                        if params.len() < 5 {
                            send(&writer_clone, json!({"id":id,"result":false,"error":[20,"bad params",null]}));
                            continue;
                        }

                        let proxy_job_id = params[1].as_str().unwrap_or("").to_string();
                        let nonce_hex    = params[4].as_str().unwrap_or("00000000").to_string();

                        // Look up job
                        let job = {
                            let jobs = recent_jobs_c.lock().unwrap();
                            jobs.get(&proxy_job_id).cloned()
                        };

                        let job = match job {
                            Some(j) => j,
                            None => {
                                println!("[proxy] stale job {}", proxy_job_id);
                                send(&writer_clone, json!({"id":id,"result":false,"error":[21,"stale",null]}));
                                continue;
                            }
                        };

                        // Parse nonce — ASIC sends as big-endian hex
                        let nonce_bytes = from_hex(&nonce_hex);
                        let nonce_be = if nonce_bytes.len() == 4 {
                            u32::from_be_bytes([nonce_bytes[0], nonce_bytes[1], nonce_bytes[2], nonce_bytes[3]])
                        } else {
                            0
                        };

                        // Reconstruct full 84-byte CSD header
                        let csd_hdr = reconstruct_csd_header(&job.csd_header, nonce_be);

                        // Compute SHA-256d of 84-byte header
                        let hash = sha256d(&csd_hdr);

                        if hash_meets_target(&hash, &job.target) {
                            println!("[BLOCK] nonce={} hash={}", nonce_hex, to_hex(&hash));

                            // Submit to CSD upstream
                            let nonce_le_hex = to_hex_u32le(nonce_be);
                            let submit = json!({
                                "id": msg_id,
                                "method": "mining.submit",
                                "params": [
                                    "asic-proxy",
                                    job.csd_job_id,
                                    job.en2_hex,
                                    job.ntime_hex,
                                    nonce_le_hex
                                ]
                            });
                            msg_id += 1;

                            let mut line = serde_json::to_string(&submit).unwrap();
                            line.push('\n');
                            let _ = upstream_writer_c.lock().unwrap().write_all(line.as_bytes());

                            send(&writer_clone, json!({"id":id,"result":true,"error":null}));
                        } else {
                            // Nonce didn't pass CSD check — silently accept from ASIC's perspective
                            // (don't penalise the ASIC, just discard)
                            send(&writer_clone, json!({"id":id,"result":true,"error":null}));
                        }
                    }

                    "mining.extranonce.subscribe" => {
                        send(&writer_clone, json!({"id":id,"result":true,"error":null}));
                    }

                    _ => {
                        send(&writer_clone, json!({"id":id,"result":null,"error":[20,"unknown",null]}));
                    }
                }
            }

            println!("[proxy] ASIC disconnected: {}", peer);
        });
    }
}
