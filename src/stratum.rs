// src/net/stratum.rs
use anyhow::{anyhow, Result};
use serde_json::{json, Value};
use std::{
    collections::VecDeque,
    net::SocketAddr,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};
use tokio::{
    io::{AsyncBufReadExt, AsyncWriteExt, BufReader},
    net::{TcpListener, TcpStream},
    sync::{broadcast, Mutex},
    time::interval,
};

use crate::{
    chain::{
        index::{get_hidx, header_hash, index_header},
        lock::ChainLock,
        pow::{expected_bits, PowTarget},
        reorg::maybe_reorg_to,
        time::now_secs,
    },
    crypto::txid,
    net::mempool::Mempool,
    params::{block_reward, MAX_BLOCK_BYTES},
    state::db::{get_tip, k_block, Stores},
    types::{Block, BlockHeader, Hash20, Hash32, Transaction},
};

use crate::chain::mine::{coinbase, merkle_root_txids};

const JOB_REFRESH_SECS: u64 = 30;
const EXTRANONCE1_BYTES: usize = 4;
const EXTRANONCE2_BYTES: usize = 4;
const VARDIFF_RETARGET_SECS: u64 = 60;
const TARGET_SHARES_PER_MIN: f64 = 30.0;
const VARDIFF_MIN_DIFF: f64 = 792_000.0;
const VARDIFF_MAX_DIFF: f64 = 1_000_000_000.0;
const VARDIFF_CHANGE_THRESHOLD: f64 = 0.25;
const INITIAL_DIFFICULTY: f64 = 792_000.0;
const RECENT_JOBS_WINDOW: usize = 8;

fn diff_to_target(diff: f64) -> [u8; 32] {
    const MANTISSA: u64 = 0x00ffff;
    const EXPONENT_BYTES: u32 = 26;

    let mut be = [0u8; 32];
    let scaled = (MANTISSA as f64) / diff;
    let scaled_u64 = scaled as u64;
    let bytes = scaled_u64.to_be_bytes();

    let dest_end = 32usize.saturating_sub(EXPONENT_BYTES as usize);
    let dest_start = dest_end.saturating_sub(8);
    let copy_len = (dest_end - dest_start).min(8);
    if copy_len > 0 {
        be[dest_start..dest_start + copy_len]
            .copy_from_slice(&bytes[8 - copy_len..]);
    }
    be.reverse();
    be
}

fn hash_meets_diff(hash: &[u8; 32], diff: f64) -> bool {
    let target = diff_to_target(diff);
    for i in (0..32).rev() {
        if hash[i] < target[i] { return true; }
        if hash[i] > target[i] { return false; }
    }
    true
}

#[derive(Clone, Debug)]
struct Job {
    job_id:        String,
    prev_hash:     Hash32,
    coinbase1:     Vec<u8>,
    coinbase2:     Vec<u8>,
    merkle_branch: Vec<Hash32>,
    version:       u32,
    bits:          u32,
    time:          u32,
    height:        u64,
    rest_txs:      Vec<Transaction>,
    created_at:    Instant,
}

impl Job {
    fn coinbase_merkle_path(txids: &[[u8; 32]]) -> Vec<[u8; 32]> {
        if txids.len() <= 1 { return vec![]; }
        let mut path  = Vec::new();
        let mut layer = txids.to_vec();
        let mut idx   = 0usize;
        while layer.len() > 1 {
            let sibling = if idx % 2 == 0 {
                if idx + 1 < layer.len() { layer[idx + 1] } else { layer[idx] }
            } else { layer[idx - 1] };
            path.push(sibling);
            let mut next = Vec::with_capacity((layer.len() + 1) / 2);
            let mut i = 0;
            while i < layer.len() {
                let l = layer[i];
                let r = if i + 1 < layer.len() { layer[i + 1] } else { layer[i] };
                let mut buf = [0u8; 64];
                buf[..32].copy_from_slice(&l);
                buf[32..].copy_from_slice(&r);
                next.push(crate::crypto::sha256d(&buf));
                i += 2;
            }
            idx   /= 2;
            layer  = next;
        }
        path
    }

    fn to_notify(&self, clean_jobs: bool) -> Value {
        let prev_hash_hex  = stratum_prev_hash(&self.prev_hash);
        let coinbase1_hex  = hex::encode(&self.coinbase1);
        let coinbase2_hex  = hex::encode(&self.coinbase2);
        let branch_hex: Vec<String> = self.merkle_branch.iter().map(hex::encode).collect();
        json!({
            "id": null,
            "method": "mining.notify",
            "params": [
                self.job_id, prev_hash_hex, coinbase1_hex, coinbase2_hex,
                branch_hex,
                format!("{:08x}", self.version),
                format!("{:08x}", self.bits),
                format!("{:08x}", self.time),
                clean_jobs,
            ]
        })
    }
}

fn build_job(
    db: &Stores, mempool: &Mempool, miner_h160: Hash20,
    max_mempool_txs: usize, job_counter: &AtomicU64,
) -> Result<Job> {
    use crate::chain::mine::build_template_with_byte_cap;

    let parent_tip: Hash32 = get_tip(db)?.unwrap_or([0u8; 32]);
    let parent_hi = if parent_tip != [0u8; 32] { get_hidx(db, &parent_tip)? } else { None };

    let height = parent_hi.as_ref().map(|h| h.height + 1).unwrap_or(0);
    let bits   = expected_bits(db, height, parent_hi.as_ref())?;
    let reward = block_reward(height);

    let byte_cap = MAX_BLOCK_BYTES.saturating_sub(16 * 1024);
    let (mut txs, _ids, _fees) =
        build_template_with_byte_cap(db, mempool, miner_h160, height, max_mempool_txs, byte_cap)?;

    let placeholder_memo = vec![0u8; EXTRANONCE1_BYTES + EXTRANONCE2_BYTES];
    let cb_placeholder = coinbase(miner_h160, reward, height, Some(&placeholder_memo));
    let c = crate::codec::consensus_bincode();
    let cb_bytes = c.serialize(&cb_placeholder)?;

    let height_le = height.to_le_bytes();
    let split = find_extranonce_offset(&cb_bytes, &height_le)?;

    let coinbase1 = cb_bytes[..split].to_vec();
    let coinbase2 = cb_bytes[split + EXTRANONCE1_BYTES + EXTRANONCE2_BYTES..].to_vec();

    let rest_txs: Vec<Transaction> = txs.drain(1..).collect();
    let mut all_txids: Vec<Hash32> = vec![[0u8; 32]];
    all_txids.extend(rest_txs.iter().map(|tx| txid(tx)));
    let merkle_branch = Job::coinbase_merkle_path(&all_txids);

    let time = {
        let mtp = crate::chain::time::median_time_past(db, &parent_tip).unwrap_or(0);
        let min_t = parent_hi
            .as_ref()
            .map(|h| h.time + crate::params::MIN_BLOCK_SPACING_SECS)
            .unwrap_or(0)
            .max(mtp.saturating_add(1));
        now_secs().max(min_t) as u32
    };

    let job_id = format!("{:016x}", job_counter.fetch_add(1, Ordering::Relaxed));

    Ok(Job {
        job_id, prev_hash: parent_tip, coinbase1, coinbase2,
        merkle_branch, version: 1, bits, time, height, rest_txs,
        created_at: Instant::now(),
    })
}

fn find_extranonce_offset(cb_bytes: &[u8], height_le: &[u8; 8]) -> Result<usize> {
    for i in 0..cb_bytes.len().saturating_sub(9) {
        if &cb_bytes[i..i + 8] == height_le && cb_bytes[i + 8] == 0x00 {
            return Ok(i + 9);
        }
    }
    Err(anyhow!("stratum: could not locate extranonce split in serialised coinbase"))
}

// ── Shared server state ───────────────────────────────────────────────────────

struct StratumState {
    current_job:      Option<Job>,
    recent_jobs:      VecDeque<Job>,   // keeps last RECENT_JOBS_WINDOW jobs
    next_extranonce1: u32,
}

impl StratumState {
    fn push_job(&mut self, job: Job) {
        self.current_job = Some(job.clone());
        self.recent_jobs.push_back(job);
        if self.recent_jobs.len() > RECENT_JOBS_WINDOW {
            self.recent_jobs.pop_front();
        }
    }

    fn find_job(&self, job_id: &str) -> Option<Job> {
        self.recent_jobs.iter().find(|j| j.job_id == job_id).cloned()
    }
}

pub struct StratumConfig {
    pub listen:          SocketAddr,
    pub miner_h160:      Hash20,
    pub max_mempool_txs: usize,
}

pub async fn run_stratum(
    db: Arc<Stores>, mempool: Arc<Mempool>,
    chain_lock: ChainLock, cfg: StratumConfig,
) -> Result<()> {
    let listener = TcpListener::bind(cfg.listen).await?;
    println!("[stratum] listening on {}", cfg.listen);

    let state = Arc::new(Mutex::new(StratumState {
        current_job:      None,
        recent_jobs:      VecDeque::new(),
        next_extranonce1: 0,
    }));
    let job_counter = Arc::new(AtomicU64::new(0));
    let (job_tx, _) = broadcast::channel::<Job>(8);
    let job_tx      = Arc::new(job_tx);

    // ── dispatcher ───────────────────────────────────────────────────────────
    {
        let db = db.clone(); let mempool = mempool.clone();
        let state = state.clone(); let job_tx = job_tx.clone();
        let job_counter = job_counter.clone();
        let miner_h160 = cfg.miner_h160;
        let max_mempool = cfg.max_mempool_txs;

        tokio::spawn(async move {
            let mut last_tip: Hash32 = [0u8; 32];
            let mut last_job_at = Instant::now();
            let mut tick = interval(Duration::from_millis(500));
            loop {
                tick.tick().await;
                let tip = get_tip(&db).ok().flatten().unwrap_or([0u8; 32]);
                let tip_changed = tip != last_tip;
                let stale = last_job_at.elapsed().as_secs() >= JOB_REFRESH_SECS;
                if !tip_changed && !stale { continue; }
                match build_job(&db, &mempool, miner_h160, max_mempool, &job_counter) {
                    Ok(job) => {
                        println!("[stratum] new job {} height={} bits={:08x} clean={}",
                            job.job_id, job.height, job.bits, tip_changed);
                        last_tip    = tip;
                        last_job_at = Instant::now();
                        state.lock().await.push_job(job.clone());
                        let _ = job_tx.send(job);
                    }
                    Err(e) => eprintln!("[stratum] build_job failed: {e}"),
                }
            }
        });
    }

    // ── accept loop ──────────────────────────────────────────────────────────
    loop {
        let (stream, addr) = listener.accept().await?;
        println!("[stratum] worker connected: {addr}");
        let db = db.clone(); let mempool = mempool.clone();
        let chain_lock = chain_lock.clone(); let state = state.clone();
        let job_rx = job_tx.subscribe();
        let job_counter = job_counter.clone();
        let miner_h160 = cfg.miner_h160;
        tokio::spawn(async move {
            if let Err(e) = handle_worker(
                stream, addr, db, mempool, chain_lock,
                state, job_rx, job_counter, miner_h160,
            ).await {
                println!("[stratum] worker {addr} disconnected: {e}");
            }
        });
    }
}

// ── Vardiff ───────────────────────────────────────────────────────────────────

struct Vardiff {
    difficulty:            f64,
    shares_since_retarget: u64,
    last_retarget:         Instant,
}

impl Vardiff {
    fn new(initial: f64) -> Self {
        Self { difficulty: initial, shares_since_retarget: 0, last_retarget: Instant::now() }
    }

    fn on_share(&mut self) -> Option<f64> {
        self.shares_since_retarget += 1;
        let elapsed = self.last_retarget.elapsed().as_secs_f64();
        if elapsed < VARDIFF_RETARGET_SECS as f64 { return None; }
        let actual_rate = self.shares_since_retarget as f64 / (elapsed / 60.0);
        let ideal_diff  = self.difficulty * (actual_rate / TARGET_SHARES_PER_MIN);
        let new_diff    = ideal_diff.clamp(VARDIFF_MIN_DIFF, VARDIFF_MAX_DIFF);
        self.shares_since_retarget = 0;
        self.last_retarget = Instant::now();
        let change = (new_diff - self.difficulty).abs() / self.difficulty;
        if change > VARDIFF_CHANGE_THRESHOLD {
            self.difficulty = new_diff;
            Some(new_diff)
        } else { None }
    }

    fn current(&self) -> f64 { self.difficulty }
}

// ── Per-worker handler ────────────────────────────────────────────────────────

struct WorkerState {
    addr:        SocketAddr,
    extranonce1: [u8; EXTRANONCE1_BYTES],
    authorized:  bool,
    subscribed:  bool,
    vardiff:     Vardiff,
}

async fn handle_worker(
    stream: TcpStream, addr: SocketAddr,
    db: Arc<Stores>, mempool: Arc<Mempool>, chain_lock: ChainLock,
    shared: Arc<Mutex<StratumState>>, mut job_rx: broadcast::Receiver<Job>,
    job_counter: Arc<AtomicU64>, miner_h160: Hash20,
) -> Result<()> {
    let (reader, writer) = stream.into_split();
    let writer = Arc::new(Mutex::new(writer));
    let mut lines = BufReader::new(reader).lines();

    let extranonce1: [u8; 4] = {
        let mut g = shared.lock().await;
        let n = g.next_extranonce1;
        g.next_extranonce1 = n.wrapping_add(1);
        n.to_le_bytes()
    };

    let mut worker = WorkerState {
        addr, extranonce1, authorized: false, subscribed: false,
        vardiff: Vardiff::new(INITIAL_DIFFICULTY),
    };

    let send = {
        let writer = writer.clone();
        move |v: Value| {
            let writer = writer.clone();
            async move {
                let mut line = serde_json::to_string(&v)?;
                line.push('\n');
                writer.lock().await.write_all(line.as_bytes()).await?;
                Ok::<(), anyhow::Error>(())
            }
        }
    };

    loop {
        tokio::select! {
            line = lines.next_line() => {
                let line = match line? { Some(l) => l, None => break };
                if line.trim().is_empty() { continue; }

                let msg: Value = match serde_json::from_str(&line) {
                    Ok(v)  => v,
                    Err(_) => { eprintln!("[stratum] {addr} bad JSON: {line}"); continue; }
                };

                let id     = msg.get("id").cloned().unwrap_or(Value::Null);
                let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("").to_string();

                println!("[stratum] {addr} method={method}");

                match method.as_str() {

                    "mining.subscribe" => {
                        worker.subscribed = true;
                        let en1_hex = hex::encode(worker.extranonce1);
                        send(json!({
                            "id": id,
                            "result": [[
                                ["mining.set_difficulty", "sub_diff"],
                                ["mining.notify", "sub_notify"]
                            ], en1_hex, EXTRANONCE2_BYTES],
                            "error": null
                        })).await?;
                        send(json!({
                            "id": null, "method": "mining.set_difficulty",
                            "params": [worker.vardiff.current()]
                        })).await?;
                    }

                    "mining.authorize" => {
                        worker.authorized = true;
                        send(json!({"id": id, "result": true, "error": null})).await?;
                        send(json!({
                            "id": null, "method": "mining.set_difficulty",
                            "params": [worker.vardiff.current()]
                        })).await?;
                        if let Some(j) = shared.lock().await.current_job.clone() {
                            send(j.to_notify(true)).await?;
                        }
                    }

                    "mining.submit" => {
                        let job_label = msg.get("params")
                            .and_then(|p| p.get(1)).and_then(|v| v.as_str()).unwrap_or("?");
                        println!("[stratum] {addr} submit job={job_label}");

                        let params = msg.get("params")
                            .and_then(|v| v.as_array()).cloned().unwrap_or_default();
                        if params.len() < 5 {
                            send(json!({"id": id, "result": null,
                                "error": [20, "malformed submit", null]})).await?;
                            continue;
                        }

                        let job_id    = params[1].as_str().unwrap_or("").to_string();
                        let en2_hex   = params[2].as_str().unwrap_or("").to_string();
                        let ntime_hex = params[3].as_str().unwrap_or("").to_string();
                        let nonce_hex = params[4].as_str().unwrap_or("").to_string();

                        let share_result = validate_and_submit(
                            &db, &mempool, &chain_lock, &shared, &worker,
                            &job_id, &en2_hex, &ntime_hex, &nonce_hex,
                            miner_h160, &job_counter,
                        ).await;

                        match share_result {
                            Ok(ShareOutcome::Block) => {
                                println!("[stratum] *** BLOCK FOUND by {addr} job={job_id} ***");
                                send(json!({"id": id, "result": true, "error": null})).await?;
                            }
                            Ok(ShareOutcome::Share) => {
                                println!("[stratum] {addr} share accepted job={job_id}");
                                send(json!({"id": id, "result": true, "error": null})).await?;
                            }
                            Err(e) => {
                                eprintln!("[stratum] {addr} bad share: {e}");
                                send(json!({"id": id, "result": null,
                                    "error": [20, e.to_string(), null]})).await?;
                                continue;
                            }
                        }

                        if let Some(new_diff) = worker.vardiff.on_share() {
                            println!("[stratum] vardiff {addr}: → {new_diff:.0}");
                            send(json!({
                                "id": null, "method": "mining.set_difficulty",
                                "params": [new_diff]
                            })).await?;
                            if let Some(j) = shared.lock().await.current_job.clone() {
                                send(j.to_notify(false)).await?;
                            }
                        }
                    }

                    "mining.get_transactions" => {
                        send(json!({"id": id, "result": [], "error": null})).await?;
                    }

                    "mining.extranonce.subscribe" => {
                        send(json!({"id": id, "result": true, "error": null})).await?;
                    }

                    other => {
                        eprintln!("[stratum] {addr} unknown method: {other}");
                        send(json!({"id": id, "result": null,
                            "error": [20, "unknown method", null]})).await?;
                    }
                }
            }

            job = job_rx.recv() => {
                let job = match job {
                    Ok(j) => j,
                    Err(broadcast::error::RecvError::Lagged(_)) => {
                        match shared.lock().await.current_job.clone() {
                            Some(j) => j, None => continue,
                        }
                    }
                    Err(broadcast::error::RecvError::Closed) => break,
                };
                if worker.subscribed {
                    send(job.to_notify(true)).await?;
                }
            }
        }
    }
    Ok(())
}

// ── Share validation ──────────────────────────────────────────────────────────

enum ShareOutcome { Share, Block }

async fn validate_and_submit(
    db: &Stores, mempool: &Mempool, chain_lock: &ChainLock,
    shared: &Mutex<StratumState>, worker: &WorkerState,
    job_id: &str, en2_hex: &str, ntime_hex: &str, nonce_hex: &str,
    miner_h160: Hash20, job_counter: &AtomicU64,
) -> Result<ShareOutcome> {

    // ── look up job in recent window ──────────────────────────────────────────
    let job = shared.lock().await.find_job(job_id)
        .ok_or_else(|| anyhow!("stale job {job_id}"))?;

    let en2 = hex::decode(en2_hex).map_err(|_| anyhow!("bad extranonce2 hex"))?;
    if en2.len() != EXTRANONCE2_BYTES {
        return Err(anyhow!("extranonce2 must be {} bytes", EXTRANONCE2_BYTES));
    }
    let ntime = u32::from_str_radix(ntime_hex, 16).map_err(|_| anyhow!("bad ntime"))?;
    let nonce = u32::from_str_radix(nonce_hex, 16).map_err(|_| anyhow!("bad nonce"))?;

    // ── reconstruct coinbase ──────────────────────────────────────────────────
    let mut cb_bytes = Vec::with_capacity(
        job.coinbase1.len() + EXTRANONCE1_BYTES + EXTRANONCE2_BYTES + job.coinbase2.len());
    cb_bytes.extend_from_slice(&job.coinbase1);
    cb_bytes.extend_from_slice(&worker.extranonce1);
    cb_bytes.extend_from_slice(&en2);
    cb_bytes.extend_from_slice(&job.coinbase2);

    let cb_tx: Transaction = crate::codec::consensus_bincode()
        .deserialize(&cb_bytes)
        .map_err(|e| anyhow!("coinbase deserialise failed: {e}"))?;

    // ── merkle root ───────────────────────────────────────────────────────────
    let cb_txid = txid(&cb_tx);
    let mut all_txids: Vec<Hash32> = Vec::with_capacity(1 + job.rest_txs.len());
    all_txids.push(cb_txid);
    all_txids.extend(job.rest_txs.iter().map(|tx| txid(tx)));
    let merkle = merkle_root_txids(&all_txids);

    let hdr = BlockHeader {
        version: job.version, prev: job.prev_hash,
        merkle, time: ntime as u64, bits: job.bits, nonce,
    };
    let h = header_hash(&hdr);

    // ── vardiff check ─────────────────────────────────────────────────────────
    if !hash_meets_diff(&h, worker.vardiff.current()) {
        return Err(anyhow!("share below worker difficulty ({:.0})", worker.vardiff.current()));
    }

    // ── network target check ──────────────────────────────────────────────────
    let network_target =
        PowTarget::from_bits(job.bits).ok_or_else(|| anyhow!("invalid bits in job"))?;

    if !network_target.check(&h) {
        return Ok(ShareOutcome::Share);
    }

    // ── it's a block ──────────────────────────────────────────────────────────
    println!("[stratum] BLOCK height={} hash=0x{}", job.height, hex::encode(h));

    let mut txs: Vec<Transaction> = Vec::with_capacity(1 + job.rest_txs.len());
    txs.push(cb_tx);
    txs.extend(job.rest_txs.clone());

    let block       = Block { header: hdr.clone(), txs };
    let block_bytes = crate::codec::consensus_bincode().serialize(&block)?;

    if block_bytes.len() > MAX_BLOCK_BYTES {
        return Err(anyhow!("block exceeds MAX_BLOCK_BYTES"));
    }

    {
        let _g = chain_lock.lock();
        let cur_tip = get_tip(db)?.unwrap_or([0u8; 32]);
        if cur_tip != job.prev_hash {
            return Err(anyhow!("stale block: tip moved"));
        }
        db.blocks.insert(k_block(&h), block_bytes)?;
        let parent_hi = if job.prev_hash == [0u8; 32] { None }
                        else { get_hidx(db, &job.prev_hash)? };
        index_header(db, &hdr, parent_hi.as_ref())?;
        db.db.flush()?;
    }

    maybe_reorg_to(db, &h, Some(mempool))
        .map_err(|e| anyhow!("maybe_reorg_to failed: {e}"))?;

    Ok(ShareOutcome::Block)
}

fn stratum_prev_hash(h: &Hash32) -> String {
    let mut out = [0u8; 32];
    for i in 0..8 {
        let c = &h[i * 4..(i + 1) * 4];
        out[i * 4]     = c[3];
        out[i * 4 + 1] = c[2];
        out[i * 4 + 2] = c[1];
        out[i * 4 + 3] = c[0];
    }
    hex::encode(out)
}
