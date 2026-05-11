use anyhow::{anyhow, Context, Result};
use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine};
use bytes::Bytes;
use cipher::{KeyIvInit, StreamCipher};
use futures::future::join_all;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use rand::seq::SliceRandom;
use reqwest::{Client, Proxy, StatusCode};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{AsyncSeekExt, AsyncWriteExt};
use tokio::sync::{mpsc, Mutex, Notify, Semaphore};
use tokio::task::JoinSet;

// ── Crypto ────────────────────────────────────────────────────────────────────

type Aes128Ctr = ctr::Ctr128BE<aes::Aes128>;
type Aes128Cbc = cbc::Decryptor<aes::Aes128>;

fn fold_key(raw: &[u8; 32]) -> ([u8; 16], [u8; 16]) {
    let mut key = [0u8; 16];
    for i in 0..16 { key[i] = raw[i] ^ raw[i + 16]; }
    let mut iv = [0u8; 16];
    iv[..8].copy_from_slice(&raw[16..24]);
    (key, iv)
}

fn decrypt_attrs(at_b64: &str, aes_key: &[u8; 16]) -> Result<String> {
    use cipher::{block_padding::NoPadding, BlockDecryptMut};
    let data = URL_SAFE_NO_PAD.decode(at_b64.trim()).context("at base64")?;
    let mut buf = data.clone();
    Aes128Cbc::new(aes_key.into(), &[0u8; 16].into())
        .decrypt_padded_mut::<NoPadding>(&mut buf)
        .map_err(|e| anyhow!("cbc decrypt: {e}"))?;
    let s = String::from_utf8_lossy(&buf);
    let s = s.trim_end_matches('\0');
    let json_start = s.find('{').ok_or_else(|| anyhow!("no {{ in attrs"))?;
    let json_end = s.rfind('}').ok_or_else(|| anyhow!("no }} in attrs"))? + 1;
    anyhow::ensure!(json_start < json_end, "malformed attrs (bad decrypt?)");
    Ok(s[json_start..json_end].to_owned())
}

fn aes128_ecb_decrypt_block(block: &mut [u8; 16], key: &[u8; 16]) {
    use aes::cipher::{BlockDecrypt, KeyInit};
    let c = aes::Aes128::new(key.into());
    c.decrypt_block(block.into());
}

fn extract_key_b64(k_field: &str) -> Option<&str> {
    for entry in k_field.split('/') {
        let key = entry.splitn(2, ':').nth(1).unwrap_or("").trim();
        if !key.is_empty() { return Some(key); }
    }
    None
}

fn decrypt_node_key(enc_b64: &str, folder_key: &[u8; 16]) -> Result<[u8; 32]> {
    let enc = URL_SAFE_NO_PAD.decode(enc_b64.trim()).context("node key b64")?;
    anyhow::ensure!(enc.len() == 32, "expected 32-byte node key, got {}", enc.len());
    let mut out = [0u8; 32];
    for (i, block) in enc.chunks(16).enumerate() {
        let mut b = [0u8; 16];
        b.copy_from_slice(block);
        aes128_ecb_decrypt_block(&mut b, folder_key);
        out[i * 16..(i + 1) * 16].copy_from_slice(&b);
    }
    Ok(out)
}

fn decrypt_chunk(data: &mut [u8], key: &[u8; 16], iv: &[u8; 16], byte_offset: u64) {
    let block_idx = byte_offset / 16;
    let skip = (byte_offset % 16) as usize;
    let mut nonce = *iv;
    let ctr_lo = u64::from_be_bytes(nonce[8..16].try_into().unwrap()).wrapping_add(block_idx);
    nonce[8..16].copy_from_slice(&ctr_lo.to_be_bytes());
    let mut cipher = Aes128Ctr::new(key.into(), &nonce.into());
    if skip > 0 { cipher.apply_keystream(&mut vec![0u8; skip]); }
    cipher.apply_keystream(data);
}

// ── MEGA API ──────────────────────────────────────────────────────────────────

#[derive(Serialize)]
struct CsReq<'a> { a: &'a str, g: u8, p: &'a str }

#[allow(dead_code)]
#[derive(Deserialize)]
struct DlResp { g: String, s: u64, at: String }

async fn file_dl_info(client: &Client, file_id: &str) -> Result<(String, u64, String)> {
    let body = serde_json::to_string(&[CsReq { a: "g", g: 1, p: file_id }])?;
    let resp: serde_json::Value = client
        .post("https://g.api.mega.co.nz/cs").query(&[("id", "1")])
        .header("content-type", "application/json").body(body)
        .send().await?.json().await?;
    let obj = resp.as_array().and_then(|a| a.first())
        .ok_or_else(|| anyhow!("bad API shape"))?.clone();
    if let Some(c) = obj.as_i64() { return Err(anyhow!("MEGA error {c}")); }
    let r: DlResp = serde_json::from_value(obj)?;
    Ok((r.g, r.s, r.at))
}

async fn folder_nodes(client: &Client, folder_id: &str) -> Result<Vec<serde_json::Value>> {
    let body = serde_json::json!([{"a":"f","c":1,"ca":1,"r":1}]).to_string();
    let resp: serde_json::Value = client
        .post("https://g.api.mega.co.nz/cs")
        .query(&[("id", "1"), ("n", folder_id)])
        .header("content-type", "application/json").body(body)
        .send().await?.json().await?;
    let obj = resp.as_array().and_then(|a| a.first())
        .ok_or_else(|| anyhow!("bad folder API"))?.clone();
    if let Some(c) = obj.as_i64() { return Err(anyhow!("MEGA folder error {c}")); }
    obj["f"].as_array().cloned().ok_or_else(|| anyhow!("no 'f' in folder response"))
}

async fn refresh_dl_url(client: &Client, file_id: &str) -> Result<String> {
    Ok(file_dl_info(client, file_id).await?.0)
}

async fn folder_file_url(base: &Client, folder_id: &str, node_handle: &str) -> Result<String> {
    let body = serde_json::json!([{"a":"g","g":1,"n":node_handle}]).to_string();
    let resp: serde_json::Value = base.post("https://g.api.mega.co.nz/cs")
        .query(&[("id", "1"), ("n", folder_id)])
        .header("content-type", "application/json").body(body)
        .send().await?.json().await?;
    let obj = resp.as_array().and_then(|a| a.first())
        .ok_or_else(|| anyhow!("bad folder dl resp"))?.clone();
    if let Some(c) = obj.as_i64() { return Err(anyhow!("MEGA folder dl error {c}")); }
    Ok(obj["g"].as_str().ok_or_else(|| anyhow!("no g in folder dl resp"))?.to_owned())
}

// Fetches download URLs for up to BATCH_SIZE files in a single API call.
// Returns None for slots where the API returned an error.
const BATCH_SIZE: usize = 50;

async fn prefetch_folder_urls(
    base: &Client,
    folder_id: &str,
    handles: &[String],
) -> Vec<Option<String>> {
    let mut results = vec![None; handles.len()];
    // Cap batch parallelism at 4 to avoid MEGA API rate limits
    let sem = Arc::new(Semaphore::new(4));
    let futs: Vec<_> = handles.chunks(BATCH_SIZE).enumerate().map(|(bi, batch)| {
        let base = base.clone();
        let folder_id = folder_id.to_owned();
        let batch: Vec<String> = batch.to_vec();
        let sem = sem.clone();
        let start = bi * BATCH_SIZE;
        async move {
            let _g = sem.acquire().await.ok()?;
            let reqs: Vec<_> = batch.iter()
                .map(|h| serde_json::json!({"a":"g","g":1,"n":h}))
                .collect();
            let body = serde_json::to_string(&reqs).ok()?;
            let resp: serde_json::Value = base
                .post("https://g.api.mega.co.nz/cs")
                .query(&[("id", "1"), ("n", folder_id.as_str())])
                .header("content-type", "application/json")
                .body(body)
                .send().await.ok()?.json().await.ok()?;
            let arr = resp.as_array()?.clone();
            let urls: Vec<Option<String>> = arr.iter()
                .map(|v| v["g"].as_str().map(str::to_owned))
                .collect();
            Some((start, urls))
        }
    }).collect();

    for result in join_all(futs).await {
        if let Some((start, urls)) = result {
            for (i, url) in urls.into_iter().enumerate() {
                if start + i < results.len() { results[start + i] = url; }
            }
        }
    }
    results
}

// ── Link parsing ──────────────────────────────────────────────────────────────

enum MegaLink {
    File { id: String, raw_key: [u8; 32] },
    Folder { id: String, folder_key: [u8; 16] },
}

fn parse_link(url: &str) -> Result<MegaLink> {
    let (path, hash) = url.trim().split_once('#')
        .ok_or_else(|| anyhow!("no # in link"))?;
    if path.contains("/file/") {
        let id = path.split("/file/").nth(1)
            .ok_or_else(|| anyhow!("no file id"))?.trim_end_matches('/').to_owned();
        let raw = URL_SAFE_NO_PAD.decode(hash).context("file key b64")?;
        anyhow::ensure!(raw.len() == 32, "file key must be 32 bytes");
        let mut arr = [0u8; 32];
        arr.copy_from_slice(&raw);
        Ok(MegaLink::File { id, raw_key: arr })
    } else if path.contains("/folder/") {
        let id = path.split("/folder/").nth(1)
            .ok_or_else(|| anyhow!("no folder id"))?.trim_end_matches('/').to_owned();
        let raw = URL_SAFE_NO_PAD.decode(hash).context("folder key b64")?;
        anyhow::ensure!(raw.len() == 16, "folder key must be 16 bytes, got {}", raw.len());
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&raw);
        Ok(MegaLink::Folder { id, folder_key: arr })
    } else {
        Err(anyhow!("unrecognised link (expected /file/ or /folder/)"))
    }
}

// ── Folder tree ───────────────────────────────────────────────────────────────

struct FileEntry {
    handle: String,
    path: PathBuf,
    size: u64,
    aes_key: [u8; 16],
    iv: [u8; 16],
}

fn build_file_list(nodes: &[serde_json::Value], folder_key: &[u8; 16]) -> Result<Vec<FileEntry>> {
    let mut info: HashMap<String, (String, String, u64)> = HashMap::new();

    for node in nodes {
        let h = node["h"].as_str().unwrap_or("").to_owned();
        let p = node["p"].as_str().unwrap_or("").to_owned();
        let t = node["t"].as_u64().unwrap_or(0);
        let name = if let Some(at) = node["a"].as_str() {
            let key_str = node["k"].as_str().unwrap_or("");
            let enc_part = extract_key_b64(key_str).unwrap_or("");
            let dec_key: [u8; 16] = if enc_part.is_empty() {
                *folder_key
            } else if t == 1 || t == 2 {
                let enc = URL_SAFE_NO_PAD.decode(enc_part.trim()).unwrap_or_default();
                if enc.len() == 16 {
                    let mut b = [0u8; 16];
                    b.copy_from_slice(&enc);
                    aes128_ecb_decrypt_block(&mut b, folder_key);
                    b
                } else { *folder_key }
            } else {
                match decrypt_node_key(enc_part, folder_key) {
                    Ok(r) => fold_key(&r).0,
                    Err(_) => *folder_key,
                }
            };
            decrypt_attrs(at, &dec_key)
                .ok()
                .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
                .and_then(|v| v["n"].as_str().map(|s| s.to_owned()))
                .unwrap_or_else(|| h.clone())
        } else { h.clone() };
        info.insert(h, (p, name, t));
    }

    fn full_path(h: &str, info: &HashMap<String, (String, String, u64)>, root: &str) -> PathBuf {
        let (parent, name, _) = match info.get(h) {
            Some(v) => v,
            None => return PathBuf::from(h),
        };
        if parent.is_empty() || h == root { return PathBuf::from(name); }
        full_path(parent, info, root).join(name)
    }

    let root_handle = nodes.iter()
        .find(|n| n["t"].as_u64() == Some(2))
        .and_then(|n| n["h"].as_str())
        .unwrap_or("").to_owned();

    let mut files = Vec::new();
    for node in nodes {
        if node["t"].as_u64() != Some(0) { continue; }
        let h = node["h"].as_str().unwrap_or("").to_owned();
        let size = node["s"].as_u64().unwrap_or(0);
        let key_str = node["k"].as_str().unwrap_or("");
        let enc_part = match extract_key_b64(key_str) {
            Some(e) => e,
            None => { eprintln!("[warn] skip {h}: no key"); continue; }
        };
        let raw32 = match decrypt_node_key(enc_part, folder_key) {
            Ok(r) => r,
            Err(e) => { eprintln!("[warn] skip {h}: {e}"); continue; }
        };
        let (aes_key, iv) = fold_key(&raw32);
        let rel_path = {
            let p = full_path(&h, &info, &root_handle);
            let comps: Vec<_> = p.components().collect();
            if comps.len() > 1 { comps[1..].iter().collect() } else { p }
        };
        files.push(FileEntry { handle: h, path: rel_path, size, aes_key, iv });
    }
    Ok(files)
}

// ── Proxy pool ────────────────────────────────────────────────────────────────

const POOL_URLS: &[&str] = &[
    "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/socks5.txt",
    "https://raw.githubusercontent.com/proxifly/free-proxy-list/main/proxies/protocols/socks5/data.txt",
    "https://raw.githubusercontent.com/iplocate/free-proxy-list/main/protocols/https.txt",
];

const PROBE_CONC: usize = 50;
const PROBE_TIMEOUT: u64 = 6;
const SINGLE_MAX_GOOD: usize = 48;
const FOLDER_MAX_GOOD: usize = 200;
const MIN_PROXIES_TO_START: usize = 3;

type SharedPool = Arc<Mutex<VecDeque<String>>>;

async fn fetch_raw_proxies(c: &Client) -> Vec<String> {
    let futs = POOL_URLS.iter().map(|url| {
        let c = c.clone();
        async move {
            c.get(*url).timeout(Duration::from_secs(15))
                .send().await.ok()?.text().await.ok()
        }
    });
    join_all(futs).await.into_iter().flatten()
        .flat_map(|body| {
            body.lines()
                .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
                .map(|l| {
                    let l = l.trim();
                    if l.starts_with("socks5://") || l.starts_with("http://") || l.starts_with("https://") {
                        l.to_owned()
                    } else { format!("socks5://{l}") }
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

async fn probe(proxy_url: String, test_url: String) -> Option<String> {
    let client = Client::builder()
        .proxy(Proxy::all(&proxy_url).ok()?)
        .timeout(Duration::from_secs(PROBE_TIMEOUT))
        .build().ok()?;
    let st = client.head(&test_url).send().await.ok()?.status();
    if st.as_u16() > 0 { Some(proxy_url) } else { None }
}

async fn probe_into_pool(
    candidates: Vec<String>,
    test_url: String,
    max_good: usize,
    pool: SharedPool,
    ready: Arc<Notify>,
    min_ready: usize,
) {
    let sem = Arc::new(Semaphore::new(PROBE_CONC));
    let pb = ProgressBar::new(candidates.len() as u64);
    pb.set_style(ProgressStyle::default_bar()
        .template("[proxy] {bar:40} {pos}/{len} good={msg}").unwrap());
    let notified = Arc::new(AtomicBool::new(false));
    let total_good = Arc::new(AtomicUsize::new(0));

    let handles: Vec<_> = candidates.into_iter().map(|p| {
        let (sem, pool, ready, notified, test, pb, tg) = (
            sem.clone(), pool.clone(), ready.clone(), notified.clone(),
            test_url.clone(), pb.clone(), total_good.clone(),
        );
        tokio::spawn(async move {
            let _g = sem.acquire().await.unwrap();
            if pool.lock().await.len() >= max_good { pb.inc(1); return; }
            if let Some(ok) = probe(p, test).await {
                let mut g = pool.lock().await;
                if g.len() < max_good {
                    g.push_back(ok);
                    drop(g);
                    let n = tg.fetch_add(1, Ordering::Relaxed) + 1;
                    pb.set_message(n.to_string());
                    if n >= min_ready && !notified.swap(true, Ordering::Relaxed) {
                        ready.notify_one();
                    }
                }
            }
            pb.inc(1);
        })
    }).collect();

    join_all(handles).await;
    ready.notify_one();
    pb.finish_and_clear();
    eprintln!("[proxy] {} working proxies", pool.lock().await.len());
}

fn spawn_proxy_probing(
    base: Client,
    test_url: String,
    max_good: usize,
    pool: SharedPool,
    refill_lock: Arc<Mutex<()>>,
    ready: Arc<Notify>,
    min_ready: usize,
) -> tokio::task::JoinHandle<()> {
    tokio::spawn(async move {
        let _guard = refill_lock.lock().await;
        eprintln!("[proxy] fetching lists…");
        let mut raw = fetch_raw_proxies(&base).await;
        raw.shuffle(&mut rand::thread_rng());
        raw.dedup();
        eprintln!("[proxy] {} candidates", raw.len());
        probe_into_pool(raw, test_url, max_good, pool, ready, min_ready).await;
    })
}

async fn build_proxy_pool(base: &Client, test_url: &str, max_good: usize) -> Vec<String> {
    eprintln!("[proxy] fetching lists…");
    let mut raw = fetch_raw_proxies(base).await;
    raw.shuffle(&mut rand::thread_rng());
    raw.dedup();
    eprintln!("[proxy] {} candidates", raw.len());
    let pool: SharedPool = Arc::new(Mutex::new(VecDeque::new()));
    let ready = Arc::new(Notify::new());
    probe_into_pool(raw, test_url.to_owned(), max_good, pool.clone(), ready, max_good).await;
    Arc::try_unwrap(pool).unwrap().into_inner().into_iter().collect()
}

// ── Per-proxy worker (single-file) ────────────────────────────────────────────

struct Chunk { idx: usize, start: u64, end: u64 }
type ChunkResult = (usize, u64, Bytes);

fn make_client(proxy: Option<&str>, timeout_secs: u64) -> Result<Client> {
    let mut b = Client::builder().timeout(Duration::from_secs(timeout_secs));
    if let Some(p) = proxy { b = b.proxy(Proxy::all(p)?); }
    Ok(b.build()?)
}

async fn download_range(client: &Client, url: &str, start: u64, end: u64) -> Result<Bytes> {
    Ok(client.get(url)
        .header("Range", format!("bytes={start}-{end}"))
        .send().await?.error_for_status()?.bytes().await?)
}

fn is_quota_error(e: &anyhow::Error) -> bool {
    e.downcast_ref::<reqwest::Error>()
        .and_then(|re| re.status())
        .map(|st| st == StatusCode::TOO_MANY_REQUESTS || st.as_u16() == 509)
        .unwrap_or(false)
}

const MAX_CONSEC_FAIL: usize = 3;

async fn proxy_worker(
    proxy: Option<String>,
    url: Arc<String>,
    work_rx: Arc<Mutex<mpsc::Receiver<Chunk>>>,
    retry_tx: mpsc::Sender<Chunk>,
    result_tx: mpsc::Sender<ChunkResult>,
    pb: Arc<ProgressBar>,
    timeout_secs: u64,
) -> Option<String> {
    let client = match make_client(proxy.as_deref(), timeout_secs) {
        Ok(c) => c,
        Err(e) => { eprintln!("[worker] client build: {e}"); return None; }
    };
    let tag = proxy.as_deref().unwrap_or("direct");
    let mut consec = 0usize;
    loop {
        let chunk = {
            let mut rx = work_rx.lock().await;
            match rx.try_recv() { Ok(c) => c, Err(_) => break }
        };
        match download_range(&client, &url, chunk.start, chunk.end).await {
            Ok(data) => {
                consec = 0;
                pb.inc(data.len() as u64);
                let _ = result_tx.send((chunk.idx, chunk.start, data)).await;
            }
            Err(e) => {
                let _ = retry_tx.send(chunk).await;
                if is_quota_error(&e) {
                    eprintln!("\n[{tag}] quota/rate → retiring");
                    return None;
                }
                consec += 1;
                if consec >= MAX_CONSEC_FAIL {
                    eprintln!("\n[{tag}] {consec} consecutive errors → retiring");
                    return None;
                }
            }
        }
    }
    proxy
}

// ── Resume state ──────────────────────────────────────────────────────────────

fn state_path(part_path: &Path) -> PathBuf {
    let mut p = part_path.to_path_buf();
    let name = p.file_name().unwrap_or_default().to_string_lossy().to_string();
    p.set_file_name(format!("{name}.meta"));
    p
}

fn load_state(state: &Path) -> HashSet<usize> {
    std::fs::read_to_string(state).ok()
        .and_then(|s| serde_json::from_str::<Vec<usize>>(&s).ok())
        .map(|v| v.into_iter().collect())
        .unwrap_or_default()
}

fn save_state(state: &Path, done: &HashSet<usize>) {
    let v: Vec<usize> = done.iter().copied().collect();
    if let Ok(json) = serde_json::to_string(&v) {
        let _ = std::fs::write(state, json);
    }
}

// ── Single-file download ──────────────────────────────────────────────────────

const CHUNK_SIZE: u64 = 4 * 1024 * 1024;
const MAX_ROUNDS: usize = 30;

async fn download_file(
    base: &Client,
    file_id: &str,
    aes_key: [u8; 16],
    iv: [u8; 16],
    file_name: &str,
    file_size: u64,
    out_dir: &Path,
    shared_pool: SharedPool,
    refill_lock: Arc<Mutex<()>>,
    probe_url: Arc<String>,
) -> Result<()> {
    let part_path = out_dir.join(format!("{file_name}.part"));
    let final_path = out_dir.join(file_name);
    let state_file = state_path(&part_path);

    if final_path.exists() {
        eprintln!("[skip] {file_name} already done");
        return Ok(());
    }

    let num_chunks = ((file_size + CHUNK_SIZE - 1) / CHUNK_SIZE) as usize;

    let mut done_set: HashSet<usize> = if part_path.exists() {
        let s = load_state(&state_file);
        if !s.is_empty() { eprintln!("[resume] {file_name}: {}/{num_chunks} chunks done", s.len()); }
        s
    } else { HashSet::new() };

    if !part_path.exists() || std::fs::metadata(&part_path).map(|m| m.len()).unwrap_or(0) != file_size {
        let f = tokio::fs::OpenOptions::new().create(true).write(true)
            .open(&part_path).await?;
        f.set_len(file_size).await?;
    }

    let file = Arc::new(Mutex::new(
        tokio::fs::OpenOptions::new().write(true).open(&part_path).await?
    ));

    let pb = Arc::new({
        let already = done_set.iter().map(|&i| {
            ((i as u64 + 1) * CHUNK_SIZE).min(file_size) - i as u64 * CHUNK_SIZE
        }).sum::<u64>();
        let p = ProgressBar::new(file_size);
        p.set_style(ProgressStyle::default_bar()
            .template(&format!("[dl] {{bar:50}} {{bytes}}/{{total_bytes}} @ {{bytes_per_sec}} eta {{eta}}  {file_name}"))
            .unwrap());
        p.inc(already);
        p
    });

    let aes_key = Arc::new(aes_key);
    let iv = Arc::new(iv);

    let mut dl_url = refresh_dl_url(base, file_id).await?;
    let mut done_count = done_set.len();

    let mut remaining: Vec<Chunk> = (0..num_chunks)
        .filter(|i| !done_set.contains(i))
        .map(|i| Chunk {
            idx: i,
            start: i as u64 * CHUNK_SIZE,
            end: (i as u64 * CHUNK_SIZE + CHUNK_SIZE - 1).min(file_size - 1),
        })
        .collect();

    for round in 0..MAX_ROUNDS {
        if remaining.is_empty() { break; }

        if round > 0 {
            eprintln!("[mega] refreshing URL for {file_name}…");
            dl_url = refresh_dl_url(base, file_id).await?;
        }
        let url = Arc::new(dl_url.clone());

        let n = remaining.len();
        let (work_tx, work_rx) = mpsc::channel::<Chunk>(n + 1);
        let (retry_tx, mut retry_rx) = mpsc::channel::<Chunk>(n + 1);
        let (result_tx, mut result_rx) = mpsc::channel::<ChunkResult>(n + 1);

        for c in remaining.drain(..) { work_tx.send(c).await.unwrap(); }
        drop(work_tx); // closed → workers exit via try_recv once queue drains
        let work_rx = Arc::new(Mutex::new(work_rx));

        // Spawn one worker per proxy that is ready right now.
        // Workers share the work channel: any worker can take any chunk.
        let mut worker_set: JoinSet<Option<String>> = JoinSet::new();
        let spawn_worker = |ws: &mut JoinSet<Option<String>>, proxy: Option<String>| {
            let (wrx, rtx, restx, u, pb2) = (
                work_rx.clone(), retry_tx.clone(), result_tx.clone(),
                url.clone(), pb.clone(),
            );
            ws.spawn(proxy_worker(proxy, u, wrx, rtx, restx, pb2, 120));
        };

        // Drain whatever is in the pool right now.
        {
            let mut pool = shared_pool.lock().await;
            for p in pool.drain(..) { spawn_worker(&mut worker_set, Some(p)); }
        }

        // Collector: decrypts and writes results as they stream in.
        let file2 = file.clone(); let k2 = aes_key.clone(); let iv2 = iv.clone();
        let ds2 = done_set.clone();
        let collector = tokio::spawn(async move {
            let mut count = 0usize;
            let mut nd = ds2;
            while let Some((idx, start, data)) = result_rx.recv().await {
                let mut data = data.to_vec();
                decrypt_chunk(&mut data, &k2, &iv2, start);
                let mut f = file2.lock().await;
                f.seek(std::io::SeekFrom::Start(start)).await?;
                f.write_all(&data).await?;
                nd.insert(idx);
                count += 1;
            }
            Ok::<(usize, HashSet<usize>), anyhow::Error>((count, nd))
        });

        // Drive workers.  Every 250 ms we also check shared_pool for proxies
        // that background probing has just validated and add them as workers.
        // This means latecomer proxies join the ongoing round and speed it up
        // rather than sitting idle until a hypothetical next round.
        let mut local_returned: Vec<Option<String>> = Vec::new();
        loop {
            // Recruit any newly-found proxies from the background probe task.
            {
                let mut pool = shared_pool.lock().await;
                for p in pool.drain(..) { spawn_worker(&mut worker_set, Some(p)); }
            }
            if worker_set.is_empty() { break; }

            // Wait for the next worker to finish, re-checking every 250 ms.
            match tokio::time::timeout(
                Duration::from_millis(250),
                worker_set.join_next(),
            ).await {
                Ok(Some(Ok(ret))) => { local_returned.push(ret); }
                Ok(None) => break,                    // JoinSet emptied
                Ok(Some(Err(_))) | Err(_) => {}       // panic or poll timeout
            }
        }

        // Close channels so the collector task can finish draining results.
        drop(retry_tx);
        drop(result_tx);

        let (written, nd) = collector.await??;
        done_set = nd;
        done_count += written;

        while let Ok(c) = retry_rx.try_recv() { remaining.push(c); }
        save_state(&state_file, &done_set);
        eprintln!("[dl] {done_count}/{num_chunks} chunks done, {} to retry", remaining.len());

        // Return healthy proxies for the next round (or to the pool at large).
        {
            let mut pool = shared_pool.lock().await;
            for p in local_returned.into_iter().flatten() { pool.push_back(p); }
        }

        if !remaining.is_empty() && shared_pool.lock().await.is_empty() {
            refill_shared_pool(&shared_pool, base, &probe_url, &refill_lock).await;
        }
    }

    pb.finish_and_clear();
    if done_count < num_chunks {
        eprintln!("WARNING: {file_name}: only {done_count}/{num_chunks} chunks after {MAX_ROUNDS} rounds");
        return Ok(());
    }

    tokio::fs::rename(&part_path, &final_path).await?;
    tokio::fs::remove_file(&state_file).await.ok();
    eprintln!("[done] {}  ({file_size} bytes)", final_path.display());
    Ok(())
}

// ── Folder download — global chunk queue ──────────────────────────────────────
//
// Instead of a per-file semaphore+worker model (bottleneck for many small
// files), all pending chunks across ALL files are fed into one shared channel.
// Each proxy worker continuously pulls and downloads chunks regardless of which
// file they belong to.  Files complete naturally when their last chunk lands.
// This keeps every proxy busy and scales to thousands of small files.

const FOLDER_CHUNK_SIZE: u64 = 1024 * 1024;
const FOLDER_TIMEOUT: u64 = 60;

// One unit of work pulled by a folder proxy worker.
struct FolderChunk {
    url: Arc<Mutex<String>>,        // refreshable per-file URL
    folder_id: Arc<String>,         // for URL refresh on retry
    node_handle: Arc<String>,       // for URL refresh on retry
    chunk: Chunk,
    file: Arc<Mutex<tokio::fs::File>>,
    aes_key: Arc<[u8; 16]>,
    iv: Arc<[u8; 16]>,
    // Shared across all chunks for the same file
    pending: Arc<AtomicUsize>,      // chunks not yet successfully written
    done_set: Arc<Mutex<HashSet<usize>>>,
    part_path: Arc<PathBuf>,
    final_path: Arc<PathBuf>,
    state_path: Arc<PathBuf>,
    pb: Arc<ProgressBar>,
    total_bytes: u64,
}

// Worker assigned to one proxy. Pulls FolderChunks from `work_rx`, downloads,
// decrypts, writes.  Failed chunks go to `retry_tx`.
// Returns Some(proxy) if it exhausted the queue while still healthy.
async fn folder_chunk_worker(
    proxy: String,
    work_rx: Arc<Mutex<mpsc::Receiver<FolderChunk>>>,
    retry_tx: mpsc::Sender<FolderChunk>,
) -> Option<String> {
    let client = make_client(Some(&proxy), FOLDER_TIMEOUT).ok()?;
    let mut consec = 0;
    loop {
        let job = {
            let mut rx = work_rx.lock().await;
            match rx.try_recv() { Ok(j) => j, Err(_) => break }
        };
        let url_snap = job.url.lock().await.clone();
        match download_range(&client, &url_snap, job.chunk.start, job.chunk.end).await {
            Ok(data) => {
                consec = 0;
                let mut data = data.to_vec();
                decrypt_chunk(&mut data, &job.aes_key, &job.iv, job.chunk.start);
                {
                    let mut f = job.file.lock().await;
                    if f.seek(std::io::SeekFrom::Start(job.chunk.start)).await.is_ok() {
                        let _ = f.write_all(&data).await;
                    }
                }
                job.pb.inc(data.len() as u64);
                let was_last = {
                    let mut ds = job.done_set.lock().await;
                    let is_new = ds.insert(job.chunk.idx);
                    // Periodic state save (every 32 chunks or on completion)
                    if is_new && (ds.len() % 32 == 0) { save_state(&job.state_path, &ds); }
                    is_new && job.pending.fetch_sub(1, Ordering::SeqCst) == 1
                };
                if was_last {
                    let ds = job.done_set.lock().await;
                    save_state(&job.state_path, &ds);
                    drop(ds);
                    if let Err(e) = tokio::fs::rename(&*job.part_path, &*job.final_path).await {
                        eprintln!("[finalize] {e}");
                    } else {
                        tokio::fs::remove_file(&*job.state_path).await.ok();
                        job.pb.finish_and_clear();
                        eprintln!("[done] {}  ({} bytes)", job.final_path.display(), job.total_bytes);
                    }
                }
            }
            Err(e) => {
                let _ = retry_tx.send(job).await;
                if is_quota_error(&e) {
                    return None;
                }
                consec += 1;
                if consec >= MAX_CONSEC_FAIL {
                    return None;
                }
            }
        }
    }
    Some(proxy)
}

async fn refill_shared_pool(
    pool: &SharedPool,
    base: &Client,
    probe_url: &str,
    refill_lock: &Arc<Mutex<()>>,
) {
    let _guard = refill_lock.lock().await;
    if pool.lock().await.len() >= 5 { return; }
    eprintln!("[proxy] shared pool low — refilling…");
    let new_proxies = build_proxy_pool(base, probe_url, FOLDER_MAX_GOOD).await;
    let mut p = pool.lock().await;
    p.extend(new_proxies);
}

// Downloads all files using a global chunk queue shared across all proxy workers.
async fn download_folder(
    base: &Client,
    folder_id: &str,
    files: Vec<FileEntry>,
    shared_pool: SharedPool,
    refill_lock: Arc<Mutex<()>>,
    probe_url: Arc<String>,
    mp: Arc<MultiProgress>,
) -> Result<()> {
    // Batch-prefetch all download URLs before spawning any worker.
    eprintln!("[mega] prefetching {} download URLs…", files.len());
    let handles_list: Vec<String> = files.iter().map(|f| f.handle.clone()).collect();
    let prefetched_urls = prefetch_folder_urls(base, folder_id, &handles_list).await;

    // Create output directories.
    for entry in &files {
        if let Some(parent) = entry.path.parent() {
            if parent != Path::new("") {
                tokio::fs::create_dir_all(parent).await?;
            }
        }
    }

    // Build the initial flat list of all pending chunks across all files.
    let mut all_chunks: Vec<FolderChunk> = Vec::new();

    for (entry, maybe_url) in files.iter().zip(prefetched_urls.iter()) {
        let file_name = entry.path.file_name().unwrap_or_default()
            .to_string_lossy().to_string();
        let out_dir = entry.path.parent()
            .filter(|p| *p != Path::new(""))
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|| PathBuf::from("."));
        let part_path = Arc::new(out_dir.join(format!("{file_name}.part")));
        let final_path = Arc::new(out_dir.join(&file_name));
        let sp = Arc::new(state_path(&part_path));

        if final_path.exists() {
            eprintln!("[skip] {file_name} already done");
            continue;
        }

        // Empty files: just create them immediately.
        if entry.size == 0 {
            tokio::fs::File::create(&*final_path).await.ok();
            eprintln!("[done] {file_name}  (0 bytes)");
            continue;
        }

        let num_chunks = ((entry.size + FOLDER_CHUNK_SIZE - 1) / FOLDER_CHUNK_SIZE) as usize;

        let done_set_inner: HashSet<usize> = if part_path.exists() {
            let s = load_state(&sp);
            if !s.is_empty() {
                eprintln!("[resume] {file_name}: {}/{num_chunks} chunks", s.len());
            }
            s
        } else {
            HashSet::new()
        };

        if !part_path.exists()
            || std::fs::metadata(&*part_path).map(|m| m.len()).unwrap_or(0) != entry.size
        {
            let f = tokio::fs::OpenOptions::new().create(true).write(true)
                .open(&*part_path).await?;
            f.set_len(entry.size).await?;
        }

        let pending_chunks: Vec<Chunk> = (0..num_chunks)
            .filter(|i| !done_set_inner.contains(i))
            .map(|i| Chunk {
                idx: i,
                start: i as u64 * FOLDER_CHUNK_SIZE,
                end: (i as u64 * FOLDER_CHUNK_SIZE + FOLDER_CHUNK_SIZE - 1).min(entry.size - 1),
            })
            .collect();

        // All chunks already done (resume case) — finalize immediately.
        if pending_chunks.is_empty() {
            tokio::fs::rename(&*part_path, &*final_path).await?;
            tokio::fs::remove_file(&*sp).await.ok();
            eprintln!("[done] {file_name}  ({} bytes)", entry.size);
            continue;
        }

        let file_handle = Arc::new(Mutex::new(
            tokio::fs::OpenOptions::new().write(true).open(&*part_path).await?
        ));

        let already_bytes = done_set_inner.iter().map(|&i| {
            ((i as u64 + 1) * FOLDER_CHUNK_SIZE).min(entry.size) - i as u64 * FOLDER_CHUNK_SIZE
        }).sum::<u64>();

        let pb = Arc::new({
            let p = mp.add(ProgressBar::new(entry.size));
            p.set_style(ProgressStyle::default_bar()
                .template(&format!("{{bar:40}} {{bytes}}/{{total_bytes}} @ {{bytes_per_sec}} eta {{eta}}  {file_name}"))
                .unwrap());
            p.inc(already_bytes);
            p
        });

        let pending = Arc::new(AtomicUsize::new(pending_chunks.len()));
        let done_set = Arc::new(Mutex::new(done_set_inner));
        // All chunks for this file share the same Arc<Mutex<String>> URL so a
        // single refresh in the retry phase propagates to all of them.
        let url_arc = Arc::new(Mutex::new(
            maybe_url.clone().unwrap_or_default()
        ));
        let handle_arc = Arc::new(entry.handle.clone());
        let folder_arc = Arc::new(folder_id.to_owned());
        let aes_key = Arc::new(entry.aes_key);
        let iv = Arc::new(entry.iv);

        eprintln!("[queue] {file_name}  ({} bytes, {} chunks)", entry.size, pending_chunks.len());
        for chunk in pending_chunks {
            all_chunks.push(FolderChunk {
                url: url_arc.clone(),
                folder_id: folder_arc.clone(),
                node_handle: handle_arc.clone(),
                chunk,
                file: file_handle.clone(),
                aes_key: aes_key.clone(),
                iv: iv.clone(),
                pending: pending.clone(),
                done_set: done_set.clone(),
                part_path: part_path.clone(),
                final_path: final_path.clone(),
                state_path: sp.clone(),
                pb: pb.clone(),
                total_bytes: entry.size,
            });
        }
    }

    if all_chunks.is_empty() {
        return Ok(());
    }

    eprintln!("[dl] {} total chunks across files", all_chunks.len());

    // Shuffle so workers spread evenly across files rather than serializing them.
    all_chunks.shuffle(&mut rand::thread_rng());

    let mut retry_chunks: Vec<FolderChunk> = Vec::new();

    for round in 0..MAX_ROUNDS {
        let current: Vec<FolderChunk> = if round == 0 {
            all_chunks.drain(..).collect()
        } else {
            if retry_chunks.is_empty() { break; }
            eprintln!("[dl] round {round}: refreshing URLs for {} failed chunks", retry_chunks.len());

            // Refresh URLs once per unique file (chunks for the same file share
            // an Arc<Mutex<String>>, so updating it propagates to all of them).
            let mut seen: HashSet<usize> = HashSet::new();
            for chunk in &retry_chunks {
                let ptr = Arc::as_ptr(&chunk.url) as usize;
                if seen.insert(ptr) {
                    if let Ok(new_url) = folder_file_url(
                        base, &chunk.folder_id, &chunk.node_handle
                    ).await {
                        *chunk.url.lock().await = new_url;
                    }
                }
            }
            retry_chunks.drain(..).collect()
        };

        let n = current.len();
        let (work_tx, work_rx) = mpsc::channel::<FolderChunk>(n + 1);
        let (retry_tx, mut retry_rx) = mpsc::channel::<FolderChunk>(n + 1);

        for c in current { work_tx.send(c).await.unwrap(); }
        drop(work_tx); // closed → workers exit via try_recv when queue drains
        let work_rx = Arc::new(Mutex::new(work_rx));

        // Seed workers from the pool; if pool is empty wait/refill first.
        let mut worker_set: JoinSet<Option<String>> = JoinSet::new();
        let spawn_fw = |ws: &mut JoinSet<Option<String>>, p: String| {
            ws.spawn(folder_chunk_worker(p, work_rx.clone(), retry_tx.clone()));
        };

        loop {
            let initial: Vec<String> = shared_pool.lock().await.drain(..).collect();
            if !initial.is_empty() {
                for p in initial { spawn_fw(&mut worker_set, p); }
                break;
            }
            // Pool genuinely empty (all proxies died) → refill, then retry.
            refill_shared_pool(&shared_pool, base, &probe_url, &refill_lock).await;
        }

        // Drive workers + recruit newly-found proxies every 250 ms.
        let mut local_returned: Vec<String> = Vec::new();
        loop {
            {
                let new_proxies: Vec<String> = shared_pool.lock().await.drain(..).collect();
                for p in new_proxies { spawn_fw(&mut worker_set, p); }
            }
            if worker_set.is_empty() { break; }

            match tokio::time::timeout(
                Duration::from_millis(250),
                worker_set.join_next(),
            ).await {
                Ok(Some(Ok(Some(p)))) => { local_returned.push(p); }
                Ok(None) => break,
                Ok(Some(Ok(None))) | Ok(Some(Err(_))) | Err(_) => {}
            }
        }
        drop(retry_tx);

        while let Ok(c) = retry_rx.try_recv() { retry_chunks.push(c); }

        // Return healthy proxies.
        {
            let mut pool = shared_pool.lock().await;
            pool.extend(local_returned);
        }

        if retry_chunks.is_empty() { break; }
    }

    if !retry_chunks.is_empty() {
        eprintln!("WARNING: {} chunks could not be downloaded after {MAX_ROUNDS} rounds",
                  retry_chunks.len());
    }

    Ok(())
}

// ── Main ──────────────────────────────────────────────────────────────────────

#[cfg(unix)]
fn raise_fd_limit() {
    unsafe {
        let mut rl = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        if libc::getrlimit(libc::RLIMIT_NOFILE, &mut rl) == 0 {
            let target = rl.rlim_max.min(8192);
            if rl.rlim_cur < target {
                rl.rlim_cur = target;
                libc::setrlimit(libc::RLIMIT_NOFILE, &rl);
            }
        }
    }
}

#[cfg(not(unix))]
fn raise_fd_limit() {}

#[tokio::main]
async fn main() -> Result<()> {
    raise_fd_limit();
    let link = std::env::args().nth(1)
        .unwrap_or_else(|| std::fs::read_to_string("../link.txt")
            .unwrap_or_default().trim().to_owned());
    if link.is_empty() { return Err(anyhow!("Usage: mega-dl <mega-link>")); }

    let base = Client::builder().timeout(Duration::from_secs(30)).build()?;

    match parse_link(&link)? {
        MegaLink::File { id, raw_key } => {
            let (aes_key, iv) = fold_key(&raw_key);
            eprintln!("[mega] file id={id}");
            let (dl_url, size, at) = file_dl_info(&base, &id).await?;
            eprintln!("[mega] size={size}");

            let name = decrypt_attrs(&at, &aes_key)
                .ok()
                .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
                .and_then(|v| v["n"].as_str().map(|s| s.to_owned()))
                .unwrap_or_else(|| format!("{id}.bin"));
            eprintln!("[mega] name={name}");

            let shared_pool: SharedPool = Arc::new(Mutex::new(VecDeque::new()));
            let refill_lock = Arc::new(Mutex::new(()));
            let probe_url = Arc::new(dl_url.clone());
            let ready = Arc::new(Notify::new());

            spawn_proxy_probing(
                base.clone(), dl_url, SINGLE_MAX_GOOD,
                shared_pool.clone(), refill_lock.clone(), ready.clone(),
                MIN_PROXIES_TO_START,
            );
            ready.notified().await;

            download_file(
                &base, &id, aes_key, iv, &name, size, Path::new("."),
                shared_pool, refill_lock, probe_url,
            ).await?;
        }

        MegaLink::Folder { id, folder_key } => {
            eprintln!("[mega] folder id={id}");
            let nodes = folder_nodes(&base, &id).await?;
            eprintln!("[mega] {} nodes", nodes.len());

            let files = build_file_list(&nodes, &folder_key)?;
            eprintln!("[mega] {} files to download", files.len());
            if files.is_empty() { return Ok(()); }

            let probe_url = Arc::new(
                folder_file_url(&base, &id, &files[0].handle).await
                    .unwrap_or_else(|_| "https://g.api.mega.co.nz/".to_owned())
            );

            let shared_pool: SharedPool = Arc::new(Mutex::new(VecDeque::new()));
            let refill_lock = Arc::new(Mutex::new(()));
            let ready = Arc::new(Notify::new());

            spawn_proxy_probing(
                base.clone(), (*probe_url).clone(), FOLDER_MAX_GOOD,
                shared_pool.clone(), refill_lock.clone(), ready.clone(),
                MIN_PROXIES_TO_START,
            );
            ready.notified().await;

            let mp = Arc::new(MultiProgress::new());
            download_folder(
                &base, &id, files,
                shared_pool, refill_lock, probe_url, mp,
            ).await?;
        }
    }
    Ok(())
}
