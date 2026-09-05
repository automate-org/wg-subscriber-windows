#![allow(dead_code)]
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::fs;
use std::io::Write;
use std::net::{IpAddr, Ipv6Addr};
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, bail};
use base64::{Engine, engine::general_purpose::STANDARD as BASE64};
use log::{debug, error, info, warn};
use rand::Rng;
use rumqttc::{
    Client, ConnectReturnCode, Connection, Event, Incoming, MqttOptions, QoS, RecvTimeoutError,
    TlsConfiguration, Transport,
};
use rustls::ClientConfig as RustlsClientConfig;
use serde_json::json;
use tempfile::NamedTempFile;

use blake3;
use ipnet::{IpNet, Ipv4Net, Ipv6Net};
use local_ip_address::list_afinet_netifas;
use std::sync::{Arc, LazyLock, Mutex};

// ---------- 常量 ----------
const DEFAULT_LISTEN_PORT: u16 = 52822;
const HANDSHAKE_MAX_AGE_SECS: u64 = 20;
const MIN_LAN_RETRY_INTERVAL: Duration = Duration::from_secs(120);
const NETWORK_CHECK_INTERVAL: Duration = Duration::from_secs(60);
const NO_HANDSHAKE_THRESHOLD: u64 = 180;
const PORT_CHANGE_LIMIT_WINDOW: Duration = Duration::from_secs(3600);
const MAX_PORT_CHANGES_PER_WINDOW: usize = 3;
const RELAY_FAIL_THRESHOLD: u64 = 180;
const RELAY_FAIL_COUNT_MAX: u32 = 2;

const REGISTER_MAX_RETRIES: u32 = 5;
const REGISTER_RETRY_INTERVAL: Duration = Duration::from_secs(5);
const TRAFFIC_REPORT_INTERVAL: Duration = Duration::from_secs(30);
const RETRY_PROCESS_INTERVAL: Duration = Duration::from_secs(2);
const LAN_CHECK_INTERVAL: Duration = Duration::from_secs(1);
const MAX_RETRY_QUEUE_SIZE: usize = 500;
const DEFAULT_MAX_RETRY_ATTEMPTS: u32 = 5;
const DEFAULT_KEEPALIVE: u16 = 25;

// ---------- LAN 验证任务 ----------
#[derive(Debug, Clone)]
struct LanVerificationTask {
    interface: String,
    pubkey: String,
    new_endpoint: String,
    fallback: Option<String>,
    start: Instant,
    timeout: Duration,
}

// ---------- 全局状态 ----------
static LAST_LAN_ATTEMPT: LazyLock<Mutex<HashMap<String, Instant>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static PORT_CHANGE_HISTORY: LazyLock<Mutex<VecDeque<Instant>>> =
    LazyLock::new(|| Mutex::new(VecDeque::new()));
static RELAY_POOL: LazyLock<Mutex<Vec<String>>> = LazyLock::new(|| Mutex::new(Vec::new()));
static RELAY_LOAD: LazyLock<Mutex<HashMap<String, u32>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static PEER_TO_RELAY: LazyLock<Mutex<HashMap<String, String>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static PEER_FAIL_COUNT: LazyLock<Mutex<HashMap<String, u32>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static LAST_SNAPSHOT_PEERS: LazyLock<Mutex<HashMap<String, PeerInfo>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static LAST_FULL_HASH: LazyLock<Mutex<Option<String>>> = LazyLock::new(|| Mutex::new(None));
static LAST_APPLIED_ROUTES: LazyLock<Mutex<(HashSet<String>, HashSet<String>)>> =
    LazyLock::new(|| Mutex::new((HashSet::new(), HashSet::new())));
static REGISTRATION_STATE: LazyLock<Mutex<RegistrationState>> =
    LazyLock::new(|| Mutex::new(RegistrationState::NotRegistered));
static TRAFFIC_SNAPSHOT: LazyLock<Mutex<HashMap<String, (u64, u64)>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));
static LAN_VERIFICATION_TASKS: LazyLock<Mutex<Vec<LanVerificationTask>>> =
    LazyLock::new(|| Mutex::new(Vec::new()));

static RELAY_CIDR_V4: LazyLock<String> =
    LazyLock::new(|| env::var("RELAY_CIDR_V4").unwrap_or_else(|_| "10.254.1.0/24".to_string()));
static RELAY_CIDR_V6: LazyLock<String> =
    LazyLock::new(|| env::var("RELAY_CIDR_V6").unwrap_or_else(|_| "fd00:1:1::/64".to_string()));

// ---------- 后端选择 ----------
fn wg_cmd() -> &'static str {
    if env::var("WG_USE_AWG")
        .map(|v| v == "1" || v == "true")
        .unwrap_or(false)
    {
        "awg.exe"
    } else {
        "wg.exe"
    }
}

// ---------- 数据结构 ----------
#[derive(Debug, Clone)]
struct RetryTask {
    pubkey: String,
    endpoint: Option<String>,
    allowed_ips: Option<Vec<String>>,
    persistent_keepalive: Option<u16>,
    preshared_key: Option<String>,
    retry_count: u32,
    last_attempt: Instant,
}

impl RetryTask {
    fn new(
        pubkey: String,
        endpoint: Option<String>,
        allowed_ips: Option<Vec<String>>,
        persistent_keepalive: Option<u16>,
        preshared_key: Option<String>,
    ) -> Self {
        Self {
            pubkey,
            endpoint,
            allowed_ips,
            persistent_keepalive,
            preshared_key,
            retry_count: 0,
            last_attempt: Instant::now(),
        }
    }
    fn next_interval(&self) -> Duration {
        Duration::from_secs(1u64 << self.retry_count.min(4))
    }
}

#[derive(Debug, Deserialize, Clone)]
struct AdvertisedRoutes {
    ipv4: Vec<String>,
    ipv6: Vec<String>,
}

#[derive(Debug, Deserialize, Clone)]
struct FullSnapshot {
    peers: HashMap<String, PeerInfo>,
    routes: AdvertisedRoutes,
    #[serde(default)]
    amnezia: Option<AmneziaConfig>,
}

#[derive(Debug, Deserialize, Clone)]
struct PeerInfo {
    #[serde(default)]
    endpoint: Option<String>,
    #[serde(default)]
    allowed_ips: Option<Vec<String>>,
    #[serde(default)]
    persistent_keepalive: Option<u16>,
    // 关键修改：区分 null 和缺失
    #[serde(deserialize_with = "deserialize_psk")]
    preshared_key: Option<String>,
    #[serde(default)]
    local_ips: Option<Vec<String>>,
}

/// 将 JSON 的 null 转为 Some("")（表示主动清除），字段缺失转为 None（表示保留现状）
fn deserialize_psk<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de::{self, Visitor};
    struct PskVisitor;
    impl<'de> Visitor<'de> for PskVisitor {
        type Value = Option<String>;

        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "a string or null")
        }

        fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
            Ok(Some(v.to_string()))
        }

        fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
            // null → Some("")  表示主动清除
            Ok(Some(String::new()))
        }

        fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
            // 字段缺失 → None  表示保留旧值
            Ok(None)
        }

        fn visit_some<D2: serde::Deserializer<'de>>(
            self,
            deserializer: D2,
        ) -> Result<Self::Value, D2::Error> {
            deserializer.deserialize_any(self)
        }
    }

    deserializer.deserialize_option(PskVisitor)
}

#[derive(Debug, Deserialize, Clone)]
struct AmneziaConfig {
    #[serde(default)]
    pub jc: u32,
    #[serde(default)]
    pub jmin: u32,
    #[serde(default)]
    pub jmax: u32,
    #[serde(default)]
    pub s1: u32,
    #[serde(default)]
    pub s2: u32,
    #[serde(default)]
    pub h1: u32,
    #[serde(default)]
    pub h2: u32,
    #[serde(default)]
    pub h3: u32,
    #[serde(default)]
    pub h4: u32,
    // 新增高级参数（可选字符串）
    #[serde(default)]
    pub i1: Option<String>,
    #[serde(default)]
    pub i2: Option<String>,
    #[serde(default)]
    pub i3: Option<String>,
    #[serde(default)]
    pub i4: Option<String>,
    #[serde(default)]
    pub i5: Option<String>,
}

#[derive(Debug, Default, Clone)]
struct WgState {
    pub listen_port: u16,
    pub peers: HashMap<String, PeerState>,
}

#[derive(Debug, Default, Clone)]
struct PeerState {
    pub endpoint: Option<String>,
    pub allowed_ips: Vec<String>,
    pub latest_handshake: Option<u64>,
    pub transfer_rx: u64,
    pub transfer_tx: u64,
}

enum RegistrationState {
    NotRegistered,
    InProgress,
    Registered,
}

// ---------- 密钥管理 ----------
#[derive(Clone)]
struct WireGuardKeys {
    private_key: String,
    public_key: String,
}

impl WireGuardKeys {
    fn generate() -> Self {
        let mut private_bytes = [0u8; 32];
        rand::thread_rng().fill(&mut private_bytes);
        private_bytes[0] &= 248;
        private_bytes[31] &= 127;
        private_bytes[31] |= 64;
        let private_key = BASE64.encode(private_bytes);
        let public_key = Self::derive_public(&private_bytes);
        Self {
            private_key,
            public_key,
        }
    }

    fn derive_public(private_bytes: &[u8; 32]) -> String {
        use x25519_dalek::{PublicKey, StaticSecret};
        let secret = StaticSecret::from(*private_bytes);
        let public = PublicKey::from(&secret);
        BASE64.encode(public.as_bytes())
    }

    fn from_private_key(private_key: &str) -> Result<Self> {
        let private_bytes = BASE64
            .decode(private_key)
            .context("Invalid base64 private key")?;
        if private_bytes.len() != 32 {
            bail!("Private key must be 32 bytes");
        }
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&private_bytes);
        let public_key = Self::derive_public(&bytes);
        Ok(Self {
            private_key: private_key.to_string(),
            public_key,
        })
    }
}

fn get_key_path() -> PathBuf {
    let program_data = env::var("PROGRAMDATA").unwrap_or_else(|_| "C:\\ProgramData".to_string());
    PathBuf::from(program_data)
        .join("wg-subscriber")
        .join("private.key")
}

fn get_self_ips_path() -> PathBuf {
    let program_data = env::var("PROGRAMDATA").unwrap_or_else(|_| "C:\\ProgramData".to_string());
    PathBuf::from(program_data)
        .join("wg-subscriber")
        .join("self_ips.json")
}

fn load_or_generate_keys() -> Result<WireGuardKeys> {
    let key_path = get_key_path();
    if key_path.exists() {
        let content = fs::read_to_string(&key_path)?;
        WireGuardKeys::from_private_key(content.trim())
    } else {
        let keys = WireGuardKeys::generate();
        if let Some(parent) = key_path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&key_path, &keys.private_key)?;
        info!("Generated new WireGuard key pair");
        Ok(keys)
    }
}

// ---------- 自身 IP 持久化 ----------
#[derive(Serialize, Deserialize, Default)]
struct SelfIps {
    ipv4: String,
    ipv6: String,
}
fn load_self_ips() -> Option<SelfIps> {
    let path = get_self_ips_path();
    if path.exists() {
        fs::read_to_string(&path)
            .ok()
            .and_then(|s| serde_json::from_str(&s).ok())
    } else {
        None
    }
}
fn save_self_ips(ipv4: &str, ipv6: &str) {
    let ips = SelfIps {
        ipv4: ipv4.to_string(),
        ipv6: ipv6.to_string(),
    };
    let path = get_self_ips_path();
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let _ = fs::write(&path, serde_json::to_string(&ips).unwrap_or_default());
}

// ---------- 获取接口当前地址 ----------
fn get_interface_addresses(interface: &str) -> (Vec<String>, Vec<String>) {
    let mut v4 = Vec::new();
    let mut v6 = Vec::new();
    if let Ok(ifaces) = list_afinet_netifas() {
        for (iface_name, addr) in ifaces {
            if iface_name.to_lowercase() == interface.to_lowercase() {
                match addr {
                    IpAddr::V4(ip) => v4.push(ip.to_string()),
                    IpAddr::V6(ip) => {
                        if !ip.is_loopback() {
                            v6.push(ip.to_string())
                        }
                    }
                }
            }
        }
    }
    (v4, v6)
}

// ---------- 自身 IP 动态配置（Windows netsh）----------
fn configure_self_ip(interface: &str, ipv4: &str, ipv6: &str) {
    let (current_v4, current_v6) = get_interface_addresses(interface);

    if ipv4.is_empty() {
        for ip in &current_v4 {
            let _ = Command::new("netsh")
                .args(&["interface", "ip", "delete", "address", interface, ip])
                .status();
            info!("Removed IPv4 address {} from {}", ip, interface);
        }
    } else {
        let target_ip = ipv4.split('/').next().unwrap_or(ipv4);
        for ip in &current_v4 {
            if ip.as_str() != target_ip {
                let _ = Command::new("netsh")
                    .args(&["interface", "ip", "delete", "address", interface, ip])
                    .status();
                info!("Removed stray IPv4 address {} from {}", ip, interface);
            }
        }
        if !current_v4.contains(&target_ip.to_string()) {
            let status = Command::new("netsh")
                .args(&[
                    "interface",
                    "ip",
                    "add",
                    "address",
                    interface,
                    target_ip,
                    "255.255.255.255",
                ])
                .status();
            match status {
                Ok(s) if s.success() => info!("Added IPv4 address {} to {}", target_ip, interface),
                _ => error!("Failed to add IPv4 address {} to {}", target_ip, interface),
            }
        } else {
            debug!("IPv4 address {} already correct, keeping", target_ip);
        }
    }

    if ipv6.is_empty() {
        for ip in &current_v6 {
            let _ = Command::new("netsh")
                .args(&["interface", "ipv6", "delete", "address", interface, ip])
                .status();
            info!("Removed IPv6 address {} from {}", ip, interface);
        }
    } else {
        let target_ip = ipv6.split('/').next().unwrap_or(ipv6);
        for ip in &current_v6 {
            if ip.as_str() != target_ip {
                let _ = Command::new("netsh")
                    .args(&["interface", "ipv6", "delete", "address", interface, ip])
                    .status();
                info!("Removed stray IPv6 address {} from {}", ip, interface);
            }
        }
        if !current_v6.contains(&target_ip.to_string()) {
            let status = Command::new("netsh")
                .args(&["interface", "ipv6", "add", "address", interface, ipv6])
                .status();
            match status {
                Ok(s) if s.success() => info!("Added IPv6 address {} to {}", ipv6, interface),
                _ => error!("Failed to add IPv6 address {} to {}", ipv6, interface),
            }
        } else {
            debug!("IPv6 address {} already correct, keeping", target_ip);
        }
    }
}

fn extract_self_ips(allowed_ips: &[String]) -> (String, String) {
    let mut ipv4 = String::new();
    let mut ipv6 = String::new();
    for cidr in allowed_ips {
        let (ip_str, prefix) = match cidr.split_once('/') {
            Some((ip, p)) => (ip, p.parse::<u8>().unwrap_or(0)),
            None => (cidr.as_str(), 32),
        };
        if let Ok(ip) = ip_str.parse::<IpAddr>() {
            match ip {
                IpAddr::V4(_) if prefix == 32 && ipv4.is_empty() => ipv4 = cidr.clone(),
                IpAddr::V6(_) if prefix == 128 && ipv6.is_empty() => ipv6 = cidr.clone(),
                _ => {}
            }
        }
    }
    (ipv4, ipv6)
}

// ---------- WireGuard 接口 ----------
struct WgInterface {
    name: String,
    key_path: PathBuf,
    config_path: PathBuf,
    installed: bool,
}
impl WgInterface {
    fn new(name: &str, keys: &WireGuardKeys) -> Result<Self> {
        let key_path = get_key_path();
        fs::write(&key_path, &keys.private_key)?;
        let current_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let config_path = current_dir.join(format!("{}.conf", name));
        if config_path.exists() {
            let _ = fs::remove_file(&config_path);
        }
        Ok(Self {
            name: name.to_string(),
            key_path,
            config_path,
            installed: false,
        })
    }

    fn install_with_config(
        &mut self,
        self_ipv4: &str,
        self_ipv6: &str,
        all_peers: &HashMap<String, serde_json::Value>,
    ) -> Result<()> {
        let listen_port = env::var("WG_LISTEN_PORT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(DEFAULT_LISTEN_PORT);
        let private_key = fs::read_to_string(&self.key_path)?.trim().to_string();
        let mut conf_lines = vec![
            "[Interface]".to_string(),
            format!("PrivateKey = {}", private_key),
            format!("ListenPort = {}", listen_port),
        ];
        let mut addresses = Vec::new();
        if !self_ipv4.is_empty() {
            addresses.push(self_ipv4.to_string());
        }
        if !self_ipv6.is_empty() {
            addresses.push(self_ipv6.to_string());
        }
        if !addresses.is_empty() {
            conf_lines.push(format!("Address = {}", addresses.join(", ")));
        }

        let peer_to_relay = PEER_TO_RELAY.lock().unwrap();
        for (pubkey, peer_val) in all_peers {
            if peer_to_relay.contains_key(pubkey) {
                continue;
            }
            conf_lines.push("".to_string());
            conf_lines.push("[Peer]".to_string());
            conf_lines.push(format!("PublicKey = {}", pubkey));
            if let Some(ep) = peer_val.get("endpoint").and_then(|v| v.as_str()) {
                conf_lines.push(format!("Endpoint = {}", ep));
            }
            if let Some(psk) = peer_val.get("preshared_key").and_then(|v| v.as_str()) {
                conf_lines.push(format!("PresharedKey = {}", psk));
            }
            if let Some(ka) = peer_val
                .get("persistent_keepalive")
                .and_then(|v| v.as_u64())
            {
                conf_lines.push(format!("PersistentKeepalive = {}", ka));
            }
            if let Some(ips) = peer_val.get("allowed_ips").and_then(|v| v.as_array()) {
                let ips_str: Vec<String> = ips
                    .iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect();
                if !ips_str.is_empty() {
                    conf_lines.push(format!("AllowedIPs = {}", ips_str.join(", ")));
                }
            }
        }
        drop(peer_to_relay);

        let conf_content = conf_lines.join("\n");
        fs::write(&self.config_path, &conf_content)?;
        info!("Config saved to {}", self.config_path.display());

        let service_name = format!("WireGuardTunnel${}", self.name);
        let _ = Command::new("wireguard")
            .args(["/uninstalltunnelservice", &self.name])
            .output();
        let _ = Command::new("sc").args(["stop", &service_name]).output();
        let _ = Command::new("sc").args(["delete", &service_name]).output();
        thread::sleep(Duration::from_secs(2));

        info!("Installing tunnel service...");
        let output = Command::new("wireguard")
            .args(["/installtunnelservice", self.config_path.to_str().unwrap()])
            .output()
            .context("Failed to install WireGuard tunnel service")?;
        if !output.status.success() {
            bail!(
                "WireGuard install failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        self.installed = true;
        info!("Tunnel service installed successfully");
        save_self_ips(self_ipv4, self_ipv6);

        for _ in 0..30 {
            if let Ok(out) = Command::new(wg_cmd()).args(["show", &self.name]).output() {
                if out.status.success() {
                    return Ok(());
                }
            }
            thread::sleep(Duration::from_secs(1));
        }
        bail!("Interface not ready after 30 seconds");
    }

    fn update_peer(&self, peer: &serde_json::Value) -> Result<()> {
        let pubkey = peer
            .get("pubkey")
            .and_then(|v| v.as_str())
            .context("Missing pubkey")?;
        let mut args = vec![
            "set".to_string(),
            self.name.clone(),
            "peer".to_string(),
            pubkey.to_string(),
        ];

        // 如果 preshared_key 是空字符串，则先删除再重新添加（以清除 PSK）
        let psk_to_clear = peer
            .get("preshared_key")
            .and_then(|v| v.as_str())
            .filter(|s| s.is_empty())
            .is_some();
        if psk_to_clear {
            self.remove_peer(pubkey)?;
            // 重新添加时不带 preshared-key 参数
        } else if let Some(psk) = peer.get("preshared_key").and_then(|v| v.as_str()) {
            let mut temp_file = NamedTempFile::new()?;
            temp_file.write_all(psk.as_bytes())?;
            temp_file.flush()?;
            let path = temp_file.path().to_string_lossy().to_string();
            args.push("preshared-key".to_string());
            args.push(path);
        }

        if let Some(ep) = peer.get("endpoint").and_then(|v| v.as_str()) {
            args.push("endpoint".to_string());
            args.push(ep.to_string());
        }
        if let Some(ka) = peer.get("persistent_keepalive").and_then(|v| v.as_u64()) {
            args.push("persistent-keepalive".to_string());
            args.push(ka.to_string());
        }
        if let Some(ips) = peer.get("allowed_ips").and_then(|v| v.as_array()) {
            let ips_str: Vec<String> = ips
                .iter()
                .filter_map(|v| v.as_str().map(String::from))
                .collect();
            if !ips_str.is_empty() {
                args.push("allowed-ips".to_string());
                args.push(ips_str.join(","));
            }
        }

        let output = Command::new(wg_cmd()).args(&args).output()?;
        if !output.status.success() {
            bail!(
                "Failed to update peer {}: {}",
                pubkey,
                String::from_utf8_lossy(&output.stderr)
            );
        }
        Ok(())
    }

    fn remove_peer(&self, pubkey: &str) -> Result<()> {
        let output = Command::new(wg_cmd())
            .args(["set", &self.name, "peer", pubkey, "remove"])
            .output()?;
        if !output.status.success() {
            bail!(
                "Failed to remove peer {}: {}",
                pubkey,
                String::from_utf8_lossy(&output.stderr)
            );
        }
        Ok(())
    }
}

// ---------- 路由管理 ----------
fn get_interface_index(if_name: &str) -> Result<u32> {
    for attempt in 0..3 {
        if attempt > 0 {
            thread::sleep(Duration::from_secs(1));
        }
        if let Ok(output) = Command::new("netsh")
            .args(["interface", "ipv4", "show", "interfaces"])
            .output()
        {
            let stdout = String::from_utf8_lossy(&output.stdout);
            for line in stdout.lines() {
                if line.to_lowercase().contains(&if_name.to_lowercase()) {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    for (i, part) in parts.iter().enumerate() {
                        if let Ok(idx) = part.parse::<u32>() {
                            if i > 0 && parts[i - 1].to_lowercase() == if_name.to_lowercase() {
                                return Ok(idx);
                            }
                        }
                    }
                    for part in parts {
                        if let Ok(idx) = part.parse::<u32>() {
                            return Ok(idx);
                        }
                    }
                }
            }
        }
        if let Ok(output) = Command::new("wmic")
            .args([
                "nic",
                "where",
                &format!("NetConnectionID='{}'", if_name),
                "get",
                "InterfaceIndex",
            ])
            .output()
        {
            let stdout = String::from_utf8_lossy(&output.stdout);
            for line in stdout.lines() {
                let line = line.trim();
                if line.is_empty() || line == "InterfaceIndex" {
                    continue;
                }
                if let Ok(idx) = line.parse::<u32>() {
                    return Ok(idx);
                }
            }
        }
    }
    bail!("Interface index not found after retries");
}
// 路由辅助函数
fn prefix_to_v4_netmask(prefix: u8) -> String {
    if prefix == 0 {
        return "0.0.0.0".to_string();
    }
    let mask = u32::MAX << (32 - prefix);
    let octets = [
        ((mask >> 24) & 0xff) as u8,
        ((mask >> 16) & 0xff) as u8,
        ((mask >> 8) & 0xff) as u8,
        (mask & 0xff) as u8,
    ];
    format!("{}.{}.{}.{}", octets[0], octets[1], octets[2], octets[3])
}

fn is_valid_cidr(s: &str) -> bool {
    s.parse::<ipnet::IpNet>().is_ok()
}

fn get_ipv4_routes() -> Result<Vec<(String, String, String)>> {
    let output = Command::new("route")
        .args(["print", "-4"])
        .output()
        .context("Failed to execute route print -4")?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut routes = Vec::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // 只解析以数字开头的行（IPv4 路由的“网络目标”列总是数字）
        if !line
            .chars()
            .next()
            .map(|c| c.is_ascii_digit())
            .unwrap_or(false)
        {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 4 {
            // 格式：Network Destination  Netmask  Gateway  Interface  Metric
            routes.push((
                parts[0].to_string(), // 目标
                parts[1].to_string(), // 掩码
                parts[3].to_string(), // 接口 IP
            ));
        }
    }
    Ok(routes)
}

fn get_ipv6_routes() -> Result<Vec<(String, u8, String)>> {
    let output = Command::new("route")
        .args(["print", "-6"])
        .output()
        .context("Failed to execute route print -6")?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut routes = Vec::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        // 有效路由行的“网络目标”列必定包含 ':'（IPv6 地址特征）
        if parts.len() >= 3 && parts[0].contains(':') {
            let net = parts[0].to_string();
            let prefix: u8 = parts[1].parse().unwrap_or(0);
            let if_desc = parts.get(2).map(|s| s.to_string()).unwrap_or_default();
            routes.push((net, prefix, if_desc));
        }
    }
    Ok(routes)
}

fn find_route_v4(network: &str, netmask: &str) -> Option<String> {
    let routes = get_ipv4_routes().ok()?;
    routes
        .into_iter()
        .find(|(net, mask, _)| net == network && mask == netmask)
        .map(|(_, _, if_ip)| if_ip)
}

fn route_v6_exists(network: &str, prefix: u8) -> bool {
    get_ipv6_routes()
        .map(|routes| {
            routes
                .iter()
                .any(|(net, pfx, _)| net == network && *pfx == prefix)
        })
        .unwrap_or(false)
}

fn apply_advertised_routes(if_name: &str, routes: &AdvertisedRoutes) -> Result<()> {
    let new_ipv4: HashSet<String> = routes.ipv4.iter().cloned().collect();
    let new_ipv6: HashSet<String> = routes.ipv6.iter().cloned().collect();
    let mut last = LAST_APPLIED_ROUTES.lock().unwrap();
    let (last_ipv4, last_ipv6) = &*last;

    // 删除旧路由 (保持不变)
    for cidr in last_ipv4.iter() {
        if !new_ipv4.contains(cidr) {
            let _ = Command::new("cmd")
                .args(["/c", "route", "delete", cidr])
                .status();
            info!("Deleted old IPv4 route: {}", cidr);
        }
    }
    for cidr in last_ipv6.iter() {
        if !new_ipv6.contains(cidr) {
            if let Ok(idx) = get_interface_index(if_name) {
                let _ = Command::new("route")
                    .args(["delete", cidr, "::", "if", &idx.to_string()])
                    .status();
            }
            info!("Deleted old IPv6 route: {}", cidr);
        }
    }

    let idx = get_interface_index(if_name).or_else(|_| {
        thread::sleep(Duration::from_secs(1));
        get_interface_index(if_name)
    })?;

    // 获取当前 WG 接口的 IPv4 地址列表，用于冲突判断（忽略 IPv6 列表）
    let (wg_v4_ips, _) = get_interface_addresses(if_name);

    // ---- 添加 IPv4 路由（带格式校验和冲突检测）----
    for cidr in &new_ipv4 {
        if !last_ipv4.contains(cidr) {
            // 1. 校验 CIDR 格式
            if !is_valid_cidr(cidr) {
                error!("Invalid IPv4 CIDR format, skipping: {}", cidr);
                continue;
            }

            let (net_str, prefix) = cidr.split_once('/').unwrap_or((cidr, "32"));
            let prefix: u8 = prefix.parse().unwrap_or(32);
            let mask = prefix_to_v4_netmask(prefix);

            match find_route_v4(net_str, &mask) {
                Some(if_ip) => {
                    if wg_v4_ips.contains(&if_ip) {
                        debug!(
                            "IPv4 route {} already exists on {}, skip adding",
                            cidr, if_name
                        );
                    } else {
                        warn!(
                            "Skipping route {} dev {} because it already exists on another interface (IP {})",
                            cidr, if_name, if_ip
                        );
                    }
                }
                None => {
                    let _ = Command::new("cmd")
                        .args([
                            "/c",
                            "route",
                            "-p",
                            "add",
                            cidr,
                            "0.0.0.0",
                            "if",
                            &idx.to_string(),
                        ])
                        .status();
                    info!("Added IPv4 route: {} on {}", cidr, if_name);
                }
            }
        }
    }

    // ---- 添加 IPv6 路由（带格式校验和冲突检测）----
    for cidr in &new_ipv6 {
        if !last_ipv6.contains(cidr) {
            // 1. 校验 CIDR 格式
            if !is_valid_cidr(cidr) {
                error!("Invalid IPv6 CIDR format, skipping: {}", cidr);
                continue;
            }

            let (net_str, prefix) = cidr.split_once('/').unwrap_or((cidr, "128"));
            let prefix: u8 = prefix.parse().unwrap_or(128);

            if route_v6_exists(net_str, prefix) {
                // IPv6 仅判断是否存在，不进行接口区分（简化处理）
                warn!("IPv6 route {} already exists, skipping add", cidr);
            } else {
                let status = Command::new("route")
                    .args(["-p", "add", cidr, "::", "if", &idx.to_string()])
                    .status();
                match status {
                    Ok(s) if s.success() => info!("Added IPv6 route: {} on {}", cidr, if_name),
                    Ok(s) => error!(
                        "Failed to add IPv6 route: {} (exit code {:?})",
                        cidr,
                        s.code()
                    ),
                    Err(e) => error!("Failed to execute route add for {}: {}", cidr, e),
                }
            }
        }
    }

    *last = (new_ipv4, new_ipv6);
    Ok(())
}

// ---------- Amnezia 配置 ----------
fn apply_amnezia_config(interface: &str, config: &AmneziaConfig) -> Result<()> {
    let mut args = vec![
        "set".to_string(),
        interface.to_string(),
        format!("jc={}", config.jc),
        format!("jmin={}", config.jmin),
        format!("jmax={}", config.jmax),
        format!("s1={}", config.s1),
        format!("s2={}", config.s2),
        format!("h1={}", config.h1),
        format!("h2={}", config.h2),
        format!("h3={}", config.h3),
        format!("h4={}", config.h4),
    ];

    // 追加可选的高级字符串参数
    if let Some(ref v) = config.i1 {
        if !v.is_empty() {
            args.push(format!("i1={}", v));
        }
    }
    if let Some(ref v) = config.i2 {
        if !v.is_empty() {
            args.push(format!("i2={}", v));
        }
    }
    if let Some(ref v) = config.i3 {
        if !v.is_empty() {
            args.push(format!("i3={}", v));
        }
    }
    if let Some(ref v) = config.i4 {
        if !v.is_empty() {
            args.push(format!("i4={}", v));
        }
    }
    if let Some(ref v) = config.i5 {
        if !v.is_empty() {
            args.push(format!("i5={}", v));
        }
    }

    let status = Command::new(wg_cmd())
        .args(&args)
        .status()
        .context("Failed to apply Amnezia config")?;
    if !status.success() {
        bail!("awg set Amnezia config failed");
    }
    info!("Applied Amnezia config to {}", interface);
    Ok(())
}

// ---------- TLS 传输 ----------
fn build_transport() -> Result<Transport> {
    let tls_enable = env::var("MQTT_TLS_ENABLE")
        .map(|v| v == "1" || v == "true")
        .unwrap_or(false);
    if !tls_enable {
        return Ok(Transport::Tcp);
    }

    let mut root_store = rustls::RootCertStore::empty();
    if let Ok(ca_path) = env::var("MQTT_TLS_CA_CERT") {
        let ca_pem = fs::read_to_string(&ca_path)?;
        let mut reader = std::io::BufReader::new(ca_pem.as_bytes());
        let certs =
            rustls_pemfile::certs(&mut reader).context("Failed to parse PEM certificates")?;
        for cert_bytes in certs {
            let cert = rustls::pki_types::CertificateDer::from(cert_bytes);
            root_store
                .add(cert)
                .context("Failed to add CA certificate")?;
        }
    } else {
        let native_certs = rustls_native_certs::load_native_certs()
            .context("Failed to load native certificates")?;
        for cert in native_certs {
            let cert_der = rustls::pki_types::CertificateDer::from(cert.0);
            root_store
                .add(cert_der)
                .context("Failed to add native certificate")?;
        }
    }
    let config = RustlsClientConfig::builder()
        .with_root_certificates(root_store)
        .with_no_client_auth();
    Ok(Transport::Tls(TlsConfiguration::Rustls(Arc::new(config))))
}

fn create_mqtt_connection(
    host: &str,
    port: u16,
    user: Option<&str>,
    pass: Option<&str>,
    client_id: &str,
) -> Result<(Client, Connection)> {
    let transport = build_transport()?;
    let mut opts = MqttOptions::new(client_id, host, port);
    opts.set_keep_alive(Duration::from_secs(30))
        .set_clean_session(false)
        .set_transport(transport);
    if let (Some(u), Some(p)) = (user, pass) {
        opts.set_credentials(u, p);
    }
    Ok(Client::new(opts, 10))
}

static SELF_IP_CONFIGURED: AtomicBool = AtomicBool::new(false);

struct RegisterRetry {
    last_attempt: Instant,
    interval: Duration,
    force: bool,
}
impl RegisterRetry {
    fn new(interval_secs: u64) -> Self {
        Self {
            last_attempt: Instant::now(),
            interval: Duration::from_secs(interval_secs),
            force: false,
        }
    }
    fn should_retry(&mut self) -> bool {
        if self.force || self.last_attempt.elapsed() >= self.interval {
            self.last_attempt = Instant::now();
            self.force = false;
            true
        } else {
            false
        }
    }
    fn force_next(&mut self) {
        self.force = true;
    }
}

// ---------- 内网切换、握手监控等辅助函数 ----------
fn should_report_ipv6(ip: &Ipv6Addr) -> bool {
    if ip.is_multicast() || ip.is_loopback() || ip.is_unspecified() || ip.is_unicast_link_local() {
        return false;
    }
    (ip.segments()[0] & 0xfe00) == 0xfc00
}

fn get_local_lan_networks() -> Vec<IpNet> {
    let mut nets = Vec::new();
    if let Ok(interfaces) = list_afinet_netifas() {
        for (iface_name, addr) in interfaces {
            if iface_name.to_lowercase().starts_with("wg") {
                continue;
            }
            match addr {
                IpAddr::V4(ip) if ip.is_private() && !ip.is_loopback() => {
                    if let Ok(net) = Ipv4Net::new(ip, 24) {
                        nets.push(IpNet::V4(net));
                    }
                }
                IpAddr::V6(ip) if should_report_ipv6(&ip) => {
                    if let Ok(net) = Ipv6Net::new(ip, 64) {
                        nets.push(IpNet::V6(net));
                    }
                }
                _ => {}
            }
        }
    }
    nets
}

fn parse_endpoint(ep: &str) -> Option<(IpAddr, u16)> {
    if let Ok(socket) = ep.parse::<std::net::SocketAddr>() {
        return Some((socket.ip(), socket.port()));
    }
    if let Some((ip_str, port_str)) = ep.rsplit_once(':') {
        if let (Ok(ip), Ok(port)) = (ip_str.parse::<IpAddr>(), port_str.parse::<u16>()) {
            return Some((ip, port));
        }
    }
    None
}

fn find_same_lan_endpoint(
    peer_local_endpoints: &[String],
    my_nets: &[IpNet],
) -> Option<(String, u16)> {
    for ep_str in peer_local_endpoints {
        if let Some((ip, port)) = parse_endpoint(ep_str) {
            for net in my_nets {
                if net.contains(&ip) {
                    return Some((ip.to_string(), port));
                }
            }
        }
    }
    None
}

fn get_current_endpoint(interface: &str, pubkey: &str) -> Option<String> {
    let output = Command::new(wg_cmd())
        .args(["show", interface, "peers", pubkey])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if line.contains("endpoint:") {
            return line.split_whitespace().nth(1).map(|s| s.to_string());
        }
    }
    None
}

fn get_peer_handshake_seconds(interface: &str, pubkey: &str) -> Option<u64> {
    let output = Command::new(wg_cmd())
        .args(["show", interface, "latest-handshakes"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 2 && parts[0] == pubkey {
            return parts[1].parse::<u64>().ok();
        }
    }
    None
}

fn get_wg_latest_handshakes(interface: &str) -> Result<HashMap<String, Option<u64>>> {
    let output = Command::new(wg_cmd())
        .args(["show", interface, "latest-handshakes"])
        .output()
        .context("Failed to execute wg show latest-handshakes")?;
    if !output.status.success() {
        bail!("{}", String::from_utf8_lossy(&output.stderr));
    }
    let stdout = String::from_utf8(output.stdout)?;
    let mut handshakes = HashMap::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        if let (Some(pubkey), Some(ts_str)) = (parts.next(), parts.next()) {
            let ts = if ts_str == "0" {
                None
            } else {
                ts_str.parse::<u64>().ok()
            };
            handshakes.insert(pubkey.to_string(), ts);
        }
    }
    Ok(handshakes)
}

fn has_recent_handshake(interface: &str, pubkey: &str, max_age_secs: u64) -> bool {
    if let Some(handshake_secs) = get_peer_handshake_seconds(interface, pubkey) {
        let now_secs = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        return now_secs.saturating_sub(handshake_secs) <= max_age_secs;
    }
    false
}

// 检查 peer 当前是否通过局域网活跃连接
fn is_lan_switching_enabled() -> bool {
    env::var("ENABLE_LAN_SWITCHING")
        .map(|v| v == "1" || v.to_lowercase() == "true")
        .unwrap_or(false)
}

fn is_lan_active(interface: &str, pubkey: &str, endpoint: &str) -> bool {
    if !is_lan_switching_enabled() {
        return false;
    }
    if let Some((ip, _)) = parse_endpoint(endpoint) {
        let my_nets = get_local_lan_networks();
        let is_lan = my_nets.iter().any(|net| net.contains(&ip));
        let has_recent = has_recent_handshake(interface, pubkey, HANDSHAKE_MAX_AGE_SECS);
        return is_lan && has_recent;
    }
    false
}

fn update_wg_endpoint(interface: &str, pubkey: &str, new_endpoint: &str) {
    let output = Command::new(wg_cmd())
        .args(["set", interface, "peer", pubkey, "endpoint", new_endpoint])
        .output();
    match output {
        Ok(o) if o.status.success() => {
            info!("Updated peer {} endpoint to {}", pubkey, new_endpoint)
        }
        Ok(o) => warn!(
            "Failed to update peer {} endpoint: {}",
            pubkey,
            String::from_utf8_lossy(&o.stderr)
        ),
        Err(e) => error!("Failed to execute wg set endpoint: {}", e),
    }
}

// ---------- 优化后的端点更新（WAN 不再回退）----------
fn update_endpoint_with_fallback(
    interface: &str,
    pubkey: &str,
    new_endpoint: &str,
    _fallback: Option<String>,
) {
    update_wg_endpoint(interface, pubkey, new_endpoint);
    info!(
        "WAN endpoint updated to {} for peer {}, fallback disabled",
        new_endpoint, pubkey
    );
}

// ---------- 优化后的 LAN 切换（任务队列）----------
fn try_switch_to_lan_endpoint(interface: String, pubkey: String, local_endpoints: Vec<String>) {
    {
        let last_attempts = LAST_LAN_ATTEMPT.lock().unwrap();
        if let Some(last) = last_attempts.get(&pubkey) {
            if last.elapsed() < MIN_LAN_RETRY_INTERVAL {
                return;
            }
        }
    }

    let my_nets = get_local_lan_networks();
    if let Some((lan_ip, lan_port)) = find_same_lan_endpoint(&local_endpoints, &my_nets) {
        LAST_LAN_ATTEMPT
            .lock()
            .unwrap()
            .insert(pubkey.clone(), Instant::now());
        let new_endpoint = format!("{}:{}", lan_ip, lan_port);
        let current_ep = get_current_endpoint(&interface, &pubkey);
        if current_ep.as_ref() == Some(&new_endpoint) {
            return;
        }
        let fallback = current_ep.clone();
        update_wg_endpoint(&interface, &pubkey, &new_endpoint);

        LAN_VERIFICATION_TASKS
            .lock()
            .unwrap()
            .push(LanVerificationTask {
                interface,
                pubkey: pubkey.clone(),
                new_endpoint,
                fallback,
                start: Instant::now(),
                timeout: Duration::from_secs(15), // LAN 握手超时
            });
    }
}

// ---------- 处理 LAN 验证任务队列 ----------
fn process_lan_verification_tasks() {
    let mut tasks = LAN_VERIFICATION_TASKS.lock().unwrap();
    if tasks.is_empty() {
        return;
    }

    // 只需要一个 wg 接口名，取第一个任务的
    let iface = tasks.first().unwrap().interface.clone();

    tasks.retain(|task| {
        // 检查 peer 是否仍然存在
        let current_ep = get_current_endpoint(&iface, &task.pubkey);
        let current_ep_matches = current_ep.as_ref() == Some(&task.new_endpoint);
        if !current_ep_matches {
            return false;
        }

        // 检查握手是否成功
        if has_recent_handshake(&iface, &task.pubkey, HANDSHAKE_MAX_AGE_SECS) {
            info!(
                "LAN endpoint confirmed for peer {} after {:.1}s",
                task.pubkey,
                task.start.elapsed().as_secs_f64()
            );
            return false;
        }

        // 超时未成功则回退
        if task.start.elapsed() >= task.timeout {
            warn!("LAN endpoint timeout for peer {}, reverting", task.pubkey);
            if let Some(ref fallback) = task.fallback {
                update_wg_endpoint(&iface, &task.pubkey, fallback);
            }
            return false;
        }

        true // 继续等待
    });
}

// 剩余辅助函数不变...
fn get_wg_listen_port(interface: &str) -> u16 {
    if let Some(p) = env::var("WG_LISTEN_PORT").ok().and_then(|s| s.parse().ok()) {
        return p;
    }
    if let Ok(output) = Command::new(wg_cmd())
        .args(["show", interface, "listen-port"])
        .output()
    {
        if let Ok(stdout) = String::from_utf8(output.stdout) {
            if let Some(p) = stdout.trim().parse().ok() {
                return p;
            }
        }
    }
    DEFAULT_LISTEN_PORT
}

fn collect_my_local_endpoints(interface: &str) -> Vec<String> {
    let port = get_wg_listen_port(interface);
    get_local_lan_networks()
        .iter()
        .filter_map(|net| match net {
            IpNet::V4(v4) => Some(format!("{}:{}", v4.addr(), port)),
            IpNet::V6(v6) => Some(format!("[{}]:{}", v6.addr(), port)),
        })
        .collect()
}

// ---------- 端口更换 ----------
fn has_lan_peer(interface: &str) -> bool {
    let output = match Command::new(wg_cmd())
        .args(["show", interface, "peers"])
        .output()
    {
        Ok(o) => o,
        Err(_) => return false,
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let my_nets = get_local_lan_networks();
    if my_nets.is_empty() {
        return false;
    }
    for pubkey in stdout.lines() {
        let pubkey = pubkey.trim();
        if pubkey.is_empty() {
            continue;
        }
        if let Some(ep) = get_current_endpoint(interface, pubkey) {
            if let Some((ip, _)) = parse_endpoint(&ep) {
                for net in &my_nets {
                    if net.contains(&ip) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn try_change_port(interface: &str, force: bool) {
    let output = match Command::new(wg_cmd())
        .args(["show", interface, "peers"])
        .output()
    {
        Ok(o) => o,
        Err(e) => {
            error!("{}", e);
            return;
        }
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let peers: Vec<&str> = stdout
        .lines()
        .map(|l| l.trim())
        .filter(|l| !l.is_empty())
        .collect();
    if peers.is_empty() {
        return;
    }
    if !force {
        if peers
            .iter()
            .any(|p| has_recent_handshake(interface, p, NO_HANDSHAKE_THRESHOLD))
        {
            return;
        }
        if has_lan_peer(interface) {
            return;
        }
    }
    let now = Instant::now();
    let mut history = PORT_CHANGE_HISTORY.lock().unwrap();
    while history
        .front()
        .map_or(false, |t| now.duration_since(*t) > PORT_CHANGE_LIMIT_WINDOW)
    {
        history.pop_front();
    }
    if history.len() >= MAX_PORT_CHANGES_PER_WINDOW {
        warn!("Port change limit reached");
        return;
    }
    if let Some(last) = history.back() {
        if now.duration_since(*last) < PORT_CHANGE_LIMIT_WINDOW / MAX_PORT_CHANGES_PER_WINDOW as u32
        {
            return;
        }
    }
    let new_port = rand::thread_rng().gen_range(1024..=65535);
    info!("Changing listen port to {} (force={})", new_port, force);
    let out = Command::new(wg_cmd())
        .args(["set", interface, "listen-port", &new_port.to_string()])
        .output();
    match out {
        Ok(o) if o.status.success() => {
            info!("Port changed to {}", new_port);
            history.push_back(now);
        }
        Ok(o) => error!("Failed: {}", String::from_utf8_lossy(&o.stderr)),
        Err(e) => error!("Failed: {}", e),
    }
}

fn check_and_maybe_change_listen_port(interface: &str) {
    try_change_port(interface, false);
}

// ---------- 中继辅助 ----------
fn get_current_allowed_ips(interface: &str, pubkey: &str) -> Result<Vec<String>> {
    let output = Command::new(wg_cmd())
        .args(["show", interface, "peers", pubkey])
        .output()?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if line.contains("allowed ips:") {
            let ips_str = line.split(':').nth(1).unwrap_or("").trim();
            return Ok(ips_str
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect());
        }
    }
    Ok(vec![])
}

fn set_allowed_ips(interface: &str, pubkey: &str, ips: &[String]) -> Result<()> {
    let output = Command::new(wg_cmd())
        .args(&[
            "set",
            interface,
            "peer",
            pubkey,
            "allowed-ips",
            &ips.join(","),
        ])
        .output()?;
    if !output.status.success() {
        bail!(
            "Failed to set allowed-ips for {}: {}",
            pubkey,
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(())
}

fn add_ips_to_peer(interface: &str, pubkey: &str, ips_to_add: &[String]) -> Result<()> {
    let current = get_current_allowed_ips(interface, pubkey)?;
    let mut set: HashSet<String> = current.into_iter().collect();
    for ip in ips_to_add {
        set.insert(ip.clone());
    }
    set_allowed_ips(interface, pubkey, &set.into_iter().collect::<Vec<_>>())
}

fn remove_ips_from_peer(interface: &str, pubkey: &str, ips_to_remove: &[String]) -> Result<()> {
    let current = get_current_allowed_ips(interface, pubkey)?;
    let remove_set: HashSet<&str> = ips_to_remove.iter().map(|s| s.as_str()).collect();
    let new_ips: Vec<String> = current
        .into_iter()
        .filter(|ip| !remove_set.contains(ip.as_str()))
        .collect();
    set_allowed_ips(interface, pubkey, &new_ips)
}

fn get_original_ips_from_snapshot(pubkey: &str) -> Vec<String> {
    LAST_SNAPSHOT_PEERS
        .lock()
        .unwrap()
        .get(pubkey)
        .and_then(|p| p.allowed_ips.clone())
        .unwrap_or_default()
}

fn discover_relay(snapshot: &FullSnapshot, interface: &str) {
    let target_v4 = &RELAY_CIDR_V4;
    let target_v6 = &RELAY_CIDR_V6;
    let mut candidates = Vec::new();
    for (pubkey, peer) in &snapshot.peers {
        if let Some(ips) = &peer.allowed_ips {
            if ips.contains(&target_v4) || ips.contains(&target_v6) {
                if has_recent_handshake(interface, pubkey, RELAY_FAIL_THRESHOLD) {
                    candidates.push(pubkey.clone());
                }
            }
        }
    }
    candidates.sort();
    let count = candidates.len();
    *RELAY_POOL.lock().unwrap() = candidates;
    info!("Relay pool updated: {} candidates", count);
}

fn check_and_apply_relay(wg: &WgInterface, local_pubkey: &str) {
    if LAST_SNAPSHOT_PEERS.lock().unwrap().is_empty() {
        return;
    }
    let pool = RELAY_POOL.lock().unwrap().clone();
    if pool.is_empty() {
        return;
    }

    let handshakes = match get_wg_latest_handshakes(&wg.name) {
        Ok(h) => h,
        Err(e) => {
            warn!("{}", e);
            return;
        }
    };

    for pubkey in handshakes.keys() {
        if pool.contains(pubkey) || pubkey == local_pubkey {
            continue;
        }
        let is_alive = has_recent_handshake(&wg.name, pubkey, RELAY_FAIL_THRESHOLD);
        if !is_alive {
            let action = {
                let mut fail_counts = PEER_FAIL_COUNT.lock().unwrap();
                let relay_load = RELAY_LOAD.lock().unwrap();
                let peer_to_relay = PEER_TO_RELAY.lock().unwrap();
                let count = fail_counts.entry(pubkey.to_string()).or_insert(0);
                *count += 1;
                if *count >= RELAY_FAIL_COUNT_MAX && !peer_to_relay.contains_key(pubkey) {
                    let best = pool
                        .iter()
                        .filter(|pk| has_recent_handshake(&wg.name, pk, RELAY_FAIL_THRESHOLD))
                        .min_by_key(|pk| relay_load.get(*pk).copied().unwrap_or(0))
                        .cloned();
                    if let Some(relay) = best {
                        let original_ips = get_original_ips_from_snapshot(pubkey);
                        if !original_ips.is_empty() {
                            Some((relay, pubkey.clone(), original_ips))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            };
            if let Some((relay, peer, original_ips)) = action {
                if add_ips_to_peer(&wg.name, &relay, &original_ips).is_ok() {
                    let should_commit = {
                        let pt = PEER_TO_RELAY.lock().unwrap();
                        !pt.contains_key(&peer)
                            && has_recent_handshake(&wg.name, &relay, RELAY_FAIL_THRESHOLD)
                    };
                    if should_commit {
                        if wg.remove_peer(&peer).is_ok() {
                            let mut relay_load = RELAY_LOAD.lock().unwrap();
                            let mut peer_to_relay = PEER_TO_RELAY.lock().unwrap();
                            *relay_load.entry(relay.clone()).or_insert(0) += 1;
                            peer_to_relay.insert(peer.clone(), relay.clone());
                            PEER_FAIL_COUNT
                                .lock()
                                .unwrap()
                                .get_mut(&peer)
                                .map(|c| *c = 0);
                            info!("Peer {} -> relay {}", peer, relay);
                        } else {
                            let _ = remove_ips_from_peer(&wg.name, &relay, &original_ips);
                        }
                    } else {
                        let _ = remove_ips_from_peer(&wg.name, &relay, &original_ips);
                    }
                }
            }
        } else {
            let action = {
                let mut peer_to_relay = PEER_TO_RELAY.lock().unwrap();
                if let Some(relay) = peer_to_relay.remove(pubkey) {
                    Some((
                        relay,
                        pubkey.clone(),
                        get_original_ips_from_snapshot(pubkey),
                    ))
                } else {
                    None
                }
            };
            if let Some((relay, peer, original_ips)) = action {
                let _ = remove_ips_from_peer(&wg.name, &relay, &original_ips);
                if PEER_TO_RELAY.lock().unwrap().get(&peer) == Some(&relay) {
                    return;
                }
                if let Some(info) = LAST_SNAPSHOT_PEERS.lock().unwrap().get(&peer).cloned() {
                    let peer_val = json!({"pubkey": peer, "endpoint": info.endpoint, "allowed_ips": info.allowed_ips,
                        "persistent_keepalive": info.persistent_keepalive, "preshared_key": info.preshared_key});
                    if wg.update_peer(&peer_val).is_ok() {
                        RELAY_LOAD
                            .lock()
                            .unwrap()
                            .get_mut(&relay)
                            .map(|l| *l = l.saturating_sub(1));
                        PEER_FAIL_COUNT.lock().unwrap().remove(&peer);
                        info!("Peer {} restored to direct", peer);
                    }
                }
            }
            PEER_FAIL_COUNT
                .lock()
                .unwrap()
                .entry(pubkey.to_string())
                .and_modify(|c| *c = 0);
        }
    }

    for relay in pool.iter() {
        if !has_recent_handshake(&wg.name, relay, RELAY_FAIL_THRESHOLD) {
            let peers_to_migrate = {
                let pt = PEER_TO_RELAY.lock().unwrap();
                pt.iter()
                    .filter(|(_, r)| *r == relay)
                    .map(|(p, _)| (p.clone(), get_original_ips_from_snapshot(p)))
                    .collect::<Vec<_>>()
            };
            if peers_to_migrate.is_empty() {
                RELAY_LOAD.lock().unwrap().remove(relay);
                continue;
            }
            warn!(
                "Relay {} failed, migrating {} peers",
                relay,
                peers_to_migrate.len()
            );
            for (peer, original_ips) in peers_to_migrate {
                let _ = remove_ips_from_peer(&wg.name, relay, &original_ips);
                let new_relay = pool
                    .iter()
                    .filter(|pk| {
                        *pk != relay && has_recent_handshake(&wg.name, pk, RELAY_FAIL_THRESHOLD)
                    })
                    .min_by_key(|pk| RELAY_LOAD.lock().unwrap().get(*pk).copied().unwrap_or(0))
                    .cloned();
                if let Some(target) = new_relay {
                    if add_ips_to_peer(&wg.name, &target, &original_ips).is_ok() {
                        let bind_ok = !PEER_TO_RELAY.lock().unwrap().contains_key(&peer)
                            && has_recent_handshake(&wg.name, &target, RELAY_FAIL_THRESHOLD);
                        if bind_ok {
                            let mut load = RELAY_LOAD.lock().unwrap();
                            *load.entry(target.clone()).or_insert(0) += 1;
                            PEER_TO_RELAY.lock().unwrap().insert(peer, target);
                        } else {
                            let _ = remove_ips_from_peer(&wg.name, &target, &original_ips);
                        }
                    }
                } else {
                    warn!("No healthy relay for {}", peer);
                }
            }
            RELAY_LOAD.lock().unwrap().remove(relay);
        }
    }
}

// ---------- 无psk跳过清除 ----------
fn get_peers_with_psk(interface: &str) -> Result<HashSet<String>> {
    let output = Command::new(wg_cmd())
        .args(["show", interface, "preshared-keys"])
        .output()
        .context("Failed to execute wg show preshared-keys")?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut set = HashSet::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }
        let pubkey = parts[0].to_string();
        if parts.len() >= 2 && parts[1] == "(none)" {
            continue;
        }
        set.insert(pubkey);
    }
    Ok(set)
}

// ---------- 重试队列处理 ----------
fn process_retry_queue(
    _interface: &str,
    retry_queue: &Arc<Mutex<VecDeque<RetryTask>>>,
    _state: &WgState,
    wg: &WgInterface,
) {
    let pending: Vec<RetryTask> = {
        let mut queue = retry_queue.lock().unwrap();
        let now = Instant::now();
        let mut collected = Vec::new();
        while let Some(mut task) = queue.pop_front() {
            if now.duration_since(task.last_attempt) >= task.next_interval() {
                task.last_attempt = now;
                task.retry_count += 1;
                collected.push(task);
            } else {
                queue.push_front(task);
                break;
            }
        }
        collected
    };
    for task in pending {
        let mut json = json!({ "pubkey": task.pubkey });
        // LAN 活跃保护：若当前 peer 有活跃 LAN 连接，保留当前端点
        if let Some(ref ep) = task.endpoint {
            if let Some(current_ep) = get_current_endpoint(&wg.name, &task.pubkey) {
                if is_lan_active(&wg.name, &task.pubkey, &current_ep) {
                    info!(
                        "Retry queue: preserving LAN endpoint {} for peer {}",
                        current_ep, task.pubkey
                    );
                    json["endpoint"] = json!(current_ep);
                } else {
                    json["endpoint"] = json!(ep);
                }
            } else {
                json["endpoint"] = json!(ep);
            }
        }
        if let Some(ref ips) = task.allowed_ips {
            json["allowed_ips"] = json!(ips);
        }
        if let Some(ka) = task.persistent_keepalive {
            json["persistent_keepalive"] = json!(ka);
        }
        if let Some(ref psk) = task.preshared_key {
            if psk.is_empty() {
                json["preshared_key"] = json!("");
            } else {
                json["preshared_key"] = json!(psk);
            }
        }
        match wg.update_peer(&json) {
            Ok(()) => info!("Retry succeeded for peer {}", task.pubkey),
            Err(e) => {
                error!(
                    "Retry {} failed for peer {}: {}",
                    task.retry_count, task.pubkey, e
                );
                if task.retry_count < DEFAULT_MAX_RETRY_ATTEMPTS {
                    retry_queue.lock().unwrap().push_back(task);
                }
            }
        }
    }
}

// ---------- 全量快照处理 ----------
fn handle_full_snapshot(
    wg: &mut WgInterface,
    local_pubkey: &str,
    payload: &[u8],
    _client: &Client,
    _request_topic: &str,
) -> Result<()> {
    let hash = blake3::hash(payload).to_hex().to_string();
    {
        let mut last_hash = LAST_FULL_HASH.lock().unwrap();
        if let Some(ref prev) = *last_hash {
            if *prev == hash {
                return Ok(());
            }
        }
        *last_hash = Some(hash);
    }
    let decompressed =
        zstd::decode_all(payload).or_else(|_| Ok::<Vec<u8>, anyhow::Error>(payload.to_vec()))?;
    let snapshot: FullSnapshot = serde_json::from_slice(&decompressed)?;
    info!("Received full snapshot: {} peers", snapshot.peers.len());

    let self_in_snapshot = snapshot.peers.contains_key(local_pubkey);
    let min_peers = 2;
    if !self_in_snapshot || snapshot.peers.len() < min_peers {
        warn!(
            "Incomplete snapshot (peers: {}, self_present: {}), ignoring.",
            snapshot.peers.len(),
            self_in_snapshot
        );
        *LAST_SNAPSHOT_PEERS.lock().unwrap() = snapshot.peers.clone();
        return Ok(());
    }

    *REGISTRATION_STATE.lock().unwrap() = RegistrationState::Registered;
    discover_relay(&snapshot, &wg.name);

    if let Some(self_peer) = snapshot.peers.get(local_pubkey) {
        if let Some(ips) = &self_peer.allowed_ips {
            let (ipv4, ipv6) = extract_self_ips(ips);
            if !ipv4.is_empty() || !ipv6.is_empty() {
                configure_self_ip(&wg.name, &ipv4, &ipv6);
            }
        }
    }

    if wg_cmd() == "awg.exe" {
        if let Some(ref amnezia) = snapshot.amnezia {
            let _ = apply_amnezia_config(&wg.name, amnezia);
        }
    }

    if !SELF_IP_CONFIGURED.load(Ordering::Relaxed) {
        if let Some(self_peer) = snapshot.peers.get(local_pubkey) {
            if let Some(ips) = &self_peer.allowed_ips {
                let mut my_ipv4 = String::new();
                let mut my_ipv6 = String::new();
                for ip in ips {
                    if my_ipv4.is_empty() && ip.contains('.') {
                        my_ipv4 = ip.clone();
                    } else if my_ipv6.is_empty() && ip.contains(':') {
                        my_ipv6 = ip.clone();
                    }
                }
                if !my_ipv4.is_empty() || !my_ipv6.is_empty() {
                    let all_peers = snapshot.peers.iter().map(|(k, v)| (k.clone(), json!({
                        "endpoint": v.endpoint, "allowed_ips": v.allowed_ips,
                        "persistent_keepalive": v.persistent_keepalive, "preshared_key": v.preshared_key,
                        "local_ips": v.local_ips
                    }))).collect();
                    wg.install_with_config(&my_ipv4, &my_ipv6, &all_peers)?;
                    SELF_IP_CONFIGURED.store(true, Ordering::Relaxed);
                    if let Err(e) = apply_advertised_routes(&wg.name, &snapshot.routes) {
                        error!("Routes: {}", e);
                    }
                }
            }
        }
    } else {
        // 获取当前已配置 PSK 的 peer 集合（用于跳过无意义的清除）
        let peers_with_psk = get_peers_with_psk(&wg.name).unwrap_or_else(|e| {
            warn!("Failed to query PSK status: {}", e);
            HashSet::new()
        });
        let force_clear = peers_with_psk.is_empty(); // 查询失败时保守清除所有

        let peer_to_relay = PEER_TO_RELAY.lock().unwrap();
        for (pubkey, peer_info) in &snapshot.peers {
            if pubkey == local_pubkey || peer_to_relay.contains_key(pubkey) {
                continue;
            }

            // 保护 allowed_ips：若快照中为空，尝试从当前 wg 接口获取旧值
            let effective_allowed_ips: Option<Vec<String>> = match &peer_info.allowed_ips {
                Some(ips) if !ips.is_empty() => Some(ips.clone()),
                _ => match get_current_allowed_ips(&wg.name, pubkey) {
                    Ok(current) if !current.is_empty() => {
                        warn!(
                            "Snapshot has empty allowed_ips for peer {}, keeping wg current",
                            pubkey
                        );
                        Some(current)
                    }
                    _ => {
                        warn!(
                            "Peer {} has no allowed_ips in snapshot and wg, skipping update",
                            pubkey
                        );
                        continue;
                    }
                },
            };

            // PSK 清除优化：若快照要求清除 PSK，但当前 peer 没有 PSK，则跳过
            if peer_info.preshared_key.as_deref() == Some("") {
                if !force_clear && !peers_with_psk.contains(pubkey.as_str()) {
                    debug!("Skipping PSK clear for peer {}: no PSK present", pubkey);
                    // 仍然需要更新其他字段（如 endpoint），但不执行清除操作
                    let peer_val = json!({
                        "pubkey": pubkey,
                        "endpoint": peer_info.endpoint,
                        "allowed_ips": effective_allowed_ips,
                        "persistent_keepalive": peer_info.persistent_keepalive,
                        "preshared_key": serde_json::Value::Null, // 不设置 PSK
                        "local_ips": peer_info.local_ips,
                    });
                    if let Err(e) = wg.update_peer(&peer_val) {
                        error!("Update {}: {}", pubkey, e);
                    }
                } else {
                    // 需要清除 PSK
                    let peer_val = json!({
                        "pubkey": pubkey,
                        "endpoint": peer_info.endpoint,
                        "allowed_ips": effective_allowed_ips,
                        "persistent_keepalive": peer_info.persistent_keepalive,
                        "preshared_key": "",
                        "local_ips": peer_info.local_ips,
                    });
                    if let Err(e) = wg.update_peer(&peer_val) {
                        error!("Update {}: {}", pubkey, e);
                    }
                }
            } else {
                // 非清除 PSK 的情况
                let mut peer_val = json!({
                    "pubkey": pubkey,
                    "endpoint": peer_info.endpoint,
                    "allowed_ips": effective_allowed_ips,
                    "persistent_keepalive": peer_info.persistent_keepalive,
                    "preshared_key": peer_info.preshared_key,
                    "local_ips": peer_info.local_ips,
                });

                // LAN 活跃保护：若当前 peer 有活跃 LAN 连接，保留其端点，不更新为快照中的公网端点
                if is_lan_switching_enabled() {
                    if let Some(ref current_ep) = get_current_endpoint(&wg.name, pubkey) {
                        if is_lan_active(&wg.name, pubkey, current_ep) {
                            info!(
                                "LAN active for peer {}, preserving LAN endpoint {} over snapshot endpoint {:?}",
                                pubkey, current_ep, peer_info.endpoint
                            );
                            peer_val["endpoint"] = json!(current_ep);
                        }
                    }
                }

                if let Err(e) = wg.update_peer(&peer_val) {
                    error!("Update {}: {}", pubkey, e);
                }
            }

            if let Some(local_ips) = &peer_info.local_ips {
                if !local_ips.is_empty() {
                    try_switch_to_lan_endpoint(wg.name.clone(), pubkey.clone(), local_ips.clone());
                }
            }
        }
        drop(peer_to_relay);

        if let Ok(output) = Command::new(wg_cmd())
            .args(["show", &wg.name, "peers"])
            .output()
        {
            let stdout = String::from_utf8_lossy(&output.stdout);
            for pubkey in stdout.lines().map(|l| l.trim()).filter(|l| !l.is_empty()) {
                if pubkey != local_pubkey && !snapshot.peers.contains_key(pubkey) {
                    let _ = wg.remove_peer(pubkey);
                    let mut pt = PEER_TO_RELAY.lock().unwrap();
                    if let Some(relay) = pt.remove(pubkey) {
                        RELAY_LOAD
                            .lock()
                            .unwrap()
                            .get_mut(&relay)
                            .map(|l| *l = l.saturating_sub(1));
                        PEER_FAIL_COUNT.lock().unwrap().remove(pubkey);
                    }
                }
            }
        }
        if let Err(e) = apply_advertised_routes(&wg.name, &snapshot.routes) {
            error!("Routes: {}", e);
        }
    }

    *LAST_SNAPSHOT_PEERS.lock().unwrap() = snapshot.peers.clone();
    Ok(())
}

// ---------- 增量消息处理 ----------
fn handle_delta_message(wg: &mut WgInterface, local_pubkey: &str, payload: &[u8]) -> Result<()> {
    let json: serde_json::Value = serde_json::from_slice(payload)?;
    let action = json
        .get("action")
        .and_then(|v| v.as_str())
        .context("Missing action")?;
    let pubkey = json
        .get("pubkey")
        .and_then(|v| v.as_str())
        .context("Missing pubkey")?;
    if pubkey == local_pubkey {
        return Ok(());
    }
    if !SELF_IP_CONFIGURED.load(Ordering::Relaxed) {
        return Ok(());
    }

    match action {
        "add" | "update" => {
            // LAN 活跃保护：如果当前 peer 已有活跃 LAN 连接，则忽略新 WAN 端点
            if is_lan_switching_enabled() {
                if let Some(new_ep) = json.get("endpoint").and_then(|v| v.as_str()) {
                    if let Some(current_ep) = get_current_endpoint(&wg.name, pubkey) {
                        if is_lan_active(&wg.name, pubkey, &current_ep) {
                            info!(
                                "LAN switching enabled: peer {} is using LAN endpoint {}, ignoring WAN endpoint update {}",
                                pubkey, current_ep, new_ep
                            );
                            // 仍然需要更新其他字段，但保持当前端点
                            let mut peer_val = json.clone();
                            if let Some(obj) = peer_val.as_object_mut() {
                                obj.insert("endpoint".to_string(), json!(current_ep));
                            }
                            if let Err(e) = wg.update_peer(&peer_val) {
                                error!("Update {}: {}", pubkey, e);
                            }
                            if let Some(local_ips) =
                                json.get("local_ips").and_then(|v| v.as_array())
                            {
                                let ips: Vec<String> = local_ips
                                    .iter()
                                    .filter_map(|v| v.as_str().map(String::from))
                                    .collect();
                                if !ips.is_empty() {
                                    try_switch_to_lan_endpoint(
                                        wg.name.clone(),
                                        pubkey.to_string(),
                                        ips,
                                    );
                                }
                            }
                            return Ok(());
                        }
                    }
                }
            }

            if let Some(new_ep) = json.get("endpoint").and_then(|v| v.as_str()) {
                let fallback = get_current_endpoint(&wg.name, pubkey);
                wg.update_peer(&json)?;
                update_endpoint_with_fallback(&wg.name, pubkey, new_ep, fallback);
            } else {
                wg.update_peer(&json)?;
            }
            if let Some(local_ips) = json.get("local_ips").and_then(|v| v.as_array()) {
                let ips: Vec<String> = local_ips
                    .iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect();
                if !ips.is_empty() {
                    try_switch_to_lan_endpoint(wg.name.clone(), pubkey.to_string(), ips);
                }
            }
        }
        "remove" => {
            wg.remove_peer(pubkey)?;
            let mut pt = PEER_TO_RELAY.lock().unwrap();
            if let Some(relay) = pt.remove(pubkey) {
                RELAY_LOAD
                    .lock()
                    .unwrap()
                    .get_mut(&relay)
                    .map(|l| *l = l.saturating_sub(1));
                PEER_FAIL_COUNT.lock().unwrap().remove(pubkey);
            }
        }
        _ => {}
    }
    Ok(())
}

// ---------- 注册管理 ----------
fn start_registration(
    client: &Client,
    register_topic: &str,
    _request_topic: &str,
    register_payload: &serde_json::Value,
) {
    let payload_str = register_payload.to_string();
    info!("Sending registration request to {}", register_topic);
    for attempt in 1..=REGISTER_MAX_RETRIES {
        match client.publish(
            register_topic,
            QoS::AtLeastOnce,
            false,
            payload_str.as_bytes(),
        ) {
            Ok(_) => {
                info!("Register message published (attempt {})", attempt);
                *REGISTRATION_STATE.lock().unwrap() = RegistrationState::InProgress;
                return;
            }
            Err(e) => {
                error!("Failed to publish register (attempt {}): {}", attempt, e);
                if attempt < REGISTER_MAX_RETRIES {
                    thread::sleep(REGISTER_RETRY_INTERVAL);
                }
            }
        }
    }
    error!("All registration attempts failed");
}

fn flush_connection(connection: &mut Connection) {
    for _ in 0..3 {
        match connection.recv_timeout(Duration::from_millis(50)) {
            Ok(_) | Err(RecvTimeoutError::Timeout) => {}
            Err(RecvTimeoutError::Disconnected) => break,
        }
    }
}

// ---------- 流量上报 ----------
fn try_report_traffic(
    client: &Client,
    interface: &str,
    local_pubkey: &str,
    state: &WgState,
) -> Result<()> {
    let increments = {
        let mut snapshot = TRAFFIC_SNAPSHOT.lock().unwrap();
        let mut increments = HashMap::new();
        for (pubkey, peer) in &state.peers {
            let cur_rx = peer.transfer_rx;
            let cur_tx = peer.transfer_tx;
            let (delta_rx, delta_tx) = if let Some(&(last_rx, last_tx)) = snapshot.get(pubkey) {
                (
                    if cur_rx >= last_rx {
                        cur_rx - last_rx
                    } else {
                        cur_rx
                    },
                    if cur_tx >= last_tx {
                        cur_tx - last_tx
                    } else {
                        cur_tx
                    },
                )
            } else {
                (cur_rx, cur_tx)
            };
            snapshot.insert(pubkey.clone(), (cur_rx, cur_tx));
            if delta_rx > 0 || delta_tx > 0 {
                increments.insert(pubkey.clone(), (delta_rx, delta_tx));
            }
        }
        snapshot.retain(|pk, _| state.peers.contains_key(pk));
        increments
    };
    let now_secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let peers: Vec<serde_json::Value> = state.peers.iter().filter_map(|(pubkey, peer)| {
        let (delta_rx, delta_tx) = increments.get(pubkey).copied().unwrap_or((0, 0));
        if peer.transfer_rx == 0 && peer.transfer_tx == 0 && delta_rx == 0 && delta_tx == 0 { return None; }
        Some(json!({"pubkey": pubkey, "rx_bytes": delta_rx, "tx_bytes": delta_tx, "rx_total": peer.transfer_rx, "tx_total": peer.transfer_tx}))
    }).collect();
    if peers.is_empty() {
        return Ok(());
    }
    let payload = json!({"timestamp": now_secs, "node": local_pubkey, "peers": peers});
    let topic = format!("wg/{}/traffic", interface);
    let _ = client.publish(
        &topic,
        QoS::AtLeastOnce,
        false,
        payload.to_string().as_bytes(),
    );
    info!(
        "Traffic report published to {} ({} peers)",
        topic,
        peers.len()
    );
    Ok(())
}

fn get_wg_state(interface: &str) -> Result<WgState> {
    let output = Command::new(wg_cmd())
        .args(["show", interface, "dump"])
        .output()
        .context("Failed to execute wg show dump")?;
    if !output.status.success() {
        bail!(
            "wg show dump failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let stdout = String::from_utf8(output.stdout).context("Dump output is not valid UTF-8")?;
    let mut state = WgState::default();
    let mut lines = stdout.lines();
    if let Some(iface_line) = lines.next() {
        let parts: Vec<&str> = iface_line.split('\t').collect();
        if parts.len() >= 3 {
            state.listen_port = parts[2].parse().unwrap_or(DEFAULT_LISTEN_PORT);
        }
    }
    for line in lines {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() < 8 {
            continue;
        }
        let pubkey = parts[0].to_string();
        let endpoint = if parts[2] == "(none)" || parts[2].is_empty() {
            None
        } else {
            Some(parts[2].to_string())
        };
        let allowed_ips: Vec<String> = parts[3]
            .split(',')
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect();
        let latest_handshake = if parts[4] == "0" {
            None
        } else {
            parts[4].parse::<u64>().ok()
        };
        let transfer_rx = parts[5].parse::<u64>().unwrap_or(0);
        let transfer_tx = parts[6].parse::<u64>().unwrap_or(0);
        state.peers.insert(
            pubkey,
            PeerState {
                endpoint,
                allowed_ips,
                latest_handshake,
                transfer_rx,
                transfer_tx,
            },
        );
    }
    Ok(state)
}

// ---------- 主函数 ----------
fn main() -> Result<()> {
    env_logger::init();
    let wg_interface = env::var("WG_INTERFACE")
        .unwrap_or_else(|_| "wg0".to_string())
        .trim()
        .to_string();
    let mqtt_host = env::var("MQTT_HOST").context("MQTT_HOST must be set")?;
    let mqtt_port = env::var("MQTT_PORT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1883);
    let mqtt_user = env::var("MQTT_USER").ok();
    let mqtt_pass = env::var("MQTT_PASS").ok();

    let enable_port_change = env::var("ENABLE_PORT_CHANGE_ON_NETWORK_LOSS")
        .map(|v| v == "1" || v.to_lowercase() == "true")
        .unwrap_or(false);
    let enable_scheduled = env::var("ENABLE_SCHEDULED_PORT_CHANGE")
        .map(|v| v == "1" || v.to_lowercase() == "true")
        .unwrap_or(false);
    let scheduled_interval = Duration::from_secs(
        env::var("SCHEDULED_PORT_CHANGE_INTERVAL")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(7200),
    );
    let enable_traffic_report = env::var("ENABLE_TRAFFIC_REPORT")
        .map(|v| v == "1" || v.to_lowercase() == "true")
        .unwrap_or(false);

    let keys = load_or_generate_keys()?;
    info!("Local public key: {}", keys.public_key);
    let mut wg = WgInterface::new(&wg_interface, &keys)?;
    let client_id = format!(
        "wg-{}",
        &blake3::hash(keys.public_key.as_bytes()).to_hex()[..20]
    );

    let full_topic = format!("wg/{}/full", wg_interface);
    let delta_topic = format!("wg/{}/delta", wg_interface);
    let response_topic = format!("wg/{}/full/response/{}", wg_interface, client_id);
    let register_topic = format!("wg/{}/register", wg_interface);
    let request_topic = format!("wg/{}/full/request/{}", wg_interface, client_id);
    let config_update_topic = format!("wg/{}/config/update", wg_interface);

    let running = Arc::new(AtomicBool::new(true));
    let r = running.clone();
    ctrlc::set_handler(move || {
        r.store(false, Ordering::Relaxed);
    })?;

    let hostname = hostname::get()
        .map(|h| h.to_string_lossy().to_string())
        .unwrap_or_else(|_| "unknown".to_string());
    let my_local_endpoints = collect_my_local_endpoints(&wg_interface);
    let register_payload =
        json!({"pubkey": keys.public_key, "hostname": hostname, "local_ips": my_local_endpoints});

    let re_register_interval = env::var("RE_REGISTER_INTERVAL")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(600);
    let mut register_retry = RegisterRetry::new(re_register_interval);
    let mut last_network_check = Instant::now();
    let mut last_scheduled_change = Instant::now();
    let mut last_traffic_report = if enable_traffic_report {
        Some(Instant::now())
    } else {
        None
    };
    let mut last_retry_process = Instant::now();
    let mut last_lan_check = Instant::now();
    let mut traffic_state_cache: Option<(Instant, WgState)> = None;

    let retry_queue = Arc::new(Mutex::new(VecDeque::<RetryTask>::new()));

    if let Some(self_ips) = load_self_ips() {
        info!(
            "Found cached self IPs: {} / {}",
            self_ips.ipv4, self_ips.ipv6
        );
    }

    let mut retry_delay = Duration::from_secs(1);
    while running.load(Ordering::Relaxed) {
        match create_mqtt_connection(
            &mqtt_host,
            mqtt_port,
            mqtt_user.as_deref(),
            mqtt_pass.as_deref(),
            &client_id,
        ) {
            Ok((client, mut connection)) => {
                info!("MQTT TCP connection established, waiting for CONNACK...");
                let mut conn_ack_success = false;
                loop {
                    match connection.recv_timeout(Duration::from_secs(10)) {
                        Ok(Ok(Event::Incoming(Incoming::ConnAck(ack)))) => {
                            if ack.code == ConnectReturnCode::Success {
                                info!("MQTT connection acknowledged");
                                conn_ack_success = true;
                                break;
                            } else {
                                error!("MQTT connection refused: {:?}", ack.code);
                                break;
                            }
                        }
                        Ok(Ok(_)) => continue,
                        Ok(Err(e)) => {
                            error!("MQTT connection error: {}", e);
                            break;
                        }
                        Err(RecvTimeoutError::Timeout) => {
                            error!("Timeout waiting for CONNACK");
                            break;
                        }
                        Err(RecvTimeoutError::Disconnected) => {
                            error!("Disconnected while waiting for CONNACK");
                            break;
                        }
                    }
                }

                if conn_ack_success {
                    for topic in &[
                        &full_topic,
                        &delta_topic,
                        &response_topic,
                        &config_update_topic,
                    ] {
                        let _ = client.subscribe(*topic, QoS::AtLeastOnce);
                    }
                    thread::sleep(Duration::from_millis(200));
                    start_registration(&client, &register_topic, &request_topic, &register_payload);
                    flush_connection(&mut connection);
                    register_retry.force_next();

                    while running.load(Ordering::Relaxed) {
                        let need_retry = {
                            let state = REGISTRATION_STATE.lock().unwrap();
                            !matches!(*state, RegistrationState::Registered)
                                && register_retry.should_retry()
                        };
                        if need_retry {
                            warn!("Still not registered, retrying...");
                            start_registration(
                                &client,
                                &register_topic,
                                &request_topic,
                                &register_payload,
                            );
                            flush_connection(&mut connection);
                        }

                        // LAN 验证任务扫描 (每秒一次)
                        if last_lan_check.elapsed() >= LAN_CHECK_INTERVAL {
                            process_lan_verification_tasks();
                            last_lan_check = Instant::now();
                        }

                        if last_retry_process.elapsed() >= RETRY_PROCESS_INTERVAL {
                            if let Ok(state) = get_wg_state(&wg.name) {
                                process_retry_queue(&wg.name, &retry_queue, &state, &wg);
                            }
                            last_retry_process = Instant::now();
                        }

                        if last_network_check.elapsed() >= NETWORK_CHECK_INTERVAL {
                            if enable_port_change && SELF_IP_CONFIGURED.load(Ordering::Relaxed) {
                                check_and_maybe_change_listen_port(&wg.name);
                            }
                            if SELF_IP_CONFIGURED.load(Ordering::Relaxed) {
                                check_and_apply_relay(&wg, &keys.public_key);
                            }
                            last_network_check = Instant::now();
                        }

                        if enable_scheduled
                            && SELF_IP_CONFIGURED.load(Ordering::Relaxed)
                            && last_scheduled_change.elapsed() >= scheduled_interval
                        {
                            try_change_port(&wg.name, true);
                            last_scheduled_change = Instant::now();
                        }

                        if let Some(ref mut last) = last_traffic_report {
                            if last.elapsed() >= TRAFFIC_REPORT_INTERVAL {
                                let state = match traffic_state_cache {
                                    Some((ts, ref state))
                                        if ts.elapsed() < Duration::from_secs(5) =>
                                    {
                                        state.clone()
                                    }
                                    _ => match get_wg_state(&wg.name) {
                                        Ok(s) => {
                                            traffic_state_cache = Some((Instant::now(), s.clone()));
                                            s
                                        }
                                        Err(e) => {
                                            error!("Failed to get wg state for traffic: {}", e);
                                            *last = Instant::now();
                                            continue;
                                        }
                                    },
                                };
                                if let Err(e) =
                                    try_report_traffic(&client, &wg.name, &keys.public_key, &state)
                                {
                                    error!("Traffic report: {}", e);
                                }
                                *last = Instant::now();
                            }
                        }

                        match connection.recv_timeout(Duration::from_secs(1)) {
                            Ok(notification) => {
                                if let Ok(event) = notification {
                                    if let Event::Incoming(Incoming::Publish(publish)) = event {
                                        let topic = publish.topic;
                                        let payload = publish.payload;
                                        if topic == config_update_topic {
                                            continue;
                                        }
                                        let result =
                                            if topic == full_topic || topic == response_topic {
                                                handle_full_snapshot(
                                                    &mut wg,
                                                    &keys.public_key,
                                                    &payload,
                                                    &client,
                                                    &request_topic,
                                                )
                                            } else if topic == delta_topic {
                                                handle_delta_message(
                                                    &mut wg,
                                                    &keys.public_key,
                                                    &payload,
                                                )
                                            } else {
                                                continue;
                                            };
                                        if let Err(e) = result {
                                            error!("{}", e);
                                        }
                                    }
                                }
                            }
                            Err(RecvTimeoutError::Timeout) => {}
                            Err(RecvTimeoutError::Disconnected) => {
                                warn!("MQTT disconnected");
                                break;
                            }
                        }
                    }
                }
            }
            Err(e) => {
                error!("Failed to connect to MQTT: {}", e);
            }
        }
        if running.load(Ordering::Relaxed) {
            warn!("Reconnecting in {} seconds...", retry_delay.as_secs());
            thread::sleep(retry_delay);
            retry_delay = std::cmp::min(retry_delay * 2, Duration::from_secs(60));
        }
    }

    info!("Goodbye (interface and peers left untouched)");
    Ok(())
}
