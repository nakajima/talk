use std::{
    collections::BTreeMap,
    env, fs,
    io::{self, Read, Write},
    net::{TcpListener, TcpStream},
    path::{Path, PathBuf},
    process::Command,
    thread,
    time::{Duration, SystemTime},
};

use crate::SiteBuilder;

const DEFAULT_PORT: u16 = 8000;
const POLL_INTERVAL: Duration = Duration::from_millis(350);
const MAX_REQUEST_BYTES: usize = 16 * 1024;
const CROSS_ORIGIN_ISOLATION_HEADERS: &str = "Cross-Origin-Opener-Policy: same-origin\r\nCross-Origin-Embedder-Policy: require-corp\r\nCross-Origin-Resource-Policy: same-origin\r\n";

pub(crate) struct DevServer {
    assets: PathBuf,
    builder: SiteBuilder,
    executable: PathBuf,
    listener: TcpListener,
    sources: SourceState,
}

impl DevServer {
    pub(crate) fn new(builder: SiteBuilder) -> io::Result<Self> {
        let port = match env::var("PORT") {
            Ok(value) => value.parse::<u16>().map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("PORT must be a number between 0 and 65535, got {value:?}"),
                )
            })?,
            Err(env::VarError::NotPresent) => DEFAULT_PORT,
            Err(error) => return Err(io::Error::new(io::ErrorKind::InvalidInput, error)),
        };
        let assets = PathBuf::from("./assets");
        builder.write_all(&assets)?;

        let listener = TcpListener::bind(("0.0.0.0", port))?;
        listener.set_nonblocking(true)?;

        Ok(Self {
            assets,
            builder,
            executable: env::current_exe()?,
            listener,
            sources: SourceState::capture(),
        })
    }

    pub(crate) fn run(mut self) -> io::Result<()> {
        let address = self.listener.local_addr()?;
        println!("serving http://localhost:{}", address.port());

        loop {
            self.accept_connections()?;
            thread::sleep(POLL_INTERVAL);
            self.rebuild_if_needed()?;
        }
    }

    fn accept_connections(&self) -> io::Result<()> {
        loop {
            match self.listener.accept() {
                Ok((stream, _)) => {
                    let assets = self.assets.clone();
                    thread::spawn(move || {
                        if let Err(error) = Connection::new(stream, assets).serve() {
                            eprintln!("request failed: {error}");
                        }
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(()),
                Err(error) => return Err(error),
            }
        }
    }

    fn rebuild_if_needed(&mut self) -> io::Result<()> {
        let current = SourceState::capture();
        let executable_changed = current.executable != self.sources.executable;
        let site_changed = current.site != self.sources.site;
        self.sources = current;

        if executable_changed {
            println!("server source changed; rebuilding");
            let status = Command::new("cargo")
                .args(["build", "--package", "builder"])
                .status()?;
            if status.success() {
                return self.restart();
            }
            eprintln!("server rebuild failed; keeping the current process running");
        } else if site_changed {
            println!("site source changed; rebuilding pages");
            match std::panic::catch_unwind(|| self.builder.write_all(&self.assets)) {
                Ok(Ok(())) => println!("rebuilt pages"),
                Ok(Err(error)) => eprintln!("site rebuild failed: {error}"),
                Err(_) => eprintln!("site rebuild failed; keeping the previous pages"),
            }
        }

        Ok(())
    }

    #[cfg(unix)]
    fn restart(&mut self) -> io::Result<()> {
        use std::os::unix::process::CommandExt;

        let error = Command::new(&self.executable).arg("dev").exec();
        Err(error)
    }

    #[cfg(not(unix))]
    fn restart(&mut self) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "automatic server restart is only supported on Unix",
        ))
    }
}

#[derive(Eq, PartialEq)]
struct SourceState {
    executable: BTreeMap<PathBuf, FileStamp>,
    site: BTreeMap<PathBuf, FileStamp>,
}

impl SourceState {
    fn capture() -> Self {
        let mut executable = BTreeMap::new();
        FileStamp::collect(Path::new("./src"), &mut executable);
        FileStamp::collect(Path::new("./Cargo.toml"), &mut executable);

        let mut site = BTreeMap::new();
        FileStamp::collect(Path::new("./content"), &mut site);
        FileStamp::collect(Path::new("./manual"), &mut site);

        Self { executable, site }
    }
}

#[derive(Eq, PartialEq)]
struct FileStamp {
    length: u64,
    modified: Option<SystemTime>,
}

impl FileStamp {
    fn collect(path: &Path, files: &mut BTreeMap<PathBuf, Self>) {
        let Ok(metadata) = fs::metadata(path) else {
            return;
        };
        if metadata.is_file() {
            files.insert(
                path.to_path_buf(),
                Self {
                    length: metadata.len(),
                    modified: metadata.modified().ok(),
                },
            );
            return;
        }
        if !metadata.is_dir() {
            return;
        }

        let Ok(entries) = fs::read_dir(path) else {
            return;
        };
        for entry in entries.flatten() {
            Self::collect(&entry.path(), files);
        }
    }
}

struct Connection {
    stream: TcpStream,
    assets: PathBuf,
}

impl Connection {
    fn new(stream: TcpStream, assets: PathBuf) -> Self {
        Self { stream, assets }
    }

    fn serve(mut self) -> io::Result<()> {
        self.stream.set_read_timeout(Some(Duration::from_secs(2)))?;
        let request = match HttpRequest::read_from(&mut self.stream) {
            Ok(request) => request,
            Err(error) => {
                return self.respond(
                    "400 Bad Request",
                    "text/plain; charset=utf-8",
                    error.to_string().into_bytes(),
                    false,
                );
            }
        };

        if request.method != "GET" && request.method != "HEAD" {
            return self.respond(
                "405 Method Not Allowed",
                "text/plain; charset=utf-8",
                b"method not allowed\n".to_vec(),
                request.method == "HEAD",
            );
        }

        let Some(asset_path) = AssetPath::from_target(&request.target) else {
            return self.respond(
                "400 Bad Request",
                "text/plain; charset=utf-8",
                b"invalid path\n".to_vec(),
                request.method == "HEAD",
            );
        };
        let Some(path) = asset_path.resolve_in(&self.assets) else {
            return self.respond(
                "404 Not Found",
                "text/plain; charset=utf-8",
                b"not found\n".to_vec(),
                request.method == "HEAD",
            );
        };

        let content_type = AssetPath::content_type(&path);
        let body = fs::read(path)?;
        self.respond("200 OK", content_type, body, request.method == "HEAD")
    }

    fn respond(
        &mut self,
        status: &str,
        content_type: &str,
        body: Vec<u8>,
        head_only: bool,
    ) -> io::Result<()> {
        write!(
            self.stream,
            "HTTP/1.1 {status}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nCache-Control: no-store\r\n{CROSS_ORIGIN_ISOLATION_HEADERS}Connection: close\r\n\r\n",
            body.len()
        )?;
        if !head_only {
            self.stream.write_all(&body)?;
        }
        self.stream.flush()
    }
}

struct HttpRequest {
    method: String,
    target: String,
}

impl HttpRequest {
    fn read_from(stream: &mut TcpStream) -> io::Result<Self> {
        let mut bytes = Vec::new();
        let mut buffer = [0_u8; 1024];
        while !bytes.windows(4).any(|window| window == b"\r\n\r\n") {
            let count = stream.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            bytes.extend_from_slice(&buffer[..count]);
            if bytes.len() > MAX_REQUEST_BYTES {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "request headers are too large",
                ));
            }
        }

        let request = str::from_utf8(&bytes)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "request is not UTF-8"))?;
        let line = request
            .lines()
            .next()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing request line"))?;
        let mut parts = line.split_whitespace();
        let method = parts.next();
        let target = parts.next();
        let version = parts.next();
        if method.is_none() || target.is_none() || version.is_none() || parts.next().is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid request line",
            ));
        }

        Ok(Self {
            method: method.unwrap().to_string(),
            target: target.unwrap().to_string(),
        })
    }
}

struct AssetPath {
    relative: PathBuf,
    directory_request: bool,
}

impl AssetPath {
    fn from_target(target: &str) -> Option<Self> {
        let encoded = target.split('?').next()?;
        if !encoded.starts_with('/') {
            return None;
        }
        let decoded = Self::percent_decode(encoded)?;
        if decoded.contains('\\') || decoded.contains('\0') {
            return None;
        }

        let mut relative = PathBuf::new();
        for segment in decoded.trim_start_matches('/').split('/') {
            match segment {
                "" | "." => {}
                ".." => return None,
                segment => relative.push(segment),
            }
        }

        Some(Self {
            relative,
            directory_request: decoded.ends_with('/'),
        })
    }

    fn resolve_in(&self, root: &Path) -> Option<PathBuf> {
        if self.relative.as_os_str().is_empty() {
            return Self::existing_file(root.join("index.html"));
        }

        let direct = root.join(&self.relative);
        if let Some(path) = Self::existing_file(direct.clone()) {
            return Some(path);
        }
        if !self.directory_request {
            let html = root.join(format!("{}.html", self.relative.to_string_lossy()));
            if let Some(path) = Self::existing_file(html) {
                return Some(path);
            }
        }
        Self::existing_file(direct.join("index.html"))
    }

    fn existing_file(path: PathBuf) -> Option<PathBuf> {
        path.is_file().then_some(path)
    }

    fn percent_decode(value: &str) -> Option<String> {
        let bytes = value.as_bytes();
        let mut decoded = Vec::with_capacity(bytes.len());
        let mut index = 0;
        while index < bytes.len() {
            if bytes[index] == b'%' {
                let high = *bytes.get(index + 1)?;
                let low = *bytes.get(index + 2)?;
                decoded.push((Self::hex(high)? << 4) | Self::hex(low)?);
                index += 3;
            } else {
                decoded.push(bytes[index]);
                index += 1;
            }
        }
        String::from_utf8(decoded).ok()
    }

    fn hex(byte: u8) -> Option<u8> {
        match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            b'A'..=b'F' => Some(byte - b'A' + 10),
            _ => None,
        }
    }

    fn content_type(path: &Path) -> &'static str {
        match path.extension().and_then(|extension| extension.to_str()) {
            Some("html") => "text/html; charset=utf-8",
            Some("css") => "text/css; charset=utf-8",
            Some("js") | Some("mjs") => "text/javascript; charset=utf-8",
            Some("json") | Some("map") => "application/json; charset=utf-8",
            Some("svg") => "image/svg+xml",
            Some("png") => "image/png",
            Some("jpg") | Some("jpeg") => "image/jpeg",
            Some("gif") => "image/gif",
            Some("webp") => "image/webp",
            Some("woff") => "font/woff",
            Some("woff2") => "font/woff2",
            Some("wasm") => "application/wasm",
            _ => "application/octet-stream",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::AssetPath;
    use std::{fs, path::Path};

    #[test]
    fn rejects_traversal_paths() {
        assert!(AssetPath::from_target("/../Cargo.toml").is_none());
        assert!(AssetPath::from_target("/%2e%2e/Cargo.toml").is_none());
        assert!(AssetPath::from_target("/..%2fCargo.toml").is_none());
    }

    #[test]
    fn resolves_extensionless_html_paths() {
        let root =
            std::env::temp_dir().join(format!("talktalk-builder-test-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("nested")).unwrap();
        fs::write(root.join("playground.html"), "play").unwrap();
        fs::write(root.join("nested/index.html"), "nested").unwrap();

        let playground = AssetPath::from_target("/playground").unwrap();
        assert_eq!(
            playground.resolve_in(&root).as_deref(),
            Some(root.join("playground.html").as_path())
        );
        let nested = AssetPath::from_target("/nested/").unwrap();
        assert_eq!(
            nested.resolve_in(&root).as_deref(),
            Some(root.join("nested/index.html").as_path())
        );

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn maps_known_content_types() {
        assert_eq!(
            AssetPath::content_type(Path::new("module.wasm")),
            "application/wasm"
        );
        assert_eq!(
            AssetPath::content_type(Path::new("style.css")),
            "text/css; charset=utf-8"
        );
    }
}
