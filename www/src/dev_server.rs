use std::{
    collections::{BTreeMap, HashMap},
    env, fs,
    io::{self, Read, Write},
    net::{TcpListener, TcpStream},
    path::{Path, PathBuf},
    process::Command,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
    },
    thread,
    time::{Duration, Instant, SystemTime},
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
    rendered: Arc<RenderedPages>,
}

// Pages rendered on demand, keyed by normalized route and cleared whenever a
// site source changes.
#[derive(Default)]
struct RenderedPages {
    pages: Mutex<HashMap<String, RenderedPage>>,
    // Held while rendering so concurrent requests for a page share one
    // render: the first request renders while the rest wait here and then
    // read the cache. Renders spawn several compiler subprocesses each, so
    // letting them stack up starves the machine.
    rendering: Mutex<()>,
}

impl RenderedPages {
    fn clear(&self) {
        self.pages.lock().unwrap().clear();
    }

    fn get_or_render(
        &self,
        route: &str,
        render: impl FnOnce() -> Result<Option<RenderedPage>, ()>,
    ) -> Result<Option<RenderedPage>, ()> {
        if let Some(page) = self.pages.lock().unwrap().get(route) {
            return Ok(Some(page.clone()));
        }
        let _rendering = self.rendering.lock().unwrap();
        if let Some(page) = self.pages.lock().unwrap().get(route) {
            return Ok(Some(page.clone()));
        }
        let result = render()?;
        if let Some(page) = &result {
            self.pages
                .lock()
                .unwrap()
                .insert(route.to_string(), page.clone());
        }
        Ok(result)
    }
}

#[derive(Clone)]
struct RenderedPage {
    content_type: &'static str,
    body: Vec<u8>,
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
        if !assets.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "./assets is missing; run the dev server from the www directory",
            ));
        }

        let listener = TcpListener::bind(("0.0.0.0", port))?;
        listener.set_nonblocking(true)?;

        Ok(Self {
            assets,
            builder,
            executable: env::current_exe()?,
            listener,
            sources: SourceState::capture(),
            rendered: Arc::new(RenderedPages::default()),
        })
    }

    pub(crate) fn run(mut self) -> io::Result<()> {
        let address = self.listener.local_addr()?;
        println!("serving http://localhost:{}", address.port());
        let documentation = DocumentationWorker::spawn(self.builder, self.assets.clone());

        loop {
            self.accept_connections()?;
            thread::sleep(POLL_INTERVAL);
            self.rebuild_if_needed(&documentation)?;
        }
    }

    fn accept_connections(&self) -> io::Result<()> {
        loop {
            match self.listener.accept() {
                Ok((stream, _)) => {
                    let connection = Connection {
                        stream,
                        assets: self.assets.clone(),
                        builder: self.builder,
                        rendered: Arc::clone(&self.rendered),
                    };
                    thread::spawn(move || {
                        if let Err(error) = connection.serve()
                            && !matches!(
                                error.kind(),
                                io::ErrorKind::BrokenPipe
                                    | io::ErrorKind::ConnectionReset
                                    | io::ErrorKind::ConnectionAborted
                            )
                        {
                            eprintln!("request failed: {error}");
                        }
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(()),
                Err(error) => return Err(error),
            }
        }
    }

    fn rebuild_if_needed(&mut self, documentation: &DocumentationWorker) -> io::Result<()> {
        let current = SourceState::capture();
        let executable_changed = current.executable != self.sources.executable;
        let site_changed = current.site != self.sources.site;
        if executable_changed {
            // Replacing this process while documentation commands are running
            // would orphan those compiler children. Wait for the worker to go
            // idle, then rebuild and exec from a clean process tree.
            if documentation.is_busy() {
                return Ok(());
            }
            self.sources = current;
            println!("server source changed; rebuilding");
            let status = Command::new("cargo")
                .args(["build", "--package", "builder"])
                .status()?;
            if status.success() {
                return self.restart();
            }
            eprintln!("server rebuild failed; keeping the current process running");
        } else if site_changed {
            self.sources = current;
            println!(
                "site source changed; request-rendered pages invalidated; regenerating documentation"
            );
            self.rendered.clear();
            documentation.mark_dirty();
        } else {
            self.sources = current;
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

// Documentation pages come from the talk-doc generator, which renders into
// files with its own incremental cache, so they stay on disk rather than
// rendering per request. Generation runs on this worker's thread to keep the
// accept loop responsive while it works.
struct DocumentationWorker {
    busy: Arc<AtomicBool>,
    dirty: Arc<AtomicBool>,
}

impl DocumentationWorker {
    fn spawn(builder: SiteBuilder, assets: PathBuf) -> Self {
        let busy = Arc::new(AtomicBool::new(true));
        let dirty = Arc::new(AtomicBool::new(true));
        let busy_flag = Arc::clone(&busy);
        let dirty_flag = Arc::clone(&dirty);
        thread::spawn(move || {
            loop {
                if dirty_flag.swap(false, Ordering::SeqCst) {
                    busy_flag.store(true, Ordering::SeqCst);
                    let started = Instant::now();
                    match std::panic::catch_unwind(|| builder.write_documentation(&assets)) {
                        Ok(Ok(())) => println!(
                            "documentation regenerated in {}",
                            elapsed_label(started.elapsed())
                        ),
                        Ok(Err(error)) => eprintln!("documentation rebuild failed: {error}"),
                        Err(_) => {
                            eprintln!("documentation rebuild failed; keeping the previous pages");
                        }
                    }
                    busy_flag.store(false, Ordering::SeqCst);
                }
                thread::sleep(POLL_INTERVAL);
            }
        });
        Self { busy, dirty }
    }

    fn is_busy(&self) -> bool {
        self.busy.load(Ordering::SeqCst)
    }

    fn mark_dirty(&self) {
        self.dirty.store(true, Ordering::SeqCst);
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
        FileStamp::collect(Path::new("../core"), &mut site);
        FileStamp::collect(Path::new("../stdlib"), &mut site);
        FileStamp::collect(Path::new("../packages"), &mut site);

        Self { executable, site }
    }
}

fn elapsed_label(duration: Duration) -> String {
    if duration.as_secs_f64() >= 1.0 {
        format!("{:.1}s", duration.as_secs_f64())
    } else {
        format!("{}ms", duration.as_millis())
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
    builder: SiteBuilder,
    rendered: Arc<RenderedPages>,
}

impl Connection {
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

        let head_only = request.method == "HEAD";
        let Some(asset_path) = AssetPath::from_target(&request.target) else {
            return self.respond(
                "400 Bad Request",
                "text/plain; charset=utf-8",
                b"invalid path\n".to_vec(),
                head_only,
            );
        };
        match self.dynamic_page(&asset_path.route()) {
            Ok(Some(page)) => {
                return self.respond("200 OK", page.content_type, page.body, head_only);
            }
            Ok(None) => {}
            Err(()) => {
                return self.respond(
                    "500 Internal Server Error",
                    "text/plain; charset=utf-8",
                    b"page render failed; see the dev server log\n".to_vec(),
                    head_only,
                );
            }
        }
        let Some(path) = asset_path.resolve_in(&self.assets) else {
            return self.respond(
                "404 Not Found",
                "text/plain; charset=utf-8",
                b"not found\n".to_vec(),
                head_only,
            );
        };

        let content_type = AssetPath::content_type(&path);
        let body = fs::read(path)?;
        self.respond("200 OK", content_type, body, head_only)
    }

    fn dynamic_page(&self, route: &str) -> Result<Option<RenderedPage>, ()> {
        if crate::page_route(route).is_none() {
            return Ok(None);
        }
        let builder = self.builder;
        self.rendered.get_or_render(route, || {
            let started = Instant::now();
            match std::panic::catch_unwind(move || builder.render_route(route)) {
                Ok(Some((content_type, body))) => {
                    println!("rendered /{route} in {}", elapsed_label(started.elapsed()));
                    Ok(Some(RenderedPage {
                        content_type,
                        body: body.into_bytes(),
                    }))
                }
                Ok(None) => Ok(None),
                Err(_) => Err(()),
            }
        })
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

    // Normalizes the request into the route form `crate::page_route` expects:
    // no leading or trailing slash and no ".html" or "/index" suffix.
    fn route(&self) -> String {
        let mut route = self.relative.to_string_lossy().into_owned();
        if let Some(length) = route.strip_suffix(".html").map(str::len) {
            route.truncate(length);
        }
        if route == "index" {
            route.clear();
        } else if let Some(length) = route.strip_suffix("/index").map(str::len) {
            route.truncate(length);
        }
        route
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
    use super::{AssetPath, RenderedPage, RenderedPages, elapsed_label};
    use std::{
        fs,
        path::Path,
        sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        },
        thread,
        time::Duration,
    };

    #[test]
    fn concurrent_requests_share_one_render() {
        let rendered = Arc::new(RenderedPages::default());
        let renders = Arc::new(AtomicUsize::new(0));
        let handles = (0..8)
            .map(|_| {
                let rendered = Arc::clone(&rendered);
                let renders = Arc::clone(&renders);
                thread::spawn(move || {
                    rendered.get_or_render("manual/effects", || {
                        renders.fetch_add(1, Ordering::SeqCst);
                        thread::sleep(Duration::from_millis(50));
                        Ok(Some(RenderedPage {
                            content_type: "text/html; charset=utf-8",
                            body: b"page".to_vec(),
                        }))
                    })
                })
            })
            .collect::<Vec<_>>();
        for handle in handles {
            let page = handle.join().unwrap().unwrap().unwrap();
            assert_eq!(page.body, b"page");
        }
        assert_eq!(renders.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn cleared_pages_render_again() {
        let rendered = RenderedPages::default();
        let render = || {
            Ok(Some(RenderedPage {
                content_type: "text/html; charset=utf-8",
                body: b"page".to_vec(),
            }))
        };
        rendered.get_or_render("qa", render).unwrap();
        rendered.clear();
        let renders = AtomicUsize::new(0);
        rendered
            .get_or_render("qa", || {
                renders.fetch_add(1, Ordering::SeqCst);
                render()
            })
            .unwrap();
        assert_eq!(renders.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn elapsed_labels_use_millis_under_a_second_and_seconds_above() {
        assert_eq!(elapsed_label(Duration::from_millis(0)), "0ms");
        assert_eq!(elapsed_label(Duration::from_millis(340)), "340ms");
        assert_eq!(elapsed_label(Duration::from_millis(1540)), "1.5s");
        assert_eq!(elapsed_label(Duration::from_secs(62)), "62.0s");
    }

    #[test]
    fn rejects_traversal_paths() {
        assert!(AssetPath::from_target("/../Cargo.toml").is_none());
        assert!(AssetPath::from_target("/%2e%2e/Cargo.toml").is_none());
        assert!(AssetPath::from_target("/..%2fCargo.toml").is_none());
    }

    #[test]
    fn routes_normalize_request_targets() {
        let route = |target: &str| AssetPath::from_target(target).unwrap().route();
        assert_eq!(route("/"), "");
        assert_eq!(route("/index.html"), "");
        assert_eq!(route("/playground"), "playground");
        assert_eq!(route("/playground.html"), "playground");
        assert_eq!(route("/playground?example=hello"), "playground");
        assert_eq!(route("/manual/"), "manual");
        assert_eq!(route("/manual/index.html"), "manual");
        assert_eq!(route("/manual/effects"), "manual/effects");
        assert_eq!(route("/docs/core/Array.html"), "docs/core/Array");
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
