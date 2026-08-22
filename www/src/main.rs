mod dev_server;

use std::{
    collections::{BTreeMap, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::{SystemTime, UNIX_EPOCH},
};

use dev_server::DevServer;

use comrak::{
    Anchorizer, Arena, ComrakOptions, format_html,
    nodes::{AstNode, NodeHtmlBlock, NodeValue},
    parse_document,
};

// it would be neat if we could just write this in talk.
fn main() {
    let mut args = std::env::args().skip(1);
    match (args.next().as_deref(), args.next()) {
        (None, None) => println!("{}", SiteBuilder.render()),
        (Some("build"), None) => {
            if let Err(error) = SiteBuilder.write_all(Path::new("./assets")) {
                eprintln!("site build failed: {error}");
                std::process::exit(1);
            }
        }
        (Some("dev"), None) => {
            if let Err(error) = DevServer::new(SiteBuilder).and_then(DevServer::run) {
                eprintln!("dev server failed: {error}");
                std::process::exit(1);
            }
        }
        _ => {
            eprintln!("usage: cargo run -- [build|dev]");
            std::process::exit(2);
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct SiteBuilder;

const DOCUMENTATION_CACHE_FORMAT: &str = "talk-doc-cache-v3";
const DOCUMENTATION_CACHE_FILE: &str = ".talk-doc-cache";

fn talk_compiler(repository: &Path) -> std::io::Result<PathBuf> {
    if let Some(configured) = std::env::var_os("TALK_COMPILER") {
        let configured = PathBuf::from(configured);
        return if configured.is_absolute() {
            Ok(configured)
        } else {
            Ok(std::env::current_dir()?.join(configured))
        };
    }
    let profile = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    Ok(repository.join("target").join(profile).join("talk"))
}

struct DocumentationFingerprint(DefaultHasher);

impl DocumentationFingerprint {
    fn new(namespace: &str) -> Self {
        let mut fingerprint = Self(DefaultHasher::new());
        fingerprint.add_text(namespace);
        fingerprint
    }

    fn add_text(&mut self, text: &str) {
        text.len().hash(&mut self.0);
        text.hash(&mut self.0);
    }

    fn add_bytes(&mut self, bytes: &[u8]) {
        bytes.len().hash(&mut self.0);
        bytes.hash(&mut self.0);
    }

    fn add_file(&mut self, label: &str, path: &Path) -> std::io::Result<()> {
        self.add_text(label);
        self.add_bytes(&std::fs::read(path)?);
        Ok(())
    }

    fn add_tree(&mut self, label: &str, root: &Path) -> std::io::Result<()> {
        let mut files = BTreeMap::new();
        Self::collect_tree(root, root, &mut files)?;
        self.add_text(label);
        for (relative, path) in files {
            self.add_text(&relative);
            self.add_bytes(&std::fs::read(path)?);
        }
        Ok(())
    }

    fn collect_tree(
        root: &Path,
        path: &Path,
        files: &mut BTreeMap<String, PathBuf>,
    ) -> std::io::Result<()> {
        let metadata = std::fs::symlink_metadata(path)?;
        if metadata.is_file() || metadata.file_type().is_symlink() {
            let relative = path
                .strip_prefix(root)
                .unwrap_or(path)
                .to_str()
                .ok_or_else(|| std::io::Error::other("documentation input path is not UTF-8"))?
                .to_string();
            files.insert(relative, path.to_path_buf());
            return Ok(());
        }
        if !metadata.is_dir() {
            return Ok(());
        }
        for entry in std::fs::read_dir(path)? {
            Self::collect_tree(root, &entry?.path(), files)?;
        }
        Ok(())
    }

    fn renderer(
        repository: &Path,
        compiler: &Path,
        tool_package: &Path,
    ) -> std::io::Result<String> {
        let mut fingerprint = Self::new(DOCUMENTATION_CACHE_FORMAT);
        fingerprint.add_file("compiler", compiler)?;
        fingerprint.add_tree("talk-doc", &tool_package.join("src"))?;
        fingerprint.add_file("talk-doc-package", &tool_package.join("package.tlk"))?;
        fingerprint.add_file("talk-doc-lock", &tool_package.join("package.lock"))?;

        let talk_md = repository.join("packages/talk-md");
        fingerprint.add_tree("talk-md", &talk_md.join("src"))?;
        fingerprint.add_file("talk-md-package", &talk_md.join("package.tlk"))?;
        fingerprint.add_file("talk-md-lock", &talk_md.join("package.lock"))?;

        fingerprint.add_tree("core", &repository.join("core"))?;
        let packages = repository.join("packages");
        fingerprint.add_tree("syntax", &packages.join("syntax/src"))?;
        fingerprint.add_tree("html", &packages.join("html/src"))?;
        fingerprint.add_file("fs", &packages.join("fs/src/fs.tlk"))?;
        fingerprint.add_file("os", &packages.join("os/src/os.tlk"))?;
        Ok(fingerprint.finish())
    }

    fn finish(&self) -> String {
        format!("{:016x}", self.0.finish())
    }
}

struct DocumentationModule {
    source: PathBuf,
    digest: String,
}

impl DocumentationModule {
    fn collect(
        source_root: &Path,
        path: &Path,
        modules: &mut BTreeMap<String, Self>,
    ) -> std::io::Result<()> {
        let metadata = std::fs::symlink_metadata(path)?;
        if metadata.is_dir() && !metadata.file_type().is_symlink() {
            for entry in std::fs::read_dir(path)? {
                Self::collect(source_root, &entry?.path(), modules)?;
            }
            return Ok(());
        }
        if !(metadata.is_file() || metadata.file_type().is_symlink()) {
            return Ok(());
        }
        let Some(filename) = path.file_name().and_then(|name| name.to_str()) else {
            return Err(std::io::Error::other(
                "documentation source filename is not UTF-8",
            ));
        };
        if !filename.ends_with(".tlk") || filename.ends_with(".test.tlk") {
            return Ok(());
        }

        let relative = path
            .strip_prefix(source_root)
            .map_err(|_| std::io::Error::other("documentation source escaped its root"))?;
        let stem = relative.with_extension("");
        let parts = stem
            .iter()
            .map(|part| {
                part.to_str()
                    .ok_or_else(|| std::io::Error::other("module path is not UTF-8"))
            })
            .collect::<std::io::Result<Vec<_>>>()?;
        if parts.is_empty() {
            return Ok(());
        }
        let page = format!("{}.html", parts.join("."));
        if page.contains(['\n', '\r']) {
            return Err(std::io::Error::other("module page name contains a newline"));
        }

        let source = std::fs::read(path)?;
        let mut fingerprint = DocumentationFingerprint::new("talk-doc-module-v1");
        fingerprint.add_text(&relative.to_string_lossy());
        fingerprint.add_bytes(&source);
        let module = Self {
            source: path.to_path_buf(),
            digest: fingerprint.finish(),
        };
        if modules.insert(page.clone(), module).is_some() {
            return Err(std::io::Error::other(format!(
                "multiple documentation sources map to {page}"
            )));
        }
        Ok(())
    }
}

struct DocumentationCacheEntry {
    digest: String,
    rendered: bool,
    symbol_pages: usize,
}

struct DocumentationCache {
    shared: String,
    modules: BTreeMap<String, DocumentationCacheEntry>,
}

impl DocumentationCache {
    fn read(path: &Path) -> Option<Self> {
        let text = std::fs::read_to_string(path).ok()?;
        let mut lines = text.lines();
        if lines.next()? != DOCUMENTATION_CACHE_FORMAT {
            return None;
        }
        let shared = lines.next()?.strip_prefix("shared ")?.to_string();
        let mut modules = BTreeMap::new();
        for line in lines {
            let mut fields = line.splitn(5, ' ');
            if fields.next()? != "module" {
                return None;
            }
            let digest = fields.next()?.to_string();
            let rendered = match fields.next()? {
                "0" => false,
                "1" => true,
                _ => return None,
            };
            let symbol_pages = fields.next()?.parse().ok()?;
            let page = fields.next()?.to_string();
            if page.is_empty()
                || modules
                    .insert(
                        page,
                        DocumentationCacheEntry {
                            digest,
                            rendered,
                            symbol_pages,
                        },
                    )
                    .is_some()
            {
                return None;
            }
        }
        Some(Self { shared, modules })
    }

    fn write(&self, path: &Path) -> std::io::Result<()> {
        let mut text = format!("{DOCUMENTATION_CACHE_FORMAT}\nshared {}\n", self.shared);
        for (page, entry) in &self.modules {
            text.push_str(&format!(
                "module {} {} {} {}\n",
                entry.digest,
                if entry.rendered { 1 } else { 0 },
                entry.symbol_pages,
                page
            ));
        }
        let temporary = path.with_extension(format!("tmp-{}", std::process::id()));
        std::fs::write(&temporary, text)?;
        std::fs::rename(temporary, path)
    }
}

struct DocumentationSection {
    slug: String,
    title: String,
    root: PathBuf,
    source_root: PathBuf,
}

impl DocumentationSection {
    fn all(repository: &Path) -> std::io::Result<Vec<Self>> {
        let mut sections = vec![Self {
            slug: "core".to_string(),
            title: "Core".to_string(),
            root: repository.to_path_buf(),
            source_root: repository.join("core"),
        }];

        let packages = repository.join("packages");
        let mut package_roots = std::fs::read_dir(&packages)?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.join("package.tlk").is_file())
            .collect::<Vec<_>>();
        package_roots.sort();

        for root in package_roots {
            let slug = root
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| std::io::Error::other("package directory name is not UTF-8"))?
                .to_string();
            sections.push(Self {
                title: slug.clone(),
                slug,
                source_root: root.join("src"),
                root,
            });
        }

        Ok(sections)
    }

    fn modules(&self) -> std::io::Result<BTreeMap<String, DocumentationModule>> {
        let mut modules = BTreeMap::new();
        DocumentationModule::collect(&self.source_root, &self.source_root, &mut modules)?;
        if self.slug == "core" {
            let builtins = self.source_root.join("builtins");
            let mut fingerprint = DocumentationFingerprint::new("talk-doc-builtins-v1");
            fingerprint.add_tree("builtins", &builtins)?;
            modules.insert(
                "Builtins.html".to_string(),
                DocumentationModule {
                    source: builtins,
                    digest: fingerprint.finish(),
                },
            );
        }
        Ok(modules)
    }

    fn shared_fingerprint(
        &self,
        renderer_fingerprint: &str,
        modules: &BTreeMap<String, DocumentationModule>,
    ) -> String {
        let mut fingerprint = DocumentationFingerprint::new("talk-doc-section-v2");
        fingerprint.add_text(renderer_fingerprint);
        fingerprint.add_text(&self.slug);
        fingerprint.add_text(&self.title);
        for (page, module) in modules {
            fingerprint.add_text(page);
            fingerprint.add_text(&module.digest);
        }
        fingerprint.finish()
    }

    fn symbol_page_count(directory: &Path, module_page: &str) -> std::io::Result<usize> {
        let stem = module_page.strip_suffix(".html").unwrap_or(module_page);
        let prefix = format!("{stem}.symbol-");
        Ok(std::fs::read_dir(directory)?
            .filter_map(Result::ok)
            .filter(|entry| {
                entry
                    .file_name()
                    .to_str()
                    .is_some_and(|name| name.starts_with(&prefix) && name.ends_with(".html"))
            })
            .count())
    }

    fn run_generator(
        &self,
        compiler: &Path,
        tool_package: &Path,
        output_directory: &Path,
        modules: &BTreeMap<String, DocumentationModule>,
        selected_pages: &[String],
    ) -> std::io::Result<()> {
        let repository = tool_package
            .parent()
            .and_then(Path::parent)
            .ok_or_else(|| {
                std::io::Error::other("talk-doc is not inside the repository packages directory")
            })?;
        let mut command = Command::new(compiler);
        command
            .current_dir(tool_package)
            .args(["run", "--bin", "main", "--"])
            .arg(&self.root)
            .arg(output_directory)
            .arg(&self.source_root)
            .arg(&self.title)
            .arg("--core-source")
            .arg(repository.join("core"))
            .arg("--core-docs-base")
            .arg("/docs/core/")
            .arg("--only");
        for page in selected_pages {
            let module = modules.get(page).ok_or_else(|| {
                std::io::Error::other(format!("missing documentation module for {page}"))
            })?;
            command.arg(&module.source);
        }
        let output = command.output()?;
        if output.status.success() {
            return Ok(());
        }

        Err(std::io::Error::other(format!(
            "failed to generate {} documentation\nstdout:\n{}\nstderr:\n{}",
            self.title,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )))
    }

    fn generate(
        &self,
        compiler: &Path,
        tool_package: &Path,
        docs_directory: &Path,
        renderer_fingerprint: &str,
    ) -> std::io::Result<()> {
        let output_directory = docs_directory.join(&self.slug);
        std::fs::create_dir_all(&output_directory)?;
        let cache_path = output_directory.join(DOCUMENTATION_CACHE_FILE);
        let previous = DocumentationCache::read(&cache_path);
        let modules = self.modules()?;
        let shared = self.shared_fingerprint(renderer_fingerprint, &modules);
        let same_module_set = previous
            .as_ref()
            .is_some_and(|cache| cache.modules.keys().eq(modules.keys()));
        let mut full = previous
            .as_ref()
            .is_none_or(|cache| cache.shared != shared || !same_module_set);
        let mut selected_pages = Vec::new();
        for (page, module) in &modules {
            let symbol_pages = Self::symbol_page_count(&output_directory, page)?;
            let changed = full
                || previous.as_ref().is_none_or(|cache| {
                    cache.modules.get(page).is_none_or(|entry| {
                        entry.digest != module.digest
                            || entry.rendered != output_directory.join(page).is_file()
                            || entry.symbol_pages != symbol_pages
                    })
                });
            if changed {
                selected_pages.push(page.clone());
            }
        }
        let index_missing = !output_directory.join("index.html").is_file();
        if selected_pages.is_empty() && !index_missing {
            println!("documentation {} is up to date", self.title);
            return Ok(());
        }

        let temporary_directory =
            docs_directory.join(format!(".{}.tmp-{}", self.slug, std::process::id()));
        if temporary_directory.exists() {
            std::fs::remove_dir_all(&temporary_directory)?;
        }
        std::fs::create_dir_all(&temporary_directory)?;

        let generation = (|| {
            self.run_generator(
                compiler,
                tool_package,
                &temporary_directory,
                &modules,
                &selected_pages,
            )?;

            let catalog_changed = !full
                && selected_pages.iter().any(|page| {
                    let was_rendered = previous.as_ref().is_some_and(|cache| {
                        cache.modules.get(page).is_some_and(|entry| entry.rendered)
                    });
                    was_rendered != temporary_directory.join(page).is_file()
                });
            if catalog_changed {
                std::fs::remove_dir_all(&temporary_directory)?;
                std::fs::create_dir_all(&temporary_directory)?;
                full = true;
                selected_pages = modules.keys().cloned().collect();
                self.run_generator(
                    compiler,
                    tool_package,
                    &temporary_directory,
                    &modules,
                    &selected_pages,
                )?;
            }

            if full {
                for entry in std::fs::read_dir(&output_directory)? {
                    let path = entry?.path();
                    if path.extension().and_then(|extension| extension.to_str()) == Some("html")
                        && path.file_name().and_then(|name| name.to_str()) != Some("index.html")
                        && !temporary_directory
                            .join(path.file_name().unwrap_or_default())
                            .is_file()
                    {
                        std::fs::remove_file(path)?;
                    }
                }
            }
            for page in &selected_pages {
                let stem = page.strip_suffix(".html").unwrap_or(page);
                let symbol_prefix = format!("{stem}.symbol-");

                for entry in std::fs::read_dir(&output_directory)? {
                    let path = entry?.path();
                    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
                        continue;
                    };
                    if name.starts_with(&symbol_prefix) && name.ends_with(".html") {
                        std::fs::remove_file(path)?;
                    }
                }

                let rendered_module = temporary_directory.join(page).is_file();
                let generated = std::fs::read_dir(&temporary_directory)?
                    .filter_map(Result::ok)
                    .map(|entry| entry.path())
                    .filter(|path| {
                        path.file_name()
                            .and_then(|name| name.to_str())
                            .is_some_and(|name| {
                                name == page
                                    || (name.starts_with(&symbol_prefix) && name.ends_with(".html"))
                            })
                    })
                    .collect::<Vec<_>>();
                for source in generated {
                    let destination = output_directory.join(
                        source
                            .file_name()
                            .ok_or_else(|| std::io::Error::other("generated page has no name"))?,
                    );
                    std::fs::rename(source, destination)?;
                }

                let destination = output_directory.join(page);
                if !rendered_module && destination.exists() {
                    std::fs::remove_file(destination)?;
                }
            }

            let index_source = temporary_directory.join("index.html");
            let index_destination = output_directory.join("index.html");
            std::fs::rename(index_source, index_destination)?;

            let mut cached_modules = BTreeMap::new();
            for (page, module) in &modules {
                cached_modules.insert(
                    page.clone(),
                    DocumentationCacheEntry {
                        digest: module.digest.clone(),
                        rendered: output_directory.join(page).is_file(),
                        symbol_pages: Self::symbol_page_count(&output_directory, page)?,
                    },
                );
            }
            let cache = DocumentationCache {
                shared,
                modules: cached_modules,
            };
            cache.write(&cache_path)
        })();

        let _ = std::fs::remove_dir_all(&temporary_directory);
        generation?;
        println!(
            "generated {} documentation ({} module{})",
            self.title,
            selected_pages.len(),
            if selected_pages.len() == 1 { "" } else { "s" }
        );
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct ContentPage {
    slug: &'static str,
    title: &'static str,
}

const CONTENT_PAGES: [ContentPage; 3] = [
    ContentPage {
        slug: "playground",
        title: "Playground",
    },
    ContentPage {
        slug: "qa",
        title: "Q/A",
    },
    ContentPage {
        slug: "philosophy",
        title: "Philosophy",
    },
];

#[derive(Clone, Copy)]
struct ManualPage {
    source: &'static str,
    slug: &'static str,
    title: &'static str,
}

impl ManualPage {
    fn validate_examples(self) -> std::io::Result<()> {
        let markdown = std::fs::read_to_string(format!("./manual/{}", self.source))?;
        let examples = ManualExample::from_markdown(&markdown);
        let mut accumulated: std::collections::HashMap<String, Vec<String>> =
            std::collections::HashMap::new();

        for (index, example) in examples.into_iter().enumerate() {
            let source = match &example.accumulate_group {
                Some(group) => {
                    let mut sources = accumulated.get(group).cloned().unwrap_or_default();
                    sources.push(example.source.clone());
                    sources.join("\n\n")
                }
                None => example.source.clone(),
            };

            if example.runnable {
                let output = talk("run", &source);
                if !output.status.success() {
                    return Err(std::io::Error::other(format!(
                        "manual example failed: {} block {}\nstdout:\n{}\nstderr:\n{}",
                        self.source,
                        index + 1,
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    )));
                }
            }

            if let Some(group) = example.accumulate_group {
                accumulated.entry(group).or_default().push(example.source);
            }
        }

        Ok(())
    }

    fn url(self) -> String {
        if self.slug.is_empty() {
            "/manual/".to_string()
        } else {
            format!("/manual/{}", self.slug)
        }
    }

    fn outline_title(self) -> &'static str {
        if self.slug.is_empty() {
            "Overview"
        } else {
            self.title
        }
    }
}

struct ManualExample {
    source: String,
    accumulate_group: Option<String>,
    runnable: bool,
}

impl ManualExample {
    fn from_markdown(markdown: &str) -> Vec<Self> {
        let arena = Arena::new();
        let root = parse_document(&arena, markdown, &ComrakOptions::default());
        let mut examples = Vec::new();
        Self::collect(root, &mut examples);
        examples
    }

    fn collect<'a>(node: &'a AstNode<'a>, examples: &mut Vec<Self>) {
        if let NodeValue::CodeBlock(block) = &node.data.borrow().value {
            let language = block.info.split_whitespace().next().unwrap_or_default();
            if language == "tlk" || language == "talktalk" {
                examples.push(Self {
                    source: block
                        .literal
                        .trim_end_matches(&['\n', '\r'][..])
                        .to_string(),
                    accumulate_group: accumulate_group(&block.info),
                    runnable: !block.info.contains("norun"),
                });
            }
        }
        for child in node.children() {
            Self::collect(child, examples);
        }
    }
}

struct ManualSection {
    id: String,
    title: String,
}

impl ManualSection {
    fn from_markdown(markdown: &str) -> Vec<Self> {
        let arena = Arena::new();
        let root = parse_document(&arena, markdown, &ComrakOptions::default());
        let mut anchorizer = Anchorizer::new();
        let mut sections = Vec::new();
        Self::collect(root, &mut anchorizer, &mut sections);
        sections
    }

    fn collect<'a>(node: &'a AstNode<'a>, anchorizer: &mut Anchorizer, sections: &mut Vec<Self>) {
        for child in node.children() {
            if let NodeValue::Heading(heading) = &child.data.borrow().value {
                let title = PlaygroundExample::text(child);
                let id = anchorizer.anchorize(title.clone());
                if heading.level == 2 {
                    sections.push(Self { id, title });
                }
            }
            Self::collect(child, anchorizer, sections);
        }
    }
}

const MANUAL_PAGES: [ManualPage; 20] = [
    ManualPage {
        source: "README.md",
        slug: "",
        title: "The TalkTalk Manual",
    },
    ManualPage {
        source: "getting-started.md",
        slug: "getting-started",
        title: "0. Getting Started",
    },
    ManualPage {
        source: "syntax.md",
        slug: "syntax",
        title: "1. Syntax",
    },
    ManualPage {
        source: "values-and-types.md",
        slug: "values-and-types",
        title: "2. Values and Types",
    },
    ManualPage {
        source: "bindings-and-functions.md",
        slug: "bindings-and-functions",
        title: "3. Bindings and Functions",
    },
    ManualPage {
        source: "data-and-patterns.md",
        slug: "data-and-patterns",
        title: "4. Data and Patterns",
    },
    ManualPage {
        source: "generics-and-protocols.md",
        slug: "generics-and-protocols",
        title: "5. Generics and Protocols",
    },
    ManualPage {
        source: "effects.md",
        slug: "effects",
        title: "6. Effects",
    },
    ManualPage {
        source: "ownership-and-memory.md",
        slug: "ownership-and-memory",
        title: "7. Ownership and Memory",
    },
    ManualPage {
        source: "collections-and-text.md",
        slug: "collections-and-text",
        title: "8. Collections and Text",
    },
    ManualPage {
        source: "modules-and-packages.md",
        slug: "modules-and-packages",
        title: "9. Modules and Packages",
    },
    ManualPage {
        source: "macros.md",
        slug: "macros",
        title: "10. Macros",
    },
    ManualPage {
        source: "concurrency.md",
        slug: "concurrency",
        title: "11. Concurrency",
    },
    ManualPage {
        source: "testing.md",
        slug: "testing",
        title: "12. Testing",
    },
    ManualPage {
        source: "standard-library.md",
        slug: "standard-library",
        title: "13. The Standard Library",
    },
    ManualPage {
        source: "toolchain.md",
        slug: "toolchain",
        title: "14. The Toolchain",
    },
    ManualPage {
        source: "unsafe-and-interop.md",
        slug: "unsafe-and-interop",
        title: "15. Unsafe Code and Interop",
    },
    ManualPage {
        source: "type-inference.md",
        slug: "type-inference",
        title: "A. Type Inference Reference",
    },
    ManualPage {
        source: "mir-reference.md",
        slug: "mir-reference",
        title: "B. MIR Reference",
    },
    ManualPage {
        source: "bytecode-reference.md",
        slug: "bytecode-reference",
        title: "C. Bytecode Reference",
    },
];

struct PlaygroundExample {
    id: String,
    title: String,
    summary: String,
    source: String,
    native_only: bool,
}

impl PlaygroundExample {
    fn from_markdown(markdown: &str) -> Vec<Self> {
        let arena = Arena::new();
        let root = parse_document(&arena, markdown, &ComrakOptions::default());
        let mut title = String::new();
        let mut summary = String::new();
        let mut examples = Vec::new();

        for node in root.children() {
            let data = node.data.borrow();
            match &data.value {
                NodeValue::Heading(heading) if heading.level == 2 => {
                    title = Self::text(node);
                    summary.clear();
                }
                NodeValue::Paragraph if !title.is_empty() && summary.is_empty() => {
                    summary = Self::text(node);
                }
                NodeValue::CodeBlock(block) => {
                    let Some((id, native_only)) = Self::metadata(&block.info) else {
                        continue;
                    };
                    examples.push(Self {
                        id,
                        title: title.clone(),
                        summary: summary.clone(),
                        source: block.literal.trim_end().to_string(),
                        native_only,
                    });
                }
                _ => {}
            }
        }

        examples
    }

    fn metadata(info: &str) -> Option<(String, bool)> {
        let start = info.find("playground(")? + "playground(".len();
        let end = info[start..].find(')')? + start;
        let mut values = info[start..end].split(',').map(str::trim);
        let id = values.next()?.to_string();
        if id.is_empty() {
            return None;
        }
        let native_only = values.any(|value| value == "native");
        Some((id, native_only))
    }

    fn text<'a>(node: &'a AstNode<'a>) -> String {
        let mut text = String::new();
        for child in node.children() {
            match &child.data.borrow().value {
                NodeValue::Text(value) => text.push_str(value),
                NodeValue::Code(code) => text.push_str(&code.literal),
                NodeValue::SoftBreak | NodeValue::LineBreak => text.push(' '),
                _ => text.push_str(&Self::text(child)),
            }
        }
        text.trim().to_string()
    }

    fn collection_json(examples: &[Self]) -> String {
        let entries = examples
            .iter()
            .map(|example| {
                format!(
                    "{{\"id\":\"{}\",\"title\":\"{}\",\"summary\":\"{}\",\"source\":\"{}\",\"nativeOnly\":{}}}",
                    Self::escape_json(&example.id),
                    Self::escape_json(&example.title),
                    Self::escape_json(&example.summary),
                    Self::escape_json(&example.source),
                    example.native_only,
                )
            })
            .collect::<Vec<_>>();
        format!("[{}]\n", entries.join(","))
    }

    fn escape_json(value: &str) -> String {
        let mut escaped = String::with_capacity(value.len());
        for character in value.chars() {
            match character {
                '"' => escaped.push_str("\\\""),
                '\\' => escaped.push_str("\\\\"),
                '\n' => escaped.push_str("\\n"),
                '\r' => escaped.push_str("\\r"),
                '\t' => escaped.push_str("\\t"),
                character if character.is_control() => {
                    escaped.push_str(&format!("\\u{:04x}", character as u32));
                }
                character => escaped.push(character),
            }
        }
        escaped
    }
}

impl SiteBuilder {
    pub(crate) fn render(self) -> String {
        let template = std::fs::read_to_string("./content/index.html.template").unwrap();
        let template = template.replace("{GLOBAL_NAV}", &self.global_nav("language"));
        let template = highlight_intro_examples(&template);
        let content = [
            std::fs::read_to_string("./content/index.md").unwrap(),
            std::fs::read_to_string("./content/intro.md").unwrap(),
        ]
        .join("\n\n");
        let compiled_html = self.render_markdown(&content);
        self.cache_bust(template)
            .replace("{CONTENT_GOES_HERE}", &compiled_html)
    }

    fn page_header(self, breadcrumbs: &str, title: &str, extra: &str) -> String {
        std::fs::read_to_string("./content/page-header.html.template")
            .unwrap()
            .replace("{BREADCRUMBS}", breadcrumbs)
            .replace("{TITLE}", title)
            .replace("{HEADER_EXTRA}", extra)
    }

    fn render_content_page(self, page: ContentPage) -> String {
        if page.slug == "playground" {
            let template = std::fs::read_to_string("./content/playground.html.template").unwrap();
            return self.cache_bust(
                template
                    .replace("{GLOBAL_NAV}", &self.global_nav(page.slug))
                    .replace("{TITLE}", page.title)
                    .replace(
                        "{PAGE_HEADER}",
                        &self.page_header(
                            &format!(
                                "<a href=\"/\">talktalk</a> / <a href=\"/{}\" aria-current=\"page\">{}</a>",
                                escape_html(page.slug),
                                escape_html(page.title)
                            ),
                            page.title,
                            "<span class=\"runtime-status\">runtime loading</span>",
                        ),
                    ),
            );
        }

        let template = std::fs::read_to_string("./content/page.html.template").unwrap();
        let content = std::fs::read_to_string(format!("./content/{}.md", page.slug)).unwrap();
        let compiled_html = self.render_markdown(&content);
        let template = template
            .replace("{GLOBAL_NAV}", &self.global_nav(page.slug))
            .replace("{TITLE}", page.title)
            .replace(
                "{PAGE_HEADER}",
                &self.page_header(
                    &format!(
                        "<a href=\"/\">talktalk</a> / <a href=\"/{}\" aria-current=\"page\">{}</a>",
                        escape_html(page.slug),
                        escape_html(page.title)
                    ),
                    page.title,
                    "",
                ),
            )
            .replace("{CONTENT_GOES_HERE}", &compiled_html);
        self.cache_bust(template)
    }

    fn render_manual_page(self, index: usize) -> String {
        let page = MANUAL_PAGES[index];
        let markdown = std::fs::read_to_string(format!("./manual/{}", page.source)).unwrap();
        let heading = format!("# {}", page.title);
        let content = markdown
            .strip_prefix(&heading)
            .and_then(|content| {
                content
                    .strip_prefix("\n")
                    .or_else(|| content.strip_prefix("\r\n"))
            })
            .unwrap_or_else(|| panic!("manual source {} must begin with {heading:?}", page.source));
        let compiled_html = self.render_manual_markdown(content);
        let template = std::fs::read_to_string("./content/manual.html.template").unwrap();
        let previous = index.checked_sub(1).map(|previous| MANUAL_PAGES[previous]);
        let next = MANUAL_PAGES.get(index + 1).copied();
        let previous_link = previous.map_or_else(
            || "<span></span>".to_string(),
            |previous| {
                format!(
                    "<a class=\"manual-previous\" href=\"{}\">&larr; {}</a>",
                    previous.url(),
                    previous.title
                )
            },
        );
        let next_link = next.map_or_else(
            || "<span></span>".to_string(),
            |next| {
                format!(
                    "<a class=\"manual-next\" href=\"{}\">{} &rarr;</a>",
                    next.url(),
                    next.title
                )
            },
        );
        let sections = ManualSection::from_markdown(content);
        let outline = MANUAL_PAGES
            .iter()
            .map(|outline_page| {
                let selected = outline_page.slug == page.slug;
                let current = if selected {
                    " aria-current=\"page\""
                } else {
                    ""
                };
                let section_links = if selected {
                    let links = sections
                        .iter()
                        .map(|section| {
                            format!(
                                "<li><a href=\"#{}\">{}</a></li>",
                                escape_html(&section.id),
                                escape_html(&section.title)
                            )
                        })
                        .collect::<Vec<_>>()
                        .join("\n");
                    format!("<ol class=\"manual-outline-sections\">{links}</ol>")
                } else {
                    String::new()
                };
                format!(
                    "<li><a href=\"{}\"{current}>{}</a>{section_links}</li>",
                    outline_page.url(),
                    outline_page.outline_title()
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let template = template
            .replace("{GLOBAL_NAV}", &self.global_nav("guide"))
            .replace("{TITLE}", page.title)
            .replace(
                "{PAGE_HEADER}",
                &self.page_header(
                    &format!(
                        "<a href=\"/manual/\">Guide</a> / <a href=\"{}\" aria-current=\"page\">{}</a>",
                        escape_html(&page.url()),
                        escape_html(page.title)
                    ),
                    page.title,
                    "",
                ),
            )
            .replace("{MANUAL_OUTLINE}", &outline)
            .replace("{CONTENT_GOES_HERE}", &compiled_html)
            .replace("{PREVIOUS_LINK}", &previous_link)
            .replace("{NEXT_LINK}", &next_link);
        self.cache_bust(template)
    }

    fn render_markdown(self, content: &str) -> String {
        self.render_markdown_with_links(content, false)
    }

    fn render_manual_markdown(self, content: &str) -> String {
        self.render_markdown_with_links(content, true)
    }

    fn render_markdown_with_links(self, content: &str, manual_links: bool) -> String {
        let arena = Arena::new();
        let mut options = ComrakOptions::default();
        options.extension.strikethrough = true;
        options.extension.footnotes = true;
        options.extension.header_ids = manual_links.then(String::new);
        options.render.unsafe_ = true;

        let root = parse_document(&arena, content, &options);
        if manual_links {
            self.rewrite_manual_links(root);
        }
        replace_code_blocks(root);

        let mut compiled_html = Vec::new();
        format_html(root, &options, &mut compiled_html).unwrap();
        String::from_utf8(compiled_html).unwrap()
    }

    fn rewrite_manual_links<'a>(self, node: &'a AstNode<'a>) {
        for child in node.children() {
            self.rewrite_manual_links(child);
        }

        let mut data = node.data.borrow_mut();
        let NodeValue::Link(link) = &mut data.value else {
            return;
        };
        if link.url == "README.md" {
            link.url = "/manual/".to_string();
        } else if !link.url.contains('/') && link.url.ends_with(".md") {
            link.url = format!("/manual/{}", link.url.trim_end_matches(".md"));
        } else if let Some(repository_path) = link.url.strip_prefix("../../") {
            link.url = format!("https://github.com/nakajima/talk/blob/main/{repository_path}");
        }
    }

    fn global_nav(self, current: &str) -> String {
        let mut nav = std::fs::read_to_string("./content/global-nav.html.template").unwrap();
        for slug in [
            "language",
            "guide",
            "docs",
            "playground",
            "qa",
            "philosophy",
        ] {
            let placeholder = format!("{{{}_CURRENT}}", slug.to_uppercase());
            let value = if slug == current {
                " aria-current=\"page\""
            } else {
                ""
            };
            nav = nav.replace(&placeholder, value);
        }
        nav
    }

    fn cache_bust(self, template: String) -> String {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        template
            .replace("/page.js", &format!("/page.js?t={timestamp}"))
            .replace("/playground.js", &format!("/playground.js?t={timestamp}"))
            .replace("/style.css", &format!("/style.css?t={timestamp}"))
            .replace("/docs.css", &format!("/docs.css?t={timestamp}"))
            .replace("/playground.css", &format!("/playground.css?t={timestamp}"))
    }

    fn render_documentation_index(self, sections: &[DocumentationSection]) -> String {
        let section_nav = sections
            .iter()
            .map(|section| {
                format!(
                    "<a href=\"/docs/{}/\">{}</a>",
                    escape_html(&section.slug),
                    escape_html(&section.title)
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let section_links = sections
            .iter()
            .map(|section| {
                format!(
                    "<a href=\"/docs/{}/\">{}</a>",
                    escape_html(&section.slug),
                    escape_html(&section.title)
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let template = std::fs::read_to_string("./content/docs.html.template").unwrap();
        self.cache_bust(
            template
                .replace("{GLOBAL_NAV}", &self.global_nav("docs"))
                .replace("{SECTION_NAV}", &section_nav)
                .replace("{SECTION_LINKS}", &section_links),
        )
    }

    fn write_documentation(self, directory: &Path) -> std::io::Result<()> {
        let repository = Path::new("..").canonicalize()?;
        let compiler = talk_compiler(&repository)?;
        let tool_package = repository.join("packages/talk-doc");
        let docs_directory = directory.join("docs");
        std::fs::create_dir_all(&docs_directory)?;
        let docs_directory = docs_directory.canonicalize()?;

        let sections = DocumentationSection::all(&repository)?;
        let current_slugs = sections
            .iter()
            .map(|section| section.slug.as_str())
            .collect::<Vec<_>>();
        for entry in std::fs::read_dir(&docs_directory)? {
            let path = entry?.path();
            if path.is_dir()
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| !name.starts_with('.') && !current_slugs.contains(&name))
            {
                std::fs::remove_dir_all(path)?;
            }
        }

        let renderer_fingerprint =
            DocumentationFingerprint::renderer(&repository, &compiler, &tool_package)?;
        let results = thread::scope(|scope| {
            sections
                .iter()
                .map(|section| {
                    scope.spawn(|| {
                        section.generate(
                            &compiler,
                            &tool_package,
                            &docs_directory,
                            &renderer_fingerprint,
                        )
                    })
                })
                .collect::<Vec<_>>()
                .into_iter()
                .map(|handle| {
                    handle.join().unwrap_or_else(|_| {
                        Err(std::io::Error::other(
                            "documentation generator thread panicked",
                        ))
                    })
                })
                .collect::<Vec<_>>()
        });
        for result in results {
            result?;
        }

        self.write_asset(
            &docs_directory.join("index.html"),
            self.render_documentation_index(&sections),
        )
    }

    pub(crate) fn write_all(self, directory: &Path) -> std::io::Result<()> {
        self.write_asset(&directory.join("index.html"), self.render())?;
        self.write_documentation(directory)?;
        for page in CONTENT_PAGES {
            self.write_asset(
                &directory.join(format!("{}.html", page.slug)),
                self.render_content_page(page),
            )?;
        }
        let manual_directory = directory.join("manual");
        std::fs::create_dir_all(&manual_directory)?;
        for (index, page) in MANUAL_PAGES.iter().enumerate() {
            page.validate_examples()?;
            let filename = if page.slug.is_empty() {
                "index.html".to_string()
            } else {
                format!("{}.html", page.slug)
            };
            self.write_asset(
                &manual_directory.join(filename),
                self.render_manual_page(index),
            )?;
        }

        let playground = std::fs::read_to_string("./content/playground.md")?;
        let examples = PlaygroundExample::from_markdown(&playground);
        self.write_asset(
            &directory.join("playground-examples.json"),
            PlaygroundExample::collection_json(&examples),
        )
    }

    fn write_asset(self, path: &Path, content: String) -> std::io::Result<()> {
        let temporary_path = path.with_extension("tmp");
        std::fs::write(&temporary_path, content)?;
        std::fs::rename(temporary_path, path)
    }
}

fn escape_html(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '&' => escaped.push_str("&amp;"),
            '<' => escaped.push_str("&lt;"),
            '>' => escaped.push_str("&gt;"),
            '"' => escaped.push_str("&quot;"),
            '\'' => escaped.push_str("&#39;"),
            _ => escaped.push(ch),
        }
    }
    escaped
}

fn line_count(value: &str) -> usize {
    let mut count = 1;
    for ch in value.chars() {
        if ch == '\n' {
            count += 1;
        }
    }
    count
}

fn highlight(code: &str) -> String {
    let mut child = std::process::Command::new(
        talk_compiler(Path::new("..")).expect("resolve Talk compiler path"),
    )
    .arg("html")
    .arg("-")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()
    .unwrap();

    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(code.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    let output = String::from_utf8_lossy(&output.stdout);
    output.trim_end_matches(&['\n', '\r'][..]).to_string()
}

fn highlight_intro_examples(template: &str) -> String {
    let Some(intro_start) = template
        .find("<code class=\"intro-text\">")
        .or_else(|| template.find("<code class=\"intro-txt\">"))
    else {
        return template.to_string();
    };
    let Some(intro_end_offset) = template[intro_start..].find("</code>") else {
        return template.to_string();
    };
    let intro_end = intro_start + intro_end_offset;
    let intro = &template[intro_start..intro_end];
    let mut names = Vec::new();
    let mut cursor = 0;

    while let Some(attr_offset) = intro[cursor..].find("data-example=\"") {
        let value_start = cursor + attr_offset + "data-example=\"".len();
        let Some(value_end_offset) = intro[value_start..].find('"') else {
            break;
        };
        let value_end = value_start + value_end_offset;
        names.push(&intro[value_start..value_end]);
        cursor = value_end + 1;
    }

    let mut examples = String::new();
    let mut default_highlighted: Option<String> = None;
    for name in names {
        let path = format!("./content/intro-code/{name}.tlk");
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {path}: {err}"));
        let source = format(source.trim_end_matches(&['\n', '\r'][..]));
        let highlighted = highlight(&source);
        if default_highlighted.is_none() {
            default_highlighted = Some(highlighted.clone());
        }
        examples.push_str("\n            <template data-example=\"");
        examples.push_str(name);
        examples.push_str("\">");
        examples.push_str(&highlighted);
        examples.push_str("</template>");
    }
    examples.push('\n');

    let mut result = template.to_string();
    result.insert_str(intro_end + "</code>".len(), &examples);

    let Some(default_highlighted) = default_highlighted else {
        return result;
    };
    let Some(code_container_start) = result.find("<div class=\"intro-code\">") else {
        return result;
    };
    let Some(pre_start_offset) = result[code_container_start..].find("<pre>") else {
        return result;
    };
    let source_start = code_container_start + pre_start_offset + "<pre>".len();
    let Some(source_end_offset) = result[source_start..].find("</pre>") else {
        return result;
    };
    let source_end = source_start + source_end_offset;
    result.replace_range(source_start..source_end, &default_highlighted);
    result
}

fn talk(command: &str, code: &str) -> std::process::Output {
    let mut child = std::process::Command::new(
        talk_compiler(Path::new("..")).expect("resolve Talk compiler path"),
    )
    .arg(command)
    .arg("-")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();

    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(code.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn format(code: &str) -> String {
    // `talk format` echoes the input back on parse errors instead of
    // failing, so check parseability explicitly first.
    let parse = talk("parse", code);
    if !parse.status.success() {
        panic!(
            "failed to parse snippet:\n{code}\nerror: {}",
            String::from_utf8_lossy(&parse.stderr)
        );
    }
    let output = talk("format", code);
    if !output.status.success() {
        panic!(
            "failed to format snippet:\n{code}\nerror: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let output = String::from_utf8_lossy(&output.stdout);
    output.trim_end_matches(&['\n', '\r'][..]).to_string()
}

fn accumulate_group(info: &str) -> Option<String> {
    let start = info.find("accumulate")? + "accumulate".len();
    let rest = info[start..].trim_start();
    if let Some(inner) = rest.strip_prefix('(') {
        let end = inner.find(')')?;
        Some(inner[..end].trim().to_string())
    } else {
        Some(String::new())
    }
}

fn accumulation_attrs(group: Option<&str>) -> String {
    match group {
        Some(group) => format!(
            " data-accumulates='true' data-accumulate-group='{}'",
            escape_html(group)
        ),
        None => String::new(),
    }
}

fn runnable(code: &str, accumulate_group: Option<&str>) -> String {
    let code = format(code.trim_end_matches(&['\n', '\r'][..]));
    let code = code.as_str();
    let highlighted = highlight(code);
    let raw = escape_html(code);
    let rows = line_count(code);
    let accumulation = accumulation_attrs(accumulate_group);
    format!(
        "<div class='runnable'{accumulation}>
            <div class='code-block'>
                <pre class='code-highlight' aria-hidden='true'>{highlighted}</pre>
                <div class='code-diagnostics' aria-hidden='true'></div>
                <textarea class='code-editable' rows='{rows}' spellcheck='false' autocapitalize='off' autocorrect='off' autocomplete='off' wrap='off'>{raw}</textarea>
            </div>
            <div class='actions'>
                <span class='action-control' data-tooltip='WASM bundle initializing' aria-label='WASM bundle initializing' tabindex='0'>
                    <button type='button' class='run' disabled>Run</button>
                </span>
                <span class='action-control' data-tooltip='WASM bundle initializing' aria-label='WASM bundle initializing' tabindex='0'>
                    <button type='button' class='lower' disabled>Lower</button>
                </span>
                <span class='action-control' data-tooltip='WASM bundle initializing' aria-label='WASM bundle initializing' tabindex='0'>
                    <button type='button' class='format' disabled>Format</button>
                </span>
            </div>
            <div class='result'></div>
        </div>"
    )
}

fn norun(code: &str, accumulate_group: Option<&str>) -> String {
    let code = format(code.trim_end_matches(&['\n', '\r'][..]));
    let code = code.as_str();
    let highlighted = highlight(code);
    let accumulation = match accumulate_group {
        Some(group) => format!(
            "{} data-source='{}'",
            accumulation_attrs(Some(group)),
            escape_html(code)
        ),
        None => String::new(),
    };
    format!(
        "<div class='code-block no-run'{accumulation}>
            <pre class='code-highlight'>{highlighted}</pre>
        </div>"
    )
}

fn replace_code_blocks<'a>(node: &'a AstNode<'a>) {
    for child in node.children() {
        replace_code_blocks(child);
    }

    let mut data = node.data.borrow_mut();
    if let NodeValue::CodeBlock(block) = &data.value {
        let language = block.info.split_whitespace().next().unwrap_or_default();
        if language != "tlk" && language != "talktalk" {
            return;
        }
        data.value = NodeValue::HtmlBlock(NodeHtmlBlock {
            block_type: 1,
            literal: if block.info.contains("norun") {
                norun(&block.literal, accumulate_group(&block.info).as_deref())
            } else {
                runnable(&block.literal, accumulate_group(&block.info).as_deref())
            },
        })
    };
}
