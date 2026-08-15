mod dev_server;

use std::{
    io::Write,
    path::Path,
    process::Stdio,
    time::{SystemTime, UNIX_EPOCH},
};

use dev_server::DevServer;

use comrak::{
    Arena, ComrakOptions, format_html,
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

    fn render_content_page(self, page: ContentPage) -> String {
        let template = std::fs::read_to_string("./content/page.html.template").unwrap();
        let content = std::fs::read_to_string(format!("./content/{}.md", page.slug)).unwrap();
        let compiled_html = self.render_markdown(&content);
        let template = template
            .replace("{GLOBAL_NAV}", &self.global_nav(page.slug))
            .replace("{TITLE}", page.title)
            .replace("{SLUG}", page.slug)
            .replace("{CONTENT_GOES_HERE}", &compiled_html);
        self.cache_bust(template)
    }

    fn render_markdown(self, content: &str) -> String {
        let arena = Arena::new();
        let mut options = ComrakOptions::default();
        options.extension.strikethrough = true;
        options.extension.footnotes = true;
        options.render.unsafe_ = true;

        let root = parse_document(&arena, content, &options);
        replace_code_blocks(root);

        let mut compiled_html = Vec::new();
        format_html(root, &options, &mut compiled_html).unwrap();
        String::from_utf8(compiled_html).unwrap()
    }

    fn global_nav(self, current: &str) -> String {
        let mut nav = std::fs::read_to_string("./content/global-nav.html.template").unwrap();
        for slug in ["language", "playground", "qa", "philosophy"] {
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
            .replace("/style.css", &format!("/style.css?t={timestamp}"))
    }

    pub(crate) fn write_all(self, directory: &Path) -> std::io::Result<()> {
        self.write_asset(&directory.join("index.html"), self.render())?;
        for page in CONTENT_PAGES {
            self.write_asset(
                &directory.join(format!("{}.html", page.slug)),
                self.render_content_page(page),
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
    let mut child = std::process::Command::new("../target/release/talk")
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
    let mut child = std::process::Command::new("../target/release/talk")
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
        </div>
        "
    )
}

fn replace_code_blocks<'a>(node: &'a AstNode<'a>) {
    for child in node.children() {
        replace_code_blocks(child);
    }

    let mut data = node.data.borrow_mut();
    if let NodeValue::CodeBlock(block) = &data.value {
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
