use std::{
    io::Write,
    process::Stdio,
    time::{SystemTime, UNIX_EPOCH},
};

use comrak::{
    Arena, ComrakOptions, format_html,
    nodes::{AstNode, NodeHtmlBlock, NodeValue},
    parse_document,
};

// it would be neat if we could just write this in talk.
fn main() {
    let template = std::fs::read_to_string("./content/index.html.template").unwrap();
    let template = template.replace(
        "/page.js",
        &format!(
            "/page.js?t={}",
            &SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
        ),
    );
    let template = template.replace(
        "/style.css",
        &format!(
            "/style.css?t={}",
            &SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
        ),
    );

    let content = [
        std::fs::read_to_string("./content/intro.md").unwrap(),
        std::fs::read_to_string("./content/index.md").unwrap(),
    ]
    .join("\n\n");
    let arena = Arena::new();
    let mut options = ComrakOptions::default();
    options.extension.strikethrough = true;
    options.extension.footnotes = true;
    options.render.unsafe_ = true;

    let root = parse_document(&arena, &content, &options);
    replace_code_blocks(root);

    let mut compiled_html = Vec::new();
    format_html(root, &options, &mut compiled_html).unwrap();
    let compiled_html = String::from_utf8(compiled_html).unwrap();
    let result = template.replace("{CONTENT_GOES_HERE}", compiled_html.as_str());
    println!("{result}");
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
    let mut child = std::process::Command::new("../target/debug/talk")
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

fn _format(code: &str) -> String {
    let mut child = std::process::Command::new("../target/debug/talk")
        .arg("format")
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

fn runnable(code: &str) -> String {
    let code = code.trim_end_matches(&['\n', '\r'][..]);
    let highlighted = highlight(code);
    let raw = escape_html(code);
    let rows = line_count(code);
    format!(
        "<div class='runnable'>
            <div class='code-block'>
                <pre class='code-highlight' aria-hidden='true'>{highlighted}</pre>
                <div class='code-diagnostics' aria-hidden='true'></div>
                <textarea class='code-editable' rows='{rows}' spellcheck='false' autocapitalize='off' autocorrect='off' autocomplete='off' wrap='off'>{raw}</textarea>
            </div>
            <div class='actions'>
                <button type='button' class='run'>Run</button>
                <button type='button' class='lower'>Lower</button>
                <button type='button' class='format'>Format</button>
            </div>
            <div class='result'></div>
        </div>"
    )
}

fn norun(code: &str) -> String {
    let code = code.trim_end_matches(&['\n', '\r'][..]);
    let highlighted = highlight(code);
    format!(
        "<div class='code-block no-run'>
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
                norun(&block.literal)
            } else {
                runnable(&block.literal)
            },
        })
    };
}
