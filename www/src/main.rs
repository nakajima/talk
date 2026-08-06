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
    let template = highlight_intro_examples(&template);
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
        std::fs::read_to_string("./content/index.md").unwrap(),
        std::fs::read_to_string("./content/intro.md").unwrap(),
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
    let mut child = std::process::Command::new("../target/debug/talk")
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
                <button type='button' class='run'>Run</button>
                <button type='button' class='lower'>Lower</button>
                <button type='button' class='format'>Format</button>
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
