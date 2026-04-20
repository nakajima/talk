use std::{
    io::Write,
    process::Stdio,
    time::{SystemTime, UNIX_EPOCH},
};

use comrak::{
    Arena, ComrakOptions, format_html,
    nodes::{AstNode, NodeValue},
    parse_document,
};

fn main() {
    let template = std::fs::read_to_string("./content/index.html.template").unwrap();
    let ts = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let template = template.replace("/page.js", &format!("/page.js?t={ts}"));
    let template = template.replace("/style.css", &format!("/style.css?t={ts}"));
    let template = template.replace("/reset.css", &format!("/reset.css?t={ts}"));

    let out = template
        .replace("{HERO}", &render_hero(&read("hero.md")))
        .replace("{GOALS}", &render_goals(&read("goals.md")))
        .replace("{TOUR}", &render_tour(&read("tour.md")))
        .replace("{PIPELINE}", &render_pipeline(&read("pipeline.md")))
        .replace("{ROADMAP}", &render_roadmap(&read("roadmap.md")))
        .replace("{INSTALL}", &render_install(&read("install.md")));

    println!("{out}");
}

fn read(name: &str) -> String {
    std::fs::read_to_string(format!("./content/{name}")).unwrap()
}

fn comrak_opts() -> ComrakOptions {
    let mut options = ComrakOptions::default();
    options.extension.strikethrough = true;
    options.extension.footnotes = true;
    options.render.unsafe_ = true;
    options
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

fn pad2(n: usize) -> String {
    format!("{n:02}")
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

fn render_inline<'a>(node: &'a AstNode<'a>) -> String {
    let opts = comrak_opts();
    let mut result = String::new();
    for child in node.children() {
        let mut inner: Vec<u8> = Vec::new();
        format_html(child, &opts, &mut inner).unwrap();
        result.push_str(&String::from_utf8_lossy(&inner));
    }
    let trimmed = result.trim();
    if let Some(rest) = trimmed.strip_prefix("<p>") {
        if let Some(core) = rest.strip_suffix("</p>") {
            return core.trim().to_string();
        }
    }
    trimmed.to_string()
}

fn render_block<'a>(node: &'a AstNode<'a>) -> String {
    let opts = comrak_opts();
    let mut buf = Vec::new();
    format_html(node, &opts, &mut buf).unwrap();
    String::from_utf8_lossy(&buf).to_string()
}

/// Returns (info, literal) for a code-block node.
fn code_block<'a>(node: &'a AstNode<'a>) -> Option<(String, String)> {
    let data = node.data.borrow();
    if let NodeValue::CodeBlock(block) = &data.value {
        Some((block.info.clone(), block.literal.clone()))
    } else {
        None
    }
}

fn text_of<'a>(node: &'a AstNode<'a>) -> String {
    let mut out = String::new();
    match &node.data.borrow().value {
        NodeValue::Text(t) => out.push_str(t),
        NodeValue::Code(c) => out.push_str(&c.literal),
        _ => {
            for child in node.children() {
                out.push_str(&text_of(child));
            }
        }
    }
    out
}

fn heading_level<'a>(node: &'a AstNode<'a>) -> Option<u8> {
    if let NodeValue::Heading(h) = &node.data.borrow().value {
        Some(h.level)
    } else {
        None
    }
}

/// Emit a runnable code editor (used by hero playground + tour snippets).
/// Preserves all class hooks page.js relies on.
fn runnable_snippet(code: &str, file: &str) -> String {
    let code = code.trim_end_matches(&['\n', '\r'][..]);
    let highlighted = highlight(code);
    let raw = escape_html(code);
    let rows = line_count(code);
    let gutter: String = (1..=rows).map(|i| format!("{i:>2}\n")).collect();
    format!(
        "<div class='runnable snippet'>
            <div class='snippet__head'>
              <span class='file'>{file}</span>
              <span class='lang'>talktalk</span>
            </div>
            <div class='snippet__body'>
              <div class='snippet__gutter'>{gutter}</div>
              <div class='code-block'>
                <pre class='code-highlight' aria-hidden='true'>{highlighted}</pre>
                <div class='code-diagnostics' aria-hidden='true'></div>
                <textarea class='code-editable' rows='{rows}' spellcheck='false' autocapitalize='off' autocorrect='off' autocomplete='off' wrap='off'>{raw}</textarea>
              </div>
            </div>
            <div class='actions snippet__tray'>
                <button type='button' class='run' data-primary>▸ Run</button>
                <button type='button' class='lower'>▽ Lower</button>
                <button type='button' class='format'>↺ Format</button>
                <span class='spacer'></span>
            </div>
            <div class='result snippet__out'></div>
        </div>",
        file = escape_html(file),
    )
}

fn norun_snippet(code: &str, file: &str) -> String {
    let code = code.trim_end_matches(&['\n', '\r'][..]);
    let highlighted = highlight(code);
    let rows = line_count(code);
    let gutter: String = (1..=rows).map(|i| format!("{i:>2}\n")).collect();
    format!(
        "<div class='snippet no-run'>
            <div class='snippet__head'>
              <span class='file'>{file}</span>
              <span class='lang'>talktalk</span>
            </div>
            <div class='snippet__body'>
              <div class='snippet__gutter'>{gutter}</div>
              <pre class='snippet__code'>{highlighted}</pre>
            </div>
        </div>",
        file = escape_html(file),
    )
}

// ── Hero ────────────────────────────────────────────────────────────
fn render_hero(md: &str) -> String {
    let arena = Arena::new();
    let opts = comrak_opts();
    let root = parse_document(&arena, md, &opts);

    let mut heading = String::new();
    let mut paragraphs = Vec::new();
    let mut code = String::new();

    for child in root.children() {
        match &child.data.borrow().value.clone() {
            NodeValue::Heading(h) if h.level == 1 => {
                heading = render_inline(child);
            }
            NodeValue::Paragraph => {
                paragraphs.push(render_block(child));
            }
            NodeValue::CodeBlock(block) => {
                code = block.literal.clone();
            }
            _ => {}
        }
    }

    let lede: String = paragraphs
        .iter()
        .map(|p| {
            // Mark the last paragraph as dim.
            p.clone()
        })
        .collect::<Vec<_>>()
        .join("\n");

    let play = if code.is_empty() {
        String::new()
    } else {
        runnable_snippet(&code, "hello.tlk")
    };

    format!(
        "<div class='hero' id='hero'>
          <div class='hero__pitch'>
            <h2 class='hero__head'>{heading}</h2>
            <div class='hero__lede'>{lede}</div>
            <div class='hero__cta'>
              <a class='btn btn--primary' href='#tour'>▸ Take the tour</a>
              <a class='btn' href='#pipeline'>How it works →</a>
              <a class='btn btn--ghost' href='#install'>Install <span class='kbd'>⌘</span></a>
            </div>
            <div class='hero__meta'>
              <div>Version <strong>0.1.1</strong></div>
              <div>License <strong>MIT</strong></div>
              <div>Stability <strong>ha. no.</strong></div>
            </div>
          </div>
          <div class='hero__play'>
            <div class='playground'>
              <div class='playground__head'>
                <div class='playground__dots'><span></span><span></span><span></span></div>
                <span class='playground__title'>hello.tlk</span>
                <span style='margin-left:auto;font-size:11px;letter-spacing:0.06em;text-transform:uppercase;color:var(--ink-mute);padding-right:10px'>talktalk</span>
              </div>
              {play}
            </div>
          </div>
        </div>"
    )
}

// ── Goals ───────────────────────────────────────────────────────────
fn render_goals(md: &str) -> String {
    let arena = Arena::new();
    let opts = comrak_opts();
    let root = parse_document(&arena, md, &opts);

    let mut h1 = String::new();
    let mut subtitle = String::new();
    let mut goals: Vec<(bool, String, String)> = Vec::new();
    let mut mark_nongoal = false;
    let mut current: Option<(bool, String, String)> = None;
    let mut saw_h1 = false;

    for child in root.children() {
        let value = child.data.borrow().value.clone();
        match value {
            NodeValue::Heading(h) if h.level == 1 => {
                h1 = render_inline(child);
                saw_h1 = true;
            }
            NodeValue::Heading(h) if h.level == 3 => {
                if let Some(c) = current.take() {
                    goals.push(c);
                }
                let title = render_inline(child);
                current = Some((mark_nongoal, title, String::new()));
                mark_nongoal = false;
            }
            NodeValue::Paragraph => {
                let html = render_block(child);
                if let Some(c) = current.as_mut() {
                    c.2.push_str(&html);
                } else if saw_h1 && subtitle.is_empty() {
                    // first paragraph after H1 is the subtitle
                    let inline = render_inline(child);
                    subtitle = inline;
                }
            }
            NodeValue::HtmlBlock(block) => {
                if block.literal.contains("nongoal") {
                    mark_nongoal = true;
                }
            }
            _ => {}
        }
    }
    if let Some(c) = current.take() {
        goals.push(c);
    }

    let mut grid = String::new();
    let mut g_idx = 0usize;
    let mut ng_idx = 0usize;
    for (is_nongoal, title, body) in &goals {
        let (cls, mark, idx) = if *is_nongoal {
            ng_idx += 1;
            ("goal goal--non", "Non-goal", ng_idx)
        } else {
            g_idx += 1;
            ("goal", "Goal", g_idx)
        };
        grid.push_str(&format!(
            "<div class='{cls}'>
              <span class='goal__mark'>{mark}</span>
              <h3 class='goal__title'><span class='idx'>{idx_str}</span>{title}</h3>
              <div class='goal__body'>{body}</div>
            </div>",
            idx_str = pad2(idx),
        ));
    }

    format!(
        "<section class='section' id='goals'>
          <div class='shell'>
            <div class='section__head'>
              <div class='section__num'>01</div>
              <h2 class='section__title'>{h1}<span class='small'>{subtitle}</span></h2>
              <div class='section__meta'></div>
            </div>
            <div class='goals'>{grid}</div>
          </div>
        </section>"
    )
}

// ── Tour ────────────────────────────────────────────────────────────
fn render_tour(md: &str) -> String {
    let arena = Arena::new();
    let opts = comrak_opts();
    let root = parse_document(&arena, md, &opts);

    struct Item {
        bonus: bool,
        id: String,
        title: String,
        prose: String,
        code: String,
        code_norun: bool,
        extra_code: Vec<(bool, String)>, // additional code blocks (is_norun, literal)
    }

    let mut h1 = String::new();
    let mut subtitle = String::new();
    let mut saw_h1 = false;
    let mut items: Vec<Item> = Vec::new();
    let mut pending_bonus = false;
    let mut current: Option<Item> = None;

    let slug = |s: &str| -> String {
        let mut out = String::with_capacity(s.len());
        let mut last_dash = true;
        for c in s.chars() {
            if c.is_ascii_alphanumeric() {
                out.push(c.to_ascii_lowercase());
                last_dash = false;
            } else if !last_dash {
                out.push('-');
                last_dash = true;
            }
        }
        out.trim_end_matches('-').to_string()
    };

    for child in root.children() {
        let value = child.data.borrow().value.clone();
        match value {
            NodeValue::Heading(h) if h.level == 1 => {
                h1 = render_inline(child);
                saw_h1 = true;
            }
            NodeValue::Heading(h) if h.level == 2 => {
                if let Some(it) = current.take() {
                    items.push(it);
                }
                let title = render_inline(child);
                let id = slug(&text_of(child));
                current = Some(Item {
                    bonus: pending_bonus,
                    id,
                    title,
                    prose: String::new(),
                    code: String::new(),
                    code_norun: false,
                    extra_code: Vec::new(),
                });
                pending_bonus = false;
            }
            NodeValue::Paragraph => {
                if let Some(it) = current.as_mut() {
                    it.prose.push_str(&render_block(child));
                } else if saw_h1 && subtitle.is_empty() {
                    subtitle = render_inline(child);
                }
            }
            NodeValue::CodeBlock(block) => {
                let is_norun = block.info.contains("norun");
                if let Some(it) = current.as_mut() {
                    if it.code.is_empty() && !is_norun {
                        it.code = block.literal.clone();
                    } else {
                        it.extra_code.push((is_norun, block.literal.clone()));
                    }
                }
            }
            NodeValue::HtmlBlock(block) => {
                if block.literal.contains("bonus") {
                    pending_bonus = true;
                }
            }
            _ => {}
        }
    }
    if let Some(it) = current.take() {
        items.push(it);
    }

    let mut nav = String::new();
    let mut body = String::new();
    let mut nav_index = 0usize;
    for it in &items {
        let primary = if it.code.is_empty() {
            String::new()
        } else if it.code_norun {
            norun_snippet(&it.code, &format!("{}.tlk", it.id))
        } else {
            runnable_snippet(&it.code, &format!("{}.tlk", it.id))
        };
        let mut extras = String::new();
        for (is_norun, code) in &it.extra_code {
            let rendered = if *is_norun {
                norun_snippet(code, &format!("{}.tlk", it.id))
            } else {
                runnable_snippet(code, &format!("{}.tlk", it.id))
            };
            extras.push_str(&rendered);
        }

        if !it.bonus {
            nav_index += 1;
            nav.push_str(&format!(
                "<li data-target='tour-{id}'{active}><span class='n'>{n}</span><span>{title}</span></li>",
                id = it.id,
                n = pad2(nav_index),
                title = it.title,
                active = if nav_index == 1 { " class='is-active'" } else { "" },
            ));
        }

        body.push_str(&format!(
            "<div class='tour__item' id='tour-{id}'>
              <h3>{title}</h3>
              {prose}
              {primary}
              {extras}
            </div>",
            id = it.id,
            title = it.title,
            prose = it.prose,
        ));
    }

    format!(
        "<section class='section' id='tour'>
          <div class='shell'>
            <div class='section__head'>
              <div class='section__num'>02</div>
              <h2 class='section__title'>{h1}<span class='small'>{subtitle}</span></h2>
              <div class='section__meta'></div>
            </div>
            <div class='tour'>
              <aside class='tour__nav'><ol>{nav}</ol></aside>
              <div class='tour__body'>{body}</div>
            </div>
          </div>
        </section>"
    )
}

// ── Pipeline ────────────────────────────────────────────────────────
fn render_pipeline(md: &str) -> String {
    let arena = Arena::new();
    let opts = comrak_opts();
    let root = parse_document(&arena, md, &opts);

    struct Stage {
        name: String,
        hint: String,
        input: String,
        output: String,
    }

    let mut h1 = String::new();
    let mut subtitle = String::new();
    let mut saw_h1 = false;
    let mut stages: Vec<Stage> = Vec::new();
    let mut current: Option<Stage> = None;

    for child in root.children() {
        let value = child.data.borrow().value.clone();
        match value {
            NodeValue::Heading(h) if h.level == 1 => {
                h1 = render_inline(child);
                saw_h1 = true;
            }
            NodeValue::Heading(h) if h.level == 2 => {
                if let Some(s) = current.take() {
                    stages.push(s);
                }
                current = Some(Stage {
                    name: render_inline(child),
                    hint: String::new(),
                    input: String::new(),
                    output: String::new(),
                });
            }
            NodeValue::Paragraph => {
                if let Some(s) = current.as_mut() {
                    if s.hint.is_empty() {
                        s.hint = render_inline(child);
                    }
                } else if saw_h1 && subtitle.is_empty() {
                    subtitle = render_inline(child);
                }
            }
            NodeValue::CodeBlock(block) => {
                if let Some(s) = current.as_mut() {
                    let info = block.info.trim();
                    if info == "in" {
                        s.input = block.literal.clone();
                    } else if info == "out" {
                        s.output = block.literal.clone();
                    }
                }
            }
            _ => {}
        }
    }
    if let Some(s) = current.take() {
        stages.push(s);
    }

    let mut strip = String::new();
    for (i, s) in stages.iter().enumerate() {
        let active = if i == 0 { " is-active" } else { "" };
        strip.push_str(&format!(
            "<div class='pipeline__stage{active}' data-idx='{i}' data-name='{name}' data-in='{input}' data-out='{output}'>
              <div class='pipeline__num'>Step {step}</div>
              <div class='pipeline__name'>{name}</div>
              <div class='pipeline__hint'>{hint}</div>
              <div class='pipeline__arrow'>→</div>
            </div>",
            name = escape_html(&s.name),
            input = escape_html(s.input.trim_end_matches(&['\n', '\r'][..])),
            output = escape_html(s.output.trim_end_matches(&['\n', '\r'][..])),
            step = pad2(i + 1),
            hint = s.hint,
        ));
    }

    let (first_in_label, first_in, first_out_label, first_out) = if let Some(s) = stages.first() {
        (
            "source".to_string(),
            escape_html(s.input.trim_end_matches(&['\n', '\r'][..])),
            s.name.clone(),
            escape_html(s.output.trim_end_matches(&['\n', '\r'][..])),
        )
    } else {
        (String::new(), String::new(), String::new(), String::new())
    };

    format!(
        "<section class='section' id='pipeline'>
          <div class='shell'>
            <div class='section__head'>
              <div class='section__num'>03</div>
              <h2 class='section__title'>{h1}<span class='small'>{subtitle}</span></h2>
              <div class='section__meta'></div>
            </div>
            <div class='pipeline'>{strip}</div>
            <div class='pipeline-view'>
              <div class='pipeline-view__panel'>
                <h4>In · <span data-slot='in-label'>{first_in_label}</span></h4>
                <pre data-slot='in'>{first_in}</pre>
              </div>
              <div class='pipeline-view__panel'>
                <h4>Out · <span data-slot='out-label'>{first_out_label}</span></h4>
                <pre data-slot='out'>{first_out}</pre>
              </div>
            </div>
          </div>
        </section>
        <script>
        (function() {{
          const stages = document.querySelectorAll('.pipeline__stage');
          const inLabel  = document.querySelector('[data-slot=\"in-label\"]');
          const outLabel = document.querySelector('[data-slot=\"out-label\"]');
          const inPre    = document.querySelector('[data-slot=\"in\"]');
          const outPre   = document.querySelector('[data-slot=\"out\"]');
          stages.forEach((stage, idx) => {{
            stage.addEventListener('click', () => {{
              stages.forEach(s => s.classList.remove('is-active'));
              stage.classList.add('is-active');
              const prev = idx > 0 ? stages[idx-1].dataset.name : 'source';
              inLabel.textContent  = prev;
              outLabel.textContent = stage.dataset.name;
              inPre.textContent    = stage.dataset.in;
              outPre.textContent   = stage.dataset.out;
            }});
          }});
        }})();
        </script>"
    )
}

// ── Roadmap ─────────────────────────────────────────────────────────
fn render_roadmap(md: &str) -> String {
    let arena = Arena::new();
    let opts = comrak_opts();
    let root = parse_document(&arena, md, &opts);

    let mut h1 = String::new();
    let mut subtitle = String::new();
    let mut saw_h1 = false;
    let mut items: Vec<(String, String, String)> = Vec::new(); // title, status, body
    let mut current: Option<(String, String, String)> = None;

    for child in root.children() {
        let value = child.data.borrow().value.clone();
        match value {
            NodeValue::Heading(h) if h.level == 1 => {
                h1 = render_inline(child);
                saw_h1 = true;
            }
            NodeValue::Heading(h) if h.level == 3 => {
                if let Some(c) = current.take() {
                    items.push(c);
                }
                let raw = render_inline(child);
                // Extract trailing [status]
                let (title, status) = if let (Some(lb), Some(rb)) = (raw.rfind('['), raw.rfind(']')) {
                    if rb > lb {
                        let status = raw[lb + 1..rb].trim().to_string();
                        let title = raw[..lb].trim().to_string();
                        (title, status)
                    } else {
                        (raw.clone(), "missing".to_string())
                    }
                } else {
                    (raw.clone(), "missing".to_string())
                };
                current = Some((title, status, String::new()));
            }
            NodeValue::Paragraph => {
                let html = render_block(child);
                if let Some(c) = current.as_mut() {
                    c.2.push_str(&html);
                } else if saw_h1 && subtitle.is_empty() {
                    subtitle = render_inline(child);
                }
            }
            _ => {}
        }
    }
    if let Some(c) = current.take() {
        items.push(c);
    }

    let mut grid = String::new();
    for (title, status, body) in &items {
        grid.push_str(&format!(
            "<div class='roadmap__item' data-status='{status}'>
              <span class='roadmap__tag'>{tag}</span>
              <h4 class='roadmap__title'>{title}</h4>
              <div class='roadmap__body'>{body}</div>
            </div>",
            tag = status.to_uppercase(),
        ));
    }

    format!(
        "<section class='section' id='roadmap'>
          <div class='shell'>
            <div class='section__head'>
              <div class='section__num'>04</div>
              <h2 class='section__title'>{h1}<span class='small'>{subtitle}</span></h2>
              <div class='section__meta'></div>
            </div>
            <div class='roadmap'>{grid}</div>
          </div>
        </section>"
    )
}

// ── Install ─────────────────────────────────────────────────────────
fn render_install(md: &str) -> String {
    let arena = Arena::new();
    let opts = comrak_opts();
    let root = parse_document(&arena, md, &opts);

    let mut h1 = String::new();
    let mut subtitle = String::new();
    let mut saw_h1 = false;
    let mut terminal = String::new();
    let mut steps_html = String::new();

    for child in root.children() {
        let value = child.data.borrow().value.clone();
        match value {
            NodeValue::Heading(h) if h.level == 1 => {
                h1 = render_inline(child);
                saw_h1 = true;
            }
            NodeValue::Paragraph if saw_h1 && subtitle.is_empty() => {
                subtitle = render_inline(child);
            }
            NodeValue::CodeBlock(block) => {
                terminal = block.literal.clone();
            }
            NodeValue::List(_) => {
                // Render the list's children as <ol>
                let mut inner = String::new();
                for item in child.children() {
                    let mut item_html = String::new();
                    for c in item.children() {
                        item_html.push_str(&render_block(c));
                    }
                    // Strip <p> wrapping inside list items
                    let stripped = if let Some(rest) = item_html.trim().strip_prefix("<p>") {
                        if let Some(core) = rest.strip_suffix("</p>\n") {
                            core.trim().to_string()
                        } else if let Some(core) = rest.strip_suffix("</p>") {
                            core.trim().to_string()
                        } else {
                            item_html.trim().to_string()
                        }
                    } else {
                        item_html.trim().to_string()
                    };
                    inner.push_str(&format!("<li>{stripped}</li>"));
                }
                steps_html = inner;
            }
            _ => {}
        }
    }

    // Format the terminal lines: $ prompts dim, indented lines dim (help/notes),
    // non-indented non-$ lines are accent-colored (command output).
    let mut term_html = String::new();
    for line in terminal.lines() {
        if line.is_empty() {
            term_html.push_str("<div>&nbsp;</div>");
        } else if let Some(rest) = line.strip_prefix("$ ") {
            term_html.push_str(&format!(
                "<div><span class='p'>$</span> {}</div>",
                escape_html(rest)
            ));
        } else if line.starts_with(' ') || line.starts_with('\t') {
            term_html.push_str(&format!(
                "<div class='p'>{}</div>",
                escape_html(line)
            ));
        } else {
            term_html.push_str(&format!(
                "<div><span class='ok'>{}</span></div>",
                escape_html(line)
            ));
        }
    }

    format!(
        "<section class='section' id='install'>
          <div class='shell'>
            <div class='section__head'>
              <div class='section__num'>05</div>
              <h2 class='section__title'>{h1}<span class='small'>{subtitle}</span></h2>
              <div class='section__meta'></div>
            </div>
            <div class='install'>
              <div class='install-card'>
                <div class='install-card__head'>
                  <span>~/code</span><span>zsh</span>
                </div>
                <div class='install-card__body'>{term_html}</div>
              </div>
              <div class='install-card'>
                <div class='install-card__head'>
                  <span>first steps</span><span>do these in order</span>
                </div>
                <ol class='install-steps'>{steps_html}</ol>
              </div>
            </div>
          </div>
        </section>"
    )
}

// These helpers are referenced indirectly to keep warnings quiet.
#[allow(dead_code)]
fn _unused_markers<'a>(n: &'a AstNode<'a>) {
    let _ = code_block(n);
    let _ = text_of(n);
    let _ = heading_level(n);
}
