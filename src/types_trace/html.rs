//! HTML generation for type visualization.

use std::collections::BTreeMap;

use crate::node_id::{FileID, NodeID};
use crate::types::types::TypeEntry;

use super::TypesVisualization;

/// Generate the complete HTML visualization.
pub fn generate(viz: &TypesVisualization) -> String {
    let mut html = String::new();

    html.push_str(HTML_HEAD);
    html.push_str("<main>\n");

    // Header
    html.push_str("<header class=\"page-header\">\n");
    html.push_str("  <div>\n");
    html.push_str("    <p class=\"eyebrow\">Type Checker</p>\n");
    html.push_str("    <h1>Types Visualization</h1>\n");
    html.push_str(&format!(
        "    <p class=\"subtitle\">{} nodes with types</p>\n",
        viz.types.types_by_node.len()
    ));
    html.push_str("  </div>\n");
    html.push_str("</header>\n");

    // Two-panel layout
    html.push_str("<div class=\"panels\">\n");

    // Source panel
    html.push_str("<section class=\"source-panel\">\n");
    html.push_str("  <div class=\"section-header\">\n");
    html.push_str("    <h2>Source</h2>\n");
    html.push_str("  </div>\n");

    // File tabs
    if viz.sources.len() > 1 {
        html.push_str("  <div class=\"file-tabs\">\n");
        for (i, (path, _)) in viz.sources.iter().enumerate() {
            let name = path.file_name().map(|n| n.to_string_lossy()).unwrap_or_default();
            let active = if i == 0 { " active" } else { "" };
            html.push_str(&format!(
                "    <button class=\"file-tab{}\" data-file=\"{}\">{}</button>\n",
                active, i, escape_html(&name)
            ));
        }
        html.push_str("  </div>\n");
    }

    // File contents with type annotations
    for (file_idx, (path, source)) in viz.sources.iter().enumerate() {
        let display = if file_idx == 0 { "block" } else { "none" };
        let name = path.file_name().map(|n| n.to_string_lossy()).unwrap_or_default();
        let file_id = FileID(file_idx as u32);

        html.push_str(&format!(
            "  <div class=\"file-content\" data-file=\"{}\" style=\"display: {}\">\n",
            file_idx, display
        ));
        html.push_str(&format!("    <h3>{}</h3>\n", escape_html(&name)));
        html.push_str("    <pre class=\"source\"><code>");

        // Collect spans for this file, sorted by position
        let mut spans_in_file: Vec<_> = viz
            .node_spans
            .iter()
            .filter(|(node_id, span)| node_id.0 == file_id && span.start < source.len() as u32)
            .collect();
        spans_in_file.sort_by_key(|(_, span)| (span.start, std::cmp::Reverse(span.end)));

        // Build a map of byte offset -> list of (node_id, is_start)
        let mut events: BTreeMap<u32, Vec<(NodeID, bool)>> = BTreeMap::new();
        for (node_id, span) in &spans_in_file {
            events.entry(span.start).or_default().push((**node_id, true));
            events.entry(span.end).or_default().push((**node_id, false));
        }

        // Render source with type spans
        let mut cursor = 0u32;
        let mut open_spans: Vec<NodeID> = Vec::new();
        let source_bytes = source.as_bytes();

        for (pos, node_events) in events {
            // Output text before this position
            if pos > cursor && (cursor as usize) < source.len() {
                let end = (pos as usize).min(source.len());
                if let Ok(text) = std::str::from_utf8(&source_bytes[cursor as usize..end]) {
                    html.push_str(&escape_html(text));
                }
                cursor = pos;
            }

            // Process events at this position (closes first, then opens)
            // Sort: closes before opens, and for opens, larger spans first
            let mut closes: Vec<NodeID> = Vec::new();
            let mut opens: Vec<NodeID> = Vec::new();
            for (node_id, is_start) in node_events {
                if is_start {
                    opens.push(node_id);
                } else {
                    closes.push(node_id);
                }
            }

            // Close spans (in reverse order of opening)
            for node_id in closes {
                if let Some(idx) = open_spans.iter().rposition(|n| *n == node_id) {
                    // Close all spans from the end to this one
                    for _ in idx..open_spans.len() {
                        html.push_str("</span>");
                    }
                    open_spans.truncate(idx);
                }
            }

            // Open spans
            for node_id in opens {
                let type_str = viz
                    .types
                    .types_by_node
                    .get(&node_id)
                    .map(|t| format_type_entry(t))
                    .unwrap_or_else(|| "?".to_string());

                html.push_str(&format!(
                    "<span class=\"typed-node\" data-node=\"{}:{}\" data-type=\"{}\">",
                    node_id.0 .0,
                    node_id.1,
                    escape_html(&type_str)
                ));
                open_spans.push(node_id);
            }
        }

        // Output remaining text
        if (cursor as usize) < source.len() {
            if let Ok(text) = std::str::from_utf8(&source_bytes[cursor as usize..]) {
                html.push_str(&escape_html(text));
            }
        }

        // Close any remaining open spans
        for _ in &open_spans {
            html.push_str("</span>");
        }

        html.push_str("</code></pre>\n");
        html.push_str("  </div>\n");
    }

    html.push_str("</section>\n");

    // Type info panel
    html.push_str("<section class=\"type-panel\">\n");
    html.push_str("  <div class=\"section-header\">\n");
    html.push_str("    <h2>Type Info</h2>\n");
    html.push_str("  </div>\n");
    html.push_str("  <div class=\"type-info\" id=\"type-info\">\n");
    html.push_str("    <p class=\"hint\">Hover over code to see types</p>\n");
    html.push_str("  </div>\n");
    html.push_str("</section>\n");

    html.push_str("</div>\n"); // panels
    html.push_str("</main>\n");
    html.push_str(HTML_SCRIPT);
    html.push_str("</body>\n</html>\n");

    html
}

fn format_type_entry(entry: &TypeEntry) -> String {
    match entry {
        TypeEntry::Mono(ty) => format!("{}", ty),
        TypeEntry::Poly(scheme) => {
            if scheme.foralls.is_empty() {
                format!("{}", scheme.ty)
            } else {
                format!("∀{:?}. {}", scheme.foralls, scheme.ty)
            }
        }
    }
}

fn escape_html(text: &str) -> String {
    let mut result = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '&' => result.push_str("&amp;"),
            '<' => result.push_str("&lt;"),
            '>' => result.push_str("&gt;"),
            '"' => result.push_str("&quot;"),
            '\'' => result.push_str("&#39;"),
            _ => result.push(ch),
        }
    }
    result
}

const HTML_HEAD: &str = r#"<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Types Visualization</title>
  <style>
    :root {
      --bg: #1a1a2e;
      --bg-accent: #16213e;
      --panel: #0f0f23;
      --ink: #e8e8e8;
      --muted: #888;
      --accent: #00d9ff;
      --accent-2: #ff6b6b;
      --hover: rgba(0, 217, 255, 0.15);
      --line: rgba(255, 255, 255, 0.1);
    }
    * { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      background: var(--bg);
      color: var(--ink);
      font-family: "JetBrains Mono", "Fira Code", monospace;
      font-size: 13px;
      line-height: 1.6;
    }
    main {
      max-width: 1800px;
      margin: 0 auto;
      padding: 20px;
    }
    .page-header {
      margin-bottom: 20px;
      padding-bottom: 20px;
      border-bottom: 1px solid var(--line);
    }
    .eyebrow {
      text-transform: uppercase;
      letter-spacing: 0.2em;
      font-size: 11px;
      color: var(--accent);
      margin-bottom: 4px;
    }
    h1 { font-size: 24px; font-weight: 600; }
    h2 { font-size: 16px; font-weight: 600; margin-bottom: 12px; }
    h3 { font-size: 14px; font-weight: 600; color: var(--muted); margin-bottom: 8px; }
    .subtitle { color: var(--muted); font-size: 13px; }
    .panels {
      display: grid;
      grid-template-columns: 2fr 1fr;
      gap: 20px;
      height: calc(100vh - 140px);
    }
    section {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 16px;
      overflow: hidden;
      display: flex;
      flex-direction: column;
    }
    .section-header {
      margin-bottom: 12px;
      flex-shrink: 0;
    }
    .file-tabs {
      display: flex;
      gap: 4px;
      margin-bottom: 12px;
      flex-shrink: 0;
    }
    .file-tab {
      background: transparent;
      border: 1px solid var(--line);
      color: var(--muted);
      padding: 6px 12px;
      border-radius: 4px;
      cursor: pointer;
      font-size: 12px;
    }
    .file-tab.active {
      background: var(--accent);
      color: var(--bg);
      border-color: var(--accent);
    }
    .file-content { overflow: auto; flex: 1; }
    .source {
      background: var(--bg-accent);
      padding: 12px;
      border-radius: 4px;
      overflow-x: auto;
      font-size: 13px;
      line-height: 1.6;
    }
    .source code { display: block; white-space: pre; }
    .typed-node {
      cursor: pointer;
      border-radius: 2px;
      transition: background 0.1s;
    }
    .typed-node:hover {
      background: var(--hover);
    }
    .typed-node.selected {
      background: rgba(0, 217, 255, 0.3);
      outline: 1px solid var(--accent);
    }
    .type-panel {
      overflow: auto;
    }
    .type-info {
      flex: 1;
      overflow: auto;
    }
    .hint {
      color: var(--muted);
      font-style: italic;
    }
    .type-display {
      background: var(--bg-accent);
      padding: 12px;
      border-radius: 4px;
      margin-bottom: 12px;
    }
    .type-display h4 {
      color: var(--accent);
      font-size: 12px;
      margin-bottom: 8px;
    }
    .type-display pre {
      white-space: pre-wrap;
      word-break: break-all;
    }
    .node-id {
      color: var(--muted);
      font-size: 11px;
    }
  </style>
</head>
<body>
"#;

const HTML_SCRIPT: &str = r#"
<script>
const typeInfo = document.getElementById('type-info');
let selectedNode = null;

document.querySelectorAll('.typed-node').forEach(node => {
  node.addEventListener('mouseenter', function() {
    showTypeInfo(this);
  });

  node.addEventListener('click', function(e) {
    e.stopPropagation();
    if (selectedNode) {
      selectedNode.classList.remove('selected');
    }
    this.classList.add('selected');
    selectedNode = this;
    showTypeInfo(this, true);
  });
});

document.addEventListener('click', function() {
  if (selectedNode) {
    selectedNode.classList.remove('selected');
    selectedNode = null;
  }
});

function showTypeInfo(node, pinned = false) {
  const nodeId = node.dataset.node;
  const type = node.dataset.type;
  const code = node.textContent.substring(0, 100) + (node.textContent.length > 100 ? '...' : '');

  typeInfo.innerHTML = `
    <div class="type-display">
      <h4>Expression</h4>
      <pre>${escapeHtml(code)}</pre>
    </div>
    <div class="type-display">
      <h4>Type</h4>
      <pre>${escapeHtml(type)}</pre>
    </div>
    <p class="node-id">NodeID: ${nodeId}</p>
    ${pinned ? '<p class="hint">Click elsewhere to deselect</p>' : ''}
  `;
}

function escapeHtml(text) {
  const div = document.createElement('div');
  div.textContent = text;
  return div.innerHTML;
}

// File tabs
document.querySelectorAll('.file-tab').forEach(tab => {
  tab.addEventListener('click', function() {
    const fileIndex = this.dataset.file;
    document.querySelectorAll('.file-tab').forEach(t => t.classList.remove('active'));
    document.querySelectorAll('.file-content').forEach(c => c.style.display = 'none');
    this.classList.add('active');
    document.querySelector(`.file-content[data-file="${fileIndex}"]`).style.display = 'block';
  });
});
</script>
"#;
