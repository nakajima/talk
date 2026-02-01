use std::io::IsTerminal;

use crate::{
    analysis::{Diagnostic, DiagnosticSeverity},
    common::text::{clamp_to_char_boundary, line_info_for_offset, line_info_for_offset_utf16},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColorMode {
    Auto,
    Always,
    Never,
}

pub fn render_text(
    doc_id: &str,
    text: &str,
    diagnostic: &Diagnostic,
    color_mode: ColorMode,
) -> String {
    // Could be chill to use miette or something for this
    let use_color = match color_mode {
        ColorMode::Auto => {
            std::io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none()
        }
        ColorMode::Always => true,
        ColorMode::Never => false,
    };
    let (line, col, line_start, line_end) = line_info_for_offset(text, diagnostic.range.start);
    let line_text = text.get(line_start..line_end).unwrap_or("");
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);

    let highlight_start =
        clamp_to_char_boundary(text, diagnostic.range.start as usize).clamp(line_start, line_end);
    let highlight_end = clamp_to_char_boundary(text, diagnostic.range.end as usize)
        .clamp(highlight_start, line_end);

    let prefix = caret_prefix(&text[line_start..highlight_start]);
    let underline_len = text[highlight_start..highlight_end].chars().count().max(1);
    let underline = "^".repeat(underline_len);

    let severity = severity_label(&diagnostic.severity);
    let severity_style = severity_style(&diagnostic.severity);
    let severity = style(severity, severity_style, use_color);

    let gutter = style("|", "2", use_color);
    let line_no = style(&format!("{line:>4}"), "2", use_color);
    let underline = style(&underline, severity_style, use_color);

    let mut output = String::new();
    output.push_str(&format!(
        "{doc_id}:{line}:{col}: {severity}: {}\n",
        diagnostic.message
    ));
    output.push_str(&format!("  {gutter}\n"));
    output.push_str(&format!("{line_no} {gutter} {line_text}\n"));
    output.push_str(&format!("  {gutter} {prefix}{underline}\n"));

    if diagnostic.range.end as usize > line_end {
        output.push_str("  = note: spans multiple lines\n");
    }

    output.push('\n');
    output
}

pub fn render_json_entry(doc_id: &str, text: &str, diagnostic: &Diagnostic) -> String {
    let (line, col, line_start, line_end) =
        line_info_for_offset_utf16(text, diagnostic.range.start);
    let line_text = text.get(line_start..line_end).unwrap_or("");
    let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);

    let highlight_start =
        clamp_to_char_boundary(text, diagnostic.range.start as usize).clamp(line_start, line_end);
    let highlight_end = clamp_to_char_boundary(text, diagnostic.range.end as usize)
        .clamp(highlight_start, line_end);

    let underline_start = text[line_start..highlight_start].encode_utf16().count() as u32 + 1;
    let underline_len = text[highlight_start..highlight_end]
        .encode_utf16()
        .count()
        .max(1) as u32;
    let multiline = diagnostic.range.end as usize > line_end;

    // Pro: Don't need to pull in a dep like serde. Con: Look at this nonsense.
    format!(
        "{{\"path\":{},\"line\":{},\"column\":{},\"severity\":{},\"message\":{},\"range\":{{\"start\":{},\"end\":{}}},\"line_text\":{},\"underline_start\":{},\"underline_len\":{},\"multiline\":{}}}",
        json_string(doc_id),
        line,
        col,
        json_string(severity_label(&diagnostic.severity)),
        json_string(&diagnostic.message),
        diagnostic.range.start,
        diagnostic.range.end,
        json_string(line_text),
        underline_start,
        underline_len,
        if multiline { "true" } else { "false" }
    )
}

pub fn render_json_output(entries: &[String]) -> String {
    format!("{{\"diagnostics\":[{}]}}", entries.join(","))
}

fn severity_label(severity: &DiagnosticSeverity) -> &'static str {
    match severity {
        DiagnosticSeverity::Error => "error",
        DiagnosticSeverity::Warning => "warning",
        DiagnosticSeverity::Info => "info",
    }
}

fn severity_style(severity: &DiagnosticSeverity) -> &'static str {
    match severity {
        DiagnosticSeverity::Error => "1;31",
        DiagnosticSeverity::Warning => "1;33",
        DiagnosticSeverity::Info => "1;34",
    }
}

fn style(text: &str, code: &str, enabled: bool) -> String {
    if enabled {
        format!("\x1b[{code}m{text}\x1b[0m")
    } else {
        text.to_string()
    }
}

fn caret_prefix(text: &str) -> String {
    let mut prefix = String::new();
    for ch in text.chars() {
        if ch == '\t' {
            prefix.push('\t');
        } else {
            prefix.push(' ');
        }
    }
    prefix
}

fn json_string(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if (ch as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", ch as u32));
            }
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}
