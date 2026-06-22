use js_sys::{Array, Object, Reflect};
use talk::{
    analysis::{Diagnostic, DocumentInput, Workspace},
    common::text::{clamp_to_char_boundary, line_info_for_offset_utf16},
    formatter,
    highlighter::highlight_html as highlight_source_html,
    repl::{ReplEvalResult, ReplSession},
};
use wasm_bindgen::prelude::*;

fn init() {
    install_panic_hook();
}

#[wasm_bindgen]
pub fn format(source: &str) -> String {
    init();
    formatter::format_string(source)
}

#[wasm_bindgen]
pub fn run_program(source: &str) -> Result<Object, JsValue> {
    init();
    let session = ReplSession::with_source_path(std::path::PathBuf::from("playground.tlk"));
    match session.eval_program(source) {
        ReplEvalResult::Output { stdout, value, .. } => {
            let obj = Object::new();
            let value = value.unwrap_or_default();
            set_str(&obj, "value", &value)?;
            set_str(&obj, "highlightedValue", &highlight_source_html(&value))?;
            set_str(&obj, "output", &stdout)?;
            Ok(obj)
        }
        failure => Err(repl_result_to_js(failure)?.into()),
    }
}

#[wasm_bindgen]
pub fn show_ir(source: &str) -> Result<Object, JsValue> {
    init();
    let ir = talk::compiling::driver::render_lowered("Playground", source)
        .map_err(|message| JsValue::from_str(&message))?;
    let obj = Object::new();
    set_str(&obj, "ir", &ir)?;
    set_str(&obj, "highlightedIr", &highlight_source_html(&ir))?;
    Ok(obj)
}

#[wasm_bindgen]
pub fn highlight(source: &str) -> Result<String, JsValue> {
    init();
    Ok(highlight_source_html(source))
}

#[wasm_bindgen]
pub fn check(source: &str) -> Result<JsValue, JsValue> {
    init();
    let doc_id = "<stdin>".to_string();
    let docs = vec![DocumentInput {
        id: doc_id.clone(),
        path: doc_id.clone(),
        version: 0,
        text: source.to_string(),
    }];

    let workspace =
        Workspace::new(docs).ok_or_else(|| JsValue::from_str("failed to build workspace"))?;
    let diagnostics = workspace
        .diagnostics
        .get(&doc_id)
        .cloned()
        .unwrap_or_default();

    diagnostics_to_js(&doc_id, source, &diagnostics)
}

#[wasm_bindgen]
pub fn hover(
    source: &str,
    byte_offset: Option<u32>,
    line: Option<u32>,
    column: Option<u32>,
    node_id: Option<String>,
) -> Result<JsValue, JsValue> {
    init();
    let doc_id = "<stdin>".to_string();
    let docs = vec![DocumentInput {
        id: doc_id.clone(),
        path: doc_id.clone(),
        version: 0,
        text: source.to_string(),
    }];
    let workspace =
        Workspace::new(docs).ok_or_else(|| JsValue::from_str("failed to build workspace"))?;

    let hover = match (byte_offset, line, column, node_id) {
        (_, _, _, Some(node_id)) => {
            let node_id = talk::analysis::hover::parse_node_id(&node_id)
                .ok_or_else(|| JsValue::from_str("node id must be \"index\" or \"file:index\""))?;
            talk::analysis::hover::hover_for_node_id(&workspace, &doc_id, node_id)
        }
        (Some(offset), None, None, None) => {
            if offset as usize > source.len() {
                return Err(JsValue::from_str("byte offset is past end of document"));
            }
            let offset = clamp_to_char_boundary(source, offset as usize) as u32;
            talk::analysis::hover_at(&workspace, &doc_id, offset)
        }
        (None, Some(line), Some(column), None) => {
            let offset = talk::common::text::byte_offset_for_line_column_utf8(source, line, column)
                .ok_or_else(|| JsValue::from_str("line/column is past end of document"))?;
            talk::analysis::hover_at(&workspace, &doc_id, offset)
        }
        _ => {
            return Err(JsValue::from_str(
                "provide byte_offset, line and column, or node_id",
            ));
        }
    };
    hover_to_js(&doc_id, source, hover)
}

fn hover_to_js(
    doc_id: &str,
    text: &str,
    hover: Option<talk::analysis::Hover>,
) -> Result<JsValue, JsValue> {
    use talk::common::text::line_info_for_offset;

    let root = Object::new();
    set_str(&root, "path", doc_id)?;
    let Some(hover) = hover else {
        Reflect::set(&root, &JsValue::from_str("hover"), &JsValue::NULL)?;
        return Ok(root.into());
    };

    let hover_obj = Object::new();
    set_str(&hover_obj, "contents", &hover.contents)?;
    let contents_markdown = format!("```talk\n{}\n```", hover.contents);
    set_str(&hover_obj, "contents_markdown", &contents_markdown)?;

    let (start_line, start_col, _, _) = line_info_for_offset(text, hover.range.start);
    let (end_line, end_col, _, _) = line_info_for_offset(text, hover.range.end);
    let range_obj = Object::new();
    let start_obj = Object::new();
    set_num(&start_obj, "byte", hover.range.start)?;
    set_num(&start_obj, "line", start_line)?;
    set_num(&start_obj, "column", start_col)?;
    let end_obj = Object::new();
    set_num(&end_obj, "byte", hover.range.end)?;
    set_num(&end_obj, "line", end_line)?;
    set_num(&end_obj, "column", end_col)?;
    Reflect::set(&range_obj, &JsValue::from_str("start"), &start_obj)?;
    Reflect::set(&range_obj, &JsValue::from_str("end"), &end_obj)?;
    Reflect::set(&hover_obj, &JsValue::from_str("range"), &range_obj)?;

    Reflect::set(&root, &JsValue::from_str("hover"), &hover_obj)?;
    Ok(root.into())
}

#[wasm_bindgen]
pub struct Repl {
    session: ReplSession,
}

#[wasm_bindgen]
impl Repl {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        init();
        Self {
            session: ReplSession::new(),
        }
    }

    pub fn reset(&mut self) {
        self.session.clear();
    }

    pub fn eval(&mut self, input: &str) -> Result<Object, JsValue> {
        repl_result_to_js(self.session.eval(input))
    }

    pub fn type_of(&self, input: &str) -> Result<Object, JsValue> {
        repl_result_to_js(self.session.type_of(input))
    }

    pub fn needs_more_input(&self, input: &str) -> bool {
        self.session.needs_more_input(input)
    }

    pub fn complete(&self, input: &str, byte_offset: u32) -> Result<Object, JsValue> {
        let completions = self.session.complete_input(input, byte_offset as usize);
        let root = Object::new();
        set_num(
            &root,
            "start",
            u32::try_from(completions.start).unwrap_or(u32::MAX),
        )?;
        let items = Array::new();
        for item in completions.items {
            let obj = Object::new();
            set_str(&obj, "display", &item.display)?;
            set_str(&obj, "replacement", &item.replacement)?;
            items.push(&obj);
        }
        Reflect::set(&root, &JsValue::from_str("items"), &items)?;
        Ok(root)
    }
}

impl Default for Repl {
    fn default() -> Self {
        Self::new()
    }
}

#[wasm_bindgen]
pub fn version() -> String {
    init();
    env!("CARGO_PKG_VERSION").to_string()
}

fn repl_result_to_js(result: ReplEvalResult) -> Result<Object, JsValue> {
    let obj = Object::new();
    match result {
        ReplEvalResult::Output {
            stdout,
            stderr,
            value,
        } => {
            set_str(&obj, "kind", "output")?;
            set_str(&obj, "stdout", &stdout)?;
            set_str(&obj, "stderr", &stderr)?;
            if let Some(value) = value {
                let highlighted_value = highlight_source_html(&value);
                set_str(&obj, "value", &value)?;
                set_str(&obj, "highlightedValue", &highlighted_value)?;
            } else {
                Reflect::set(&obj, &JsValue::from_str("value"), &JsValue::NULL)?;
                Reflect::set(&obj, &JsValue::from_str("highlightedValue"), &JsValue::NULL)?;
            }
        }
        ReplEvalResult::Diagnostics {
            source,
            diagnostics,
            message,
        } => {
            set_str(&obj, "kind", "diagnostics")?;
            set_str(&obj, "source", &source)?;
            if let Some(message) = message {
                set_str(&obj, "message", &message)?;
            } else {
                Reflect::set(&obj, &JsValue::from_str("message"), &JsValue::NULL)?;
            }
            let entries =
                diagnostics_array_to_js(talk::repl::REPL_DOCUMENT_ID, &source, &diagnostics)?;
            Reflect::set(&obj, &JsValue::from_str("diagnostics"), &entries)?;
        }
        ReplEvalResult::Error(message) => {
            set_str(&obj, "kind", "error")?;
            set_str(&obj, "message", &message)?;
        }
    }

    Ok(obj)
}

fn install_panic_hook() {
    console_error_panic_hook::set_once();
}

fn diagnostics_to_js(
    doc_id: &str,
    text: &str,
    diagnostics: &[Diagnostic],
) -> Result<JsValue, JsValue> {
    let entries = diagnostics_array_to_js(doc_id, text, diagnostics)?;
    let root = Object::new();
    Reflect::set(&root, &JsValue::from_str("diagnostics"), &entries)?;
    Ok(root.into())
}

fn diagnostics_array_to_js(
    doc_id: &str,
    text: &str,
    diagnostics: &[Diagnostic],
) -> Result<Array, JsValue> {
    let entries = Array::new();
    for diagnostic in diagnostics {
        let (line, col, line_start, line_end) =
            line_info_for_offset_utf16(text, diagnostic.range.start);
        let line_text = text.get(line_start..line_end).unwrap_or("");
        let line_text = line_text.strip_suffix('\r').unwrap_or(line_text);

        let highlight_start = clamp_to_char_boundary(text, diagnostic.range.start as usize)
            .clamp(line_start, line_end);
        let highlight_end = clamp_to_char_boundary(text, diagnostic.range.end as usize)
            .clamp(highlight_start, line_end);

        let underline_start = text[line_start..highlight_start].encode_utf16().count() as u32 + 1;
        let underline_len = text[highlight_start..highlight_end]
            .encode_utf16()
            .count()
            .max(1) as u32;
        let multiline = diagnostic.range.end as usize > line_end;

        let obj = Object::new();
        set_str(&obj, "path", doc_id)?;
        set_num(&obj, "line", line)?;
        set_num(&obj, "column", col)?;
        set_str(&obj, "severity", severity_label(&diagnostic.severity))?;
        set_str(&obj, "message", &diagnostic.message)?;
        set_str(&obj, "line_text", line_text)?;
        set_num(&obj, "underline_start", underline_start)?;
        set_num(&obj, "underline_len", underline_len)?;
        set_bool(&obj, "multiline", multiline)?;

        let range = Object::new();
        set_num(&range, "start", diagnostic.range.start)?;
        set_num(&range, "end", diagnostic.range.end)?;
        Reflect::set(&obj, &JsValue::from_str("range"), &range)?;

        entries.push(&obj);
    }

    Ok(entries)
}

fn severity_label(severity: &talk::analysis::DiagnosticSeverity) -> &'static str {
    match severity {
        talk::analysis::DiagnosticSeverity::Error => "error",
        talk::analysis::DiagnosticSeverity::Warning => "warning",
        talk::analysis::DiagnosticSeverity::Info => "info",
    }
}

fn set_str(obj: &Object, key: &str, value: &str) -> Result<(), JsValue> {
    Reflect::set(obj, &JsValue::from_str(key), &JsValue::from_str(value))?;
    Ok(())
}

fn set_num(obj: &Object, key: &str, value: u32) -> Result<(), JsValue> {
    Reflect::set(
        obj,
        &JsValue::from_str(key),
        &JsValue::from_f64(value as f64),
    )?;
    Ok(())
}

fn set_bool(obj: &Object, key: &str, value: bool) -> Result<(), JsValue> {
    Reflect::set(obj, &JsValue::from_str(key), &JsValue::from_bool(value))?;
    Ok(())
}
