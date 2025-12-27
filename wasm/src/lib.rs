use js_sys::{Array, Object, Reflect};
use talk::{
    analysis::{Diagnostic, DocumentInput, Workspace},
    common::text::{clamp_to_char_boundary, line_info_for_offset_utf16},
    compiling::driver::{Driver, DriverConfig, Lowered, Source},
    formatter,
    highlighter::highlight_html as highlight_source_html,
    ir::{
        highlighter::highlight_html as highlight_ir_html,
        interpreter::Interpreter,
        io::{CaptureIO, IO, IOError, MultiWriteIO},
    },
    name_resolution::symbol::set_symbol_names,
};
use wasm_bindgen::prelude::*;

#[derive(Default)]
pub struct ConsoleIO {}
impl IO for ConsoleIO {
    fn write_stdout(&mut self, bytes: &[u8]) -> Result<(), talk::ir::io::IOError> {
        let string = str::from_utf8(bytes).map_err(|e| IOError::WriteError(format!("{e:?}")))?;
        web_sys::console::log_1(&JsValue::from_str(string));
        Ok(())
    }

    fn write_stderr(&mut self, bytes: &[u8]) -> Result<(), talk::ir::io::IOError> {
        let string = str::from_utf8(bytes).map_err(|e| IOError::WriteError(format!("{e:?}")))?;
        web_sys::console::error_1(&JsValue::from_str(string));
        Ok(())
    }

    fn read_stdio(&mut self, _bytes: &mut [u8]) -> Result<usize, talk::ir::io::IOError> {
        Err(IOError::Unsupported)
    }
}

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
    let lowered = compile_source(source)?;
    let display_names = lowered.display_symbol_names();
    let module = lowered.module("talk");
    let mut capture = CaptureIO::default();
    let mut console = ConsoleIO::default();
    let io = MultiWriteIO {
        adapters: vec![Box::new(&mut capture), Box::new(&mut console)],
    };
    let mut interpreter = Interpreter::new(module.program, Some(display_names), io);
    let result = interpreter.run();

    let obj = Object::new();
    let value = interpreter.display(result, true);
    let highlighted_value = highlight_source_html(&value);
    set_str(&obj, "value", &value)?;
    set_str(&obj, "highlightedValue", &highlighted_value)?;
    set_str(
        &obj,
        "output",
        str::from_utf8(&capture.stdout).map_err(|e| JsValue::from_str(&format!("{e:?}")))?,
    )?;

    Ok(obj)
}

#[wasm_bindgen]
pub fn show_ir(source: &str) -> Result<Object, JsValue> {
    init();
    let lowered = compile_source(source)?;
    let display_names = lowered.display_symbol_names();
    let _guard = set_symbol_names(display_names);
    let ir = format!("{}", lowered.module("WASM").program);
    let highlighted_ir = highlight_ir_html(&ir);

    let obj = Object::new();
    set_str(&obj, "ir", &ir)?;
    set_str(&obj, "highlightedIr", &highlighted_ir)?;
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
pub fn version() -> String {
    init();
    env!("CARGO_PKG_VERSION").to_string()
}

type LoweredDriver = Driver<Lowered>;

fn compile_source(source: &str) -> Result<LoweredDriver, JsValue> {
    let driver = Driver::new(
        vec![Source::from(source)],
        DriverConfig::new("_").executable(),
    );

    driver
        .parse()
        .map_err(to_js_error)?
        .resolve_names()
        .map_err(to_js_error)?
        .typecheck()
        .map_err(to_js_error)?
        .lower()
        .map_err(to_js_error)
}

fn to_js_error(err: impl std::fmt::Debug) -> JsValue {
    JsValue::from_str(&format!("{err:?}"))
}

fn install_panic_hook() {
    console_error_panic_hook::set_once();
}

fn diagnostics_to_js(
    doc_id: &str,
    text: &str,
    diagnostics: &[Diagnostic],
) -> Result<JsValue, JsValue> {
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

    let root = Object::new();
    Reflect::set(&root, &JsValue::from_str("diagnostics"), &entries)?;
    Ok(root.into())
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
