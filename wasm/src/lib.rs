use js_sys::{Array, Object, Reflect};
use talk::{
    analysis::hover::{hover_at, hover_for_node_id},
    analysis::{Diagnostic, DocumentInput, Workspace},
    common::text::{
        byte_offset_for_line_column_utf8, clamp_to_char_boundary, line_info_for_offset,
        line_info_for_offset_utf16,
    },
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

    // File I/O not supported in WASM
    fn io_open(&mut self, _path: &[u8], _flags: i64, _mode: i64) -> i64 {
        -1 // EPERM
    }

    fn io_read(&mut self, _fd: i64, _buf: &mut [u8]) -> i64 {
        -1 // EPERM
    }

    fn io_write(&mut self, _fd: i64, _buf: &[u8]) -> i64 {
        -1 // EPERM
    }

    fn io_close(&mut self, _fd: i64) -> i64 {
        -1 // EPERM
    }

    fn io_ctl(&mut self, _fd: i64, _op: i64, _arg: i64) -> i64 {
        -1 // EPERM
    }

    fn io_poll(&mut self, _fds: &mut [(i32, i16, i16)], _timeout: i64) -> i64 {
        -1 // EPERM
    }

    fn io_socket(&mut self, _domain: i64, _socktype: i64, _protocol: i64) -> i64 {
        -1 // EPERM
    }

    fn io_bind(&mut self, _fd: i64, _addr: i64, _port: i64) -> i64 {
        -1 // EPERM
    }

    fn io_listen(&mut self, _fd: i64, _backlog: i64) -> i64 {
        -1 // EPERM
    }

    fn io_connect(&mut self, _fd: i64, _addr: i64, _port: i64) -> i64 {
        -1 // EPERM
    }

    fn io_accept(&mut self, _fd: i64) -> i64 {
        -1 // EPERM
    }

    fn io_sleep(&mut self, _ms: i64) -> i64 {
        // In WASM, we can't block, so this is a no-op
        0
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

    let query = parse_hover_query(byte_offset, line, column, node_id)?;
    let core = Workspace::core();
    let core = core.as_ref();
    let hover = match query {
        HoverQuery::ByteOffset(offset) => {
            if offset as usize > source.len() {
                return Err(JsValue::from_str("byte offset is past end of document"));
            }
            let offset = clamp_to_char_boundary(source, offset as usize);
            let offset = u32::try_from(offset).unwrap_or(u32::MAX);
            hover_at(&workspace, core, &doc_id, offset)
        }
        HoverQuery::LineColumn { line, column } => {
            let Some(offset) = byte_offset_for_line_column_utf8(source, line, column) else {
                return Err(JsValue::from_str("line/column out of range"));
            };
            hover_at(&workspace, core, &doc_id, offset)
        }
        HoverQuery::NodeId(node_id) => {
            if node_id.0 != talk::node_id::FileID(0) {
                return Err(JsValue::from_str("node id file index is out of range"));
            }
            hover_for_node_id(&workspace, core, &doc_id, node_id)
        }
    };

    hover_to_js(&doc_id, source, hover)
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

enum HoverQuery {
    ByteOffset(u32),
    LineColumn { line: u32, column: u32 },
    NodeId(talk::node_id::NodeID),
}

fn parse_hover_query(
    byte_offset: Option<u32>,
    line: Option<u32>,
    column: Option<u32>,
    node_id: Option<String>,
) -> Result<HoverQuery, JsValue> {
    let mut count = 0;
    if byte_offset.is_some() {
        count += 1;
    }
    if line.is_some() || column.is_some() {
        count += 1;
    }
    if node_id.is_some() {
        count += 1;
    }

    if count == 0 {
        return Err(JsValue::from_str(
            "provide byte_offset, line/column, or node_id",
        ));
    }
    if count > 1 {
        return Err(JsValue::from_str(
            "provide only one of byte_offset, line/column, or node_id",
        ));
    }

    if let Some(offset) = byte_offset {
        return Ok(HoverQuery::ByteOffset(offset));
    }

    if line.is_some() || column.is_some() {
        let line = line.ok_or_else(|| JsValue::from_str("line requires column"))?;
        let column = column.ok_or_else(|| JsValue::from_str("column requires line"))?;
        return Ok(HoverQuery::LineColumn { line, column });
    }

    let node_id = node_id.expect("count ensures node id");
    Ok(HoverQuery::NodeId(parse_node_id(&node_id)?))
}

fn parse_node_id(input: &str) -> Result<talk::node_id::NodeID, JsValue> {
    let (file_id, node_id) = match input.split_once(':') {
        Some((file_id, node_id)) => (file_id, node_id),
        None => ("0", input),
    };
    let file_id = file_id
        .parse::<u32>()
        .map_err(|_| JsValue::from_str("node id file index must be a u32"))?;
    let node_id = node_id
        .parse::<u32>()
        .map_err(|_| JsValue::from_str("node id must be a u32"))?;
    Ok(talk::node_id::NodeID(
        talk::node_id::FileID(file_id),
        node_id,
    ))
}

fn hover_to_js(
    doc_id: &str,
    text: &str,
    hover: Option<talk::analysis::Hover>,
) -> Result<JsValue, JsValue> {
    let root = Object::new();
    set_str(&root, "path", doc_id)?;

    let Some(hover) = hover else {
        Reflect::set(&root, &JsValue::from_str("hover"), &JsValue::NULL)?;
        return Ok(root.into());
    };

    let talk::analysis::Hover { contents, range } = hover;
    let hover_obj = Object::new();
    set_str(&hover_obj, "contents", &contents)?;
    let contents_markdown = format!("```talk\n{contents}\n```");
    set_str(&hover_obj, "contents_markdown", &contents_markdown)?;

    if let Some(range) = range {
        let (start_line, start_col, _, _) = line_info_for_offset(text, range.start);
        let (end_line, end_col, _, _) = line_info_for_offset(text, range.end);
        let range_obj = Object::new();
        let start_obj = Object::new();
        set_num(&start_obj, "byte", range.start)?;
        set_num(&start_obj, "line", start_line)?;
        set_num(&start_obj, "column", start_col)?;
        let end_obj = Object::new();
        set_num(&end_obj, "byte", range.end)?;
        set_num(&end_obj, "line", end_line)?;
        set_num(&end_obj, "column", end_col)?;
        Reflect::set(&range_obj, &JsValue::from_str("start"), &start_obj)?;
        Reflect::set(&range_obj, &JsValue::from_str("end"), &end_obj)?;
        Reflect::set(&hover_obj, &JsValue::from_str("range"), &range_obj)?;
    } else {
        Reflect::set(&hover_obj, &JsValue::from_str("range"), &JsValue::NULL)?;
    }

    Reflect::set(&root, &JsValue::from_str("hover"), &hover_obj)?;
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
