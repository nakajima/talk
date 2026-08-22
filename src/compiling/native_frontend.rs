//! The native frontend binding (ADR 0048): the compiler's private link
//! to the generated frontend library that `build.rs` compiles from
//! `bootstrap/frontend.c`.
//!
//! Calls are serialized behind one lock — the native runtime keeps
//! file-scope state, so one invocation is active at a time — and each
//! invocation runs a full `init` → call → consume → `teardown` cycle:
//! results (including borrowed string bytes) are valid only until
//! teardown, so consumers adapt inside the invocation. A Talk trap or
//! exit request is contained by the wrapper boundary and surfaces here
//! as an ordinary error string; it never terminates this process.

#[cfg(not(target_arch = "wasm32"))]
use std::ffi::CStr;
#[cfg(not(target_arch = "wasm32"))]
use std::os::raw::c_char;
#[cfg(not(target_arch = "wasm32"))]
use std::sync::Mutex;

/// The native runtime's uniform boundary value (16 bytes, payload at
/// offset 8), asserted on the C side by the library boundary.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct NativeValue {
    pub tag: u8,
    reserved: [u8; 7],
    payload: u64,
}

pub const TAG_UNIT: u8 = 0;
pub const TAG_BOOL: u8 = 1;
pub const TAG_INT: u8 = 2;
pub const TAG_AGG: u8 = 3;
pub const TAG_PTR: u8 = 6;
pub const TAG_BYTE: u8 = 7;
pub const TAG_FLOAT: u8 = 8;

impl NativeValue {
    #[cfg(not(target_arch = "wasm32"))]
    fn unit() -> Self {
        Self {
            tag: TAG_UNIT,
            reserved: [0; 7],
            payload: 0,
        }
    }

    /// The integer payload, meaningful for `TAG_INT`/`TAG_BYTE`.
    pub fn int(&self) -> i64 {
        self.payload as i64
    }

    /// The boolean payload, meaningful for `TAG_BOOL`.
    pub fn boolean(&self) -> bool {
        self.payload != 0
    }

    /// The float payload, meaningful for `TAG_FLOAT`.
    pub fn float(&self) -> f64 {
        f64::from_bits(self.payload)
    }
}

#[cfg(not(target_arch = "wasm32"))]
const OK: i32 = 0;

#[cfg(not(target_arch = "wasm32"))]
type ExportFn = unsafe extern "C" fn(*mut NativeValue, *const NativeValue, usize) -> i32;

#[cfg(not(target_arch = "wasm32"))]
unsafe extern "C" {
    fn talk_frontend_init() -> i32;
    fn talk_frontend_teardown();
    fn talk_frontend_error_message() -> *const c_char;
    fn talk_frontend_string_new(out: *mut NativeValue, bytes: *const u8, len: u64) -> i32;
    fn talk_frontend_value_view(
        value: NativeValue,
        display: *mut u32,
        tag: *mut i32,
        len: *mut u32,
    ) -> i32;
    fn talk_frontend_value_element(value: NativeValue, index: u32, out: *mut NativeValue) -> i32;
    fn talk_frontend_string_read(value: NativeValue, bytes: *mut *const u8, len: *mut u64) -> i32;
    fn talk_frontend_array_word(base: NativeValue, index: u64, out: *mut u64) -> i32;
    fn talk_frontend_array_byte(base: NativeValue, index: u64, out: *mut u8) -> i32;
    fn talk_frontend_boxed_read(word: u64, out: *mut NativeValue) -> i32;
    fn talk_frontend_symbol_count() -> u32;
    fn talk_frontend_symbol(display: u32, kind: *mut u8, module: *mut u32, local: *mut u32) -> i32;
    fn talk_frontend_lex(out: *mut NativeValue, args: *const NativeValue, argc: usize) -> i32;
    fn talk_frontend_trees(out: *mut NativeValue, args: *const NativeValue, argc: usize) -> i32;
    fn talk_frontend_parse(out: *mut NativeValue, args: *const NativeValue, argc: usize) -> i32;
    fn talk_frontend_parse__file__source(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__file__docs__source(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__lenient(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__block__items(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__expr(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__pattern(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__type(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_lex__tokens(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__block__items__source(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__pattern__source(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__type__source(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
    fn talk_frontend_parse__members__source(
        out: *mut NativeValue,
        args: *const NativeValue,
        argc: usize,
    ) -> i32;
}

/// The frontend's export wrappers by export name (the C symbols carry
/// the shared boundary mangling, so `_` doubles).
#[cfg(not(target_arch = "wasm32"))]
fn export_fn(name: &str) -> Option<ExportFn> {
    Some(match name {
        "lex" => talk_frontend_lex,
        "trees" => talk_frontend_trees,
        "parse" => talk_frontend_parse,
        "parse_file_source" => talk_frontend_parse__file__source,
        "parse_file_docs_source" => talk_frontend_parse__file__docs__source,
        "parse_lenient" => talk_frontend_parse__lenient,
        "parse_block_items" => talk_frontend_parse__block__items,
        "parse_expr" => talk_frontend_parse__expr,
        "parse_pattern" => talk_frontend_parse__pattern,
        "parse_type" => talk_frontend_parse__type,
        "lex_tokens" => talk_frontend_lex__tokens,
        "parse_block_items_source" => talk_frontend_parse__block__items__source,
        "parse_pattern_source" => talk_frontend_parse__pattern__source,
        "parse_type_source" => talk_frontend_parse__type__source,
        "parse_members_source" => talk_frontend_parse__members__source,
        _ => return None,
    })
}

/// The invocation lock: the native runtime's state is global.
#[cfg(not(target_arch = "wasm32"))]
static NATIVE: Mutex<()> = Mutex::new(());

#[cfg(not(target_arch = "wasm32"))]
fn last_error() -> String {
    // Safety: `talk_frontend_error_message` returns the library's
    // NUL-terminated message buffer, valid for the process lifetime.
    let message = unsafe { CStr::from_ptr(talk_frontend_error_message()) };
    message.to_string_lossy().into_owned()
}

/// One serialized native invocation: initialize, build the string
/// arguments inside the library, call the export, hand the result to
/// `consume`, and tear down. `consume` must finish adaptation before it
/// returns — teardown invalidates the result.
#[cfg(not(target_arch = "wasm32"))]
pub fn run_export<R>(
    name: &str,
    args: &[&[u8]],
    consume: impl FnOnce(&NativeRun) -> Result<R, String>,
) -> Result<R, String> {
    let export =
        export_fn(name).ok_or_else(|| format!("the native frontend does not export `{name}`"))?;
    let _guard = NATIVE
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    // Safety: the lock serializes every entry into the native library,
    // and the teardown guard restores the uninitialized state on every
    // path (teardown is a no-op after a contained trap already cleaned
    // up).
    unsafe {
        let status = talk_frontend_init();
        if status != OK {
            return Err(format!("native frontend init failed: {}", last_error()));
        }
        struct Teardown;
        impl Drop for Teardown {
            fn drop(&mut self) {
                unsafe { talk_frontend_teardown() };
            }
        }
        let _teardown = Teardown;
        let mut built: Vec<NativeValue> = Vec::with_capacity(args.len());
        for bytes in args {
            let mut value = NativeValue::unit();
            let status = talk_frontend_string_new(&mut value, bytes.as_ptr(), bytes.len() as u64);
            if status != OK {
                return Err(format!(
                    "native frontend argument construction failed: {}",
                    last_error()
                ));
            }
            built.push(value);
        }
        let mut out = NativeValue::unit();
        let status = export(&mut out, built.as_ptr(), built.len());
        if status != OK {
            return Err(last_error());
        }
        consume(&NativeRun { value: out })
    }
}

/// A native export's result, alive until the invocation tears down.
/// The accessors mirror `talk_vm::interp::RunOutcome`'s logical reads.
pub struct NativeRun {
    pub value: NativeValue,
}

#[cfg(not(target_arch = "wasm32"))]
impl NativeRun {
    pub fn view(&self, value: NativeValue) -> Result<(u32, Option<u16>, usize), String> {
        let mut display = 0u32;
        let mut tag = -1i32;
        let mut len = 0u32;
        // Safety: pure logical read; out-pointers are locals.
        let status = unsafe { talk_frontend_value_view(value, &mut display, &mut tag, &mut len) };
        if status != OK {
            return Err(last_error());
        }
        let tag = u16::try_from(tag).ok();
        Ok((display, tag, len as usize))
    }

    pub fn element(&self, value: NativeValue, index: u16) -> Result<NativeValue, String> {
        let mut out = NativeValue::unit();
        // Safety: logical read; a contained trap surfaces as a status.
        let status = unsafe { talk_frontend_value_element(value, u32::from(index), &mut out) };
        if status != OK {
            return Err(last_error());
        }
        Ok(out)
    }

    pub fn string_bytes(&self, value: NativeValue) -> Result<&[u8], String> {
        let mut bytes: *const u8 = std::ptr::null();
        let mut len = 0u64;
        // Safety: the returned bytes stay valid until teardown, which
        // cannot happen while `self` is borrowed.
        let status = unsafe { talk_frontend_string_read(value, &mut bytes, &mut len) };
        if status != OK {
            return Err(last_error());
        }
        if len == 0 {
            return Ok(&[]);
        }
        Ok(unsafe { std::slice::from_raw_parts(bytes, len as usize) })
    }

    pub fn read_word(&self, base: NativeValue, index: u64) -> Result<u64, String> {
        let mut out = 0u64;
        // Safety: reads library-owned array storage.
        let status = unsafe { talk_frontend_array_word(base, index, &mut out) };
        if status != OK {
            return Err(last_error());
        }
        Ok(out)
    }

    pub fn read_byte(&self, base: NativeValue, index: u64) -> Result<u8, String> {
        let mut out = 0u8;
        // Safety: reads library-owned array storage.
        let status = unsafe { talk_frontend_array_byte(base, index, &mut out) };
        if status != OK {
            return Err(last_error());
        }
        Ok(out)
    }

    pub fn boxed_value(&self, word: u64) -> Result<NativeValue, String> {
        let mut out = NativeValue::unit();
        // Safety: the word is a cell pointer the library wrote.
        let status = unsafe { talk_frontend_boxed_read(word, &mut out) };
        if status != OK {
            return Err(last_error());
        }
        Ok(out)
    }
}

/// The module-symbol row behind one display id, from the artifact's
/// emitted symbol table: `MirSymbolKind` declaration order for `kind`.
#[cfg(not(target_arch = "wasm32"))]
pub fn symbol_rows() -> Vec<(u8, u32, u32)> {
    // Safety: reads the artifact's constant table.
    unsafe {
        let count = talk_frontend_symbol_count();
        let mut rows = Vec::with_capacity(count as usize);
        for display in 0..count {
            let (mut kind, mut module, mut local) = (255u8, 0u32, 0u32);
            if talk_frontend_symbol(display, &mut kind, &mut module, &mut local) == OK {
                rows.push((kind, module, local));
            } else {
                rows.push((255, 0, 0));
            }
        }
        rows
    }
}

// wasm32 executes the verified bootstrap bytecode in the VM instead of
// linking a native artifact (ADR 0048 wasm carve-out); these stubs keep
// the bridge's native arms compiling without referencing any symbol.
#[cfg(target_arch = "wasm32")]
pub fn run_export<R>(
    name: &str,
    _args: &[&[u8]],
    _consume: impl FnOnce(&NativeRun) -> Result<R, String>,
) -> Result<R, String> {
    Err(format!(
        "the native frontend is unavailable on wasm32 (export `{name}`); parsing routes through the VM"
    ))
}

#[cfg(target_arch = "wasm32")]
pub fn symbol_rows() -> Vec<(u8, u32, u32)> {
    Vec::new()
}

#[cfg(target_arch = "wasm32")]
impl NativeRun {
    fn unavailable<T>() -> Result<T, String> {
        Err("the native frontend is unavailable on wasm32".to_string())
    }

    pub fn view(&self, _value: NativeValue) -> Result<(u32, Option<u16>, usize), String> {
        Self::unavailable()
    }

    pub fn element(&self, _value: NativeValue, _index: u16) -> Result<NativeValue, String> {
        Self::unavailable()
    }

    pub fn string_bytes(&self, _value: NativeValue) -> Result<&[u8], String> {
        Self::unavailable()
    }

    pub fn read_word(&self, _base: NativeValue, _index: u64) -> Result<u64, String> {
        Self::unavailable()
    }

    pub fn read_byte(&self, _base: NativeValue, _index: u64) -> Result<u8, String> {
        Self::unavailable()
    }

    pub fn boxed_value(&self, _word: u64) -> Result<NativeValue, String> {
        Self::unavailable()
    }
}
