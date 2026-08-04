//! The shared native library boundary (ADR 0048).
//!
//! Both native backends emit library artifacts through this module, so
//! the versioned call convention -- an output slot, a contiguous
//! argument array, and an argument count -- the lifecycle entry points,
//! the status codes, the symbol mangling, and the generated header are
//! one definition rather than two that could drift.
//!
//! The generated C here references the `TALK_LIBRARY` machinery in
//! `runtime.c` (`talk_lib_*`, `talk_stack_init`) and the data tables
//! every backend emits under the same names (`talk_statics`,
//! `talk_type_table`, `talk_layout_table`, `talk_globals`).

use std::fmt::Write as _;

/// The library boundary's ABI version: the wrapper signature, status
/// codes, value representation, and lifecycle contract. Bump on any
/// change to those.
pub const ABI_VERSION: u32 = 1;

/// Entry points every library exposes besides its export wrappers; an
/// export whose mangled symbol lands on one is rejected.
pub const LIFECYCLE: [&str; 4] = ["init", "teardown", "error_message", "exit_status"];

/// One export wrapper's identity: the Talk name, the external C symbol,
/// and the arity the wrapper checks before entering generated code.
pub struct Export {
    pub name: String,
    pub symbol: String,
    pub arity: u16,
}

/// The prefix becomes the leading part of every external symbol, so it
/// must be a C identifier.
pub fn validate_prefix(prefix: &str) -> Result<(), String> {
    let mut chars = prefix.chars();
    let valid = match chars.next() {
        Some(first) => {
            (first.is_ascii_alphabetic() || first == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        None => false,
    };
    if valid {
        Ok(())
    } else {
        Err(format!(
            "invalid library symbol prefix \"{prefix}\": a C identifier is required"
        ))
    }
}

/// Deterministic, collision-free mangling for arbitrary UTF-8 export
/// names: ASCII alphanumerics pass through, `_` doubles, and every other
/// byte becomes `_` plus two lowercase hex digits. The escape introducer
/// is always `_` and what follows it is self-delimiting, so distinct
/// names cannot meet at one symbol.
pub fn mangle(name: &str) -> String {
    let mut mangled = String::with_capacity(name.len());
    for byte in name.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' => mangled.push(char::from(byte)),
            b'_' => mangled.push_str("__"),
            _ => {
                let _ = write!(mangled, "_{byte:02x}");
            }
        }
    }
    mangled
}

/// Resolve export names to external symbols under `prefix`, rejecting an
/// invalid prefix, malformed names, lifecycle collisions, and duplicate
/// external symbols.
pub fn resolve_symbols(prefix: &str, names: &[&str]) -> Result<Vec<String>, String> {
    validate_prefix(prefix)?;
    let reserved: Vec<String> = LIFECYCLE
        .iter()
        .map(|name| format!("{prefix}_{name}"))
        .collect();
    let mut symbols: Vec<String> = Vec::with_capacity(names.len());
    for name in names {
        if name.is_empty() {
            return Err("malformed export id: an empty name".to_string());
        }
        let symbol = format!("{prefix}_{}", mangle(name));
        if reserved.contains(&symbol) {
            return Err(format!(
                "export \"{name}\" collides with the library lifecycle symbol {symbol}"
            ));
        }
        if symbols.contains(&symbol) {
            return Err(format!(
                "duplicate external symbol {symbol} (export \"{name}\")"
            ));
        }
        symbols.push(symbol);
    }
    Ok(symbols)
}

/// The export-name-to-symbol manifest: one tab-separated line per
/// export, in export order.
pub fn manifest(exports: &[Export]) -> String {
    exports
        .iter()
        .map(|export| format!("{}\t{}\n", export.name, export.symbol))
        .collect()
}

/// The boundary tail's opening: value-ABI asserts and the status codes
/// the wrappers return, shared verbatim with the generated header.
pub fn boundary_prelude() -> String {
    format!(
        "\n/* ---- library boundary (ADR 0048), ABI version {ABI_VERSION} ---- */\n\
         #include <stddef.h>\n\
         _Static_assert(sizeof(TalkValue) == 16, \"the library value ABI assumes 16-byte values\");\n\
         _Static_assert(offsetof(TalkValue, v) == 8, \"the library value ABI assumes the payload at offset 8\");\n\
         #define TALK_LIB_OK 0\n\
         #define TALK_LIB_ERR_ARITY 1\n\
         #define TALK_LIB_ERR_TRAP 2\n\
         #define TALK_LIB_ERR_EXIT 3\n\
         #define TALK_LIB_ERR_STATE 4\n\
         #define TALK_LIB_ERR_VALUE 5\n"
    )
}

/// The display-id-to-module-symbol row every backend emits as
/// `talk_lib_symbols` in library mode: row 0 is the anonymous tuple
/// (kind 255), and row N is the module symbol behind display id N,
/// mirroring the type table exactly. `kind` follows `MirSymbolKind`
/// declaration order (0 struct, 1 enum, 2 effect, 3 protocol).
pub fn symbol_row_type() -> &'static str {
    "\ntypedef struct {\n    uint8_t kind;\n    uint32_t module;\n    uint32_t local;\n} TalkLibSymbolRow;\n"
}

/// The logical value accessors (ADR 0048 stage 6): a host bridge walks
/// returned aggregates through these instead of knowing layouts. All
/// reads are logical — products index their declared fields, sums index
/// the live variant's payloads, native boxes are retagged first — so
/// the walk matches the VM's `aggregate`/`element` exactly.
///
/// `string_ids` is the interned `(layout, display)` identity of core
/// String when the module has one; without it `{p}_string_new` reports
/// `TALK_LIB_ERR_VALUE`.
pub fn accessors(prefix: &str, string_ids: Option<(u32, u32)>) -> String {
    let string_new_body = match string_ids {
        Some((layout, display)) => format!(
            "    if (!talk_lib_initialized) {{\n        return TALK_LIB_ERR_STATE;\n    }}\n    \
             switch (setjmp(talk_lib_boundary)) {{\n    \
             case 0:\n        break;\n    \
             default:\n        talk_lib_cleanup();\n        return TALK_LIB_ERR_TRAP;\n    \
             }}\n    \
             talk_lib_boundary_armed = 1;\n    \
             TalkValue storage = talk_alloc(talk_int((int64_t)len));\n    \
             if (len != 0) {{\n        memcpy(storage.v.ptr, bytes, (size_t)len);\n    }}\n    \
             TalkValue built = talk_agg({layout}u, {display}u, 0, 3);\n    \
             built.v.agg->fields[0] = storage;\n    \
             built.v.agg->fields[1] = talk_int((int64_t)len);\n    \
             built.v.agg->fields[2] = talk_int((int64_t)len);\n    \
             talk_lib_boundary_armed = 0;\n    \
             *out = built;\n    \
             return TALK_LIB_OK;\n"
        ),
        None => "    (void)out;\n    (void)bytes;\n    (void)len;\n    \
                 return talk_lib_value_error(\"this library has no String type\");\n"
            .to_string(),
    };
    format!(
        "\nstatic int talk_lib_value_error(const char *what) {{\n    \
         snprintf(talk_lib_message, sizeof talk_lib_message, \"%s\", what);\n    \
         return TALK_LIB_ERR_VALUE;\n}}\n\
         \nstatic TalkValue talk_lib_plain(TalkValue value) {{\n    \
         return value.tag == TALK_NATIVE ? talk_native_retag(value) : value;\n}}\n\
         \n/* The aggregate view: display identity, live variant tag (-1 for\n\
         \x20  products), and logical member count. */\n\
         int {prefix}_value_view(TalkValue value, uint32_t *display, int32_t *tag, uint32_t *len) {{\n    \
         value = talk_lib_plain(value);\n    \
         if (value.tag != TALK_AGG) {{\n        \
         return talk_lib_value_error(\"a non-aggregate value has no view\");\n    }}\n    \
         TalkAgg *agg = value.v.agg;\n    \
         *display = agg->symbol;\n    \
         if (agg->layout == TALK_DYN || agg->layout >= talk_layout_count) {{\n        \
         *tag = -1;\n        *len = agg->len;\n        return TALK_LIB_OK;\n    }}\n    \
         const TalkLayoutInfo *info = &talk_layouts[agg->layout];\n    \
         if (info->is_sum) {{\n        \
         uint32_t live = (uint32_t)agg->fields[0].v.i;\n        \
         if (live >= info->variant_count) {{\n            \
         return talk_lib_value_error(\"enum tag out of range\");\n        }}\n        \
         *tag = (int32_t)live;\n        \
         *len = info->variant_starts[live + 1] - info->variant_starts[live];\n    \
         }} else {{\n        \
         *tag = -1;\n        *len = info->field_count;\n    }}\n    \
         return TALK_LIB_OK;\n}}\n\
         \n/* One logical member: a product's declared field or the live\n\
         \x20  variant's payload. Spliced children reconstruct in the arena, so\n\
         \x20  an out-of-memory trap is contained here like a wrapper call. */\n\
         int {prefix}_value_element(TalkValue value, uint32_t index, TalkValue *out) {{\n    \
         value = talk_lib_plain(value);\n    \
         if (value.tag != TALK_AGG) {{\n        \
         return talk_lib_value_error(\"a non-aggregate value has no members\");\n    }}\n    \
         TalkAgg *agg = value.v.agg;\n    \
         switch (setjmp(talk_lib_boundary)) {{\n    \
         case 0:\n        break;\n    \
         default:\n        talk_lib_cleanup();\n        return TALK_LIB_ERR_TRAP;\n    \
         }}\n    \
         talk_lib_boundary_armed = 1;\n    \
         int status = TALK_LIB_OK;\n    \
         if (agg->layout == TALK_DYN || agg->layout >= talk_layout_count) {{\n        \
         if (index >= agg->len) {{\n            \
         status = talk_lib_value_error(\"member index out of range\");\n        \
         }} else {{\n            *out = agg->fields[index];\n        }}\n    \
         }} else {{\n        \
         const TalkLayoutInfo *info = &talk_layouts[agg->layout];\n        \
         if (info->is_sum) {{\n            \
         uint32_t live = (uint32_t)agg->fields[0].v.i;\n            \
         if (live >= info->variant_count\n                \
         || index >= info->variant_starts[live + 1] - info->variant_starts[live]) {{\n                \
         status = talk_lib_value_error(\"payload index out of range\");\n            \
         }} else {{\n                \
         *out = talk_field_at(value, &info->fields[info->variant_starts[live] + index]);\n            \
         }}\n        \
         }} else if (index >= info->field_count) {{\n            \
         status = talk_lib_value_error(\"member index out of range\");\n        \
         }} else {{\n            \
         *out = talk_field_at(value, &info->fields[index]);\n        }}\n    }}\n    \
         talk_lib_boundary_armed = 0;\n    \
         return status;\n}}\n\
         \n/* A string's bytes: borrowed until teardown or a failed call. */\n\
         int {prefix}_string_read(TalkValue value, const unsigned char **bytes, uint64_t *len) {{\n    \
         value = talk_lib_plain(value);\n    \
         if (value.tag != TALK_AGG || value.v.agg->len < 2\n        \
         || value.v.agg->fields[0].tag != TALK_PTR\n        \
         || value.v.agg->fields[1].tag != TALK_INT) {{\n        \
         return talk_lib_value_error(\"value is not a string\");\n    }}\n    \
         *bytes = value.v.agg->fields[0].v.ptr;\n    \
         *len = (uint64_t)value.v.agg->fields[1].v.i;\n    \
         return TALK_LIB_OK;\n}}\n\
         \n/* Raw array storage reads: an 8-byte word or one byte at an index\n\
         \x20  off a storage base pointer. */\n\
         int {prefix}_array_word(TalkValue base, uint64_t index, uint64_t *out) {{\n    \
         if (base.tag != TALK_PTR) {{\n        \
         return talk_lib_value_error(\"array storage is not a pointer\");\n    }}\n    \
         memcpy(out, base.v.ptr + index * 8, 8);\n    \
         return TALK_LIB_OK;\n}}\n\
         \nint {prefix}_array_byte(TalkValue base, uint64_t index, uint8_t *out) {{\n    \
         if (base.tag != TALK_PTR) {{\n        \
         return talk_lib_value_error(\"array storage is not a pointer\");\n    }}\n    \
         *out = base.v.ptr[index];\n    \
         return TALK_LIB_OK;\n}}\n\
         \n/* A boxed array element: the stored word is a cell pointer. */\n\
         int {prefix}_boxed_read(uint64_t word, TalkValue *out) {{\n    \
         TalkValue *cell = (TalkValue *)(uintptr_t)word;\n    \
         if (cell == NULL) {{\n        \
         return talk_lib_value_error(\"null boxed array element\");\n    }}\n    \
         *out = *cell;\n    \
         return TALK_LIB_OK;\n}}\n\
         \n/* The display-id-to-module-symbol table, for record identity\n\
         \x20  validation against an ABI descriptor. */\n\
         uint32_t {prefix}_symbol_count(void) {{\n    \
         return (uint32_t)(sizeof talk_lib_symbols / sizeof *talk_lib_symbols);\n}}\n\
         \nint {prefix}_symbol(uint32_t display, uint8_t *kind, uint32_t *module, uint32_t *local) {{\n    \
         if (display >= sizeof talk_lib_symbols / sizeof *talk_lib_symbols) {{\n        \
         return talk_lib_value_error(\"display id out of range\");\n    }}\n    \
         *kind = talk_lib_symbols[display].kind;\n    \
         *module = talk_lib_symbols[display].module;\n    \
         *local = talk_lib_symbols[display].local;\n    \
         return TALK_LIB_OK;\n}}\n\
         \n/* Construct a Talk String over host bytes, allocated inside the\n\
         \x20  library so teardown reclaims it. */\n\
         int {prefix}_string_new(TalkValue *out, const unsigned char *bytes, uint64_t len) {{\n\
         {string_new_body}}}\n"
    )
}

/// The helper a failed or torn-down invocation ends in: all resources
/// reclaimed and the library back to its uninitialized state, so
/// previously returned values are invalidated together.
pub fn cleanup_helper(has_globals: bool) -> String {
    let globals = if has_globals {
        "\n    memset(talk_globals, 0, sizeof talk_globals);"
    } else {
        ""
    };
    format!(
        "\nstatic void talk_lib_cleanup(void) {{\n    \
         talk_lib_reset();{globals}\n    \
         talk_lib_initialized = 0;\n}}\n"
    )
}

/// The namespaced lifecycle entry points. `layout_count` is the C
/// expression for the layout table's row count -- the backends size
/// their tables differently.
pub fn lifecycle(prefix: &str, layout_count: &str) -> String {
    format!(
        "\nint {prefix}_init(void) {{\n    \
         if (talk_lib_initialized) {{\n        return TALK_LIB_ERR_STATE;\n    }}\n    \
         talk_argc = 0;\n    \
         talk_argv = NULL;\n    \
         talk_statics_base = talk_statics;\n    \
         talk_statics_len = sizeof talk_statics;\n    \
         talk_types = talk_type_table;\n    \
         talk_type_count = sizeof talk_type_table / sizeof *talk_type_table;\n    \
         talk_layouts = talk_layout_table;\n    \
         talk_layout_count = {layout_count};\n    \
         talk_lib_message[0] = '\\0';\n    \
         talk_lib_exit_status = 0;\n    \
         talk_lib_initialized = 1;\n    \
         return TALK_LIB_OK;\n}}\n\
         \nvoid {prefix}_teardown(void) {{\n    \
         if (talk_lib_initialized) {{\n        talk_lib_cleanup();\n    }}\n}}\n\
         \nconst char *{prefix}_error_message(void) {{\n    return talk_lib_message;\n}}\n\
         \nint {prefix}_exit_status(void) {{\n    return talk_lib_exit_status;\n}}\n"
    )
}

/// One export wrapper under the versioned convention. `invoke` is the C
/// statement block that leaves `TalkValue result` defined -- how
/// generated code is entered is the one backend-specific part.
pub fn wrapper(export: &Export, invoke: &str) -> String {
    let Export {
        name,
        symbol,
        arity,
    } = export;
    let unused_args = if *arity == 0 { "\n    (void)args;" } else { "" };
    format!(
        "\n/* export \"{}\" */\n\
         int {symbol}(TalkValue *out, const TalkValue *args, size_t argc) {{\n    \
         if (!talk_lib_initialized) {{\n        return TALK_LIB_ERR_STATE;\n    }}\n    \
         if (argc != {arity}) {{\n        \
         snprintf(talk_lib_message, sizeof talk_lib_message,\n                 \
         \"export \\\"{}\\\" takes {arity} argument(s), got %zu\", argc);\n        \
         return TALK_LIB_ERR_ARITY;\n    }}\n    \
         {{ char anchor; talk_stack_init((uintptr_t)&anchor); }}{unused_args}\n    \
         switch (setjmp(talk_lib_boundary)) {{\n    \
         case 0:\n        break;\n    \
         case 2:\n        talk_lib_cleanup();\n        return TALK_LIB_ERR_EXIT;\n    \
         default:\n        talk_lib_cleanup();\n        return TALK_LIB_ERR_TRAP;\n    \
         }}\n    \
         talk_lib_boundary_armed = 1;\n    \
         {invoke}\n    \
         talk_lib_boundary_armed = 0;\n    \
         if (out != NULL) {{\n        *out = result;\n    }}\n    \
         return TALK_LIB_OK;\n}}\n",
        comment(name),
        string_escape(name),
    )
}

/// The generated header: the value type, scalar tags, status codes, and
/// every entry point, all under the caller's prefix so two generated
/// libraries can be used from one translation unit.
pub fn header(prefix: &str, exports: &[Export]) -> String {
    let guard = format!("{}_H", prefix.to_ascii_uppercase());
    let upper = prefix.to_ascii_uppercase();
    let mut header = String::new();
    let _ = write!(
        header,
        "/* Generated Talk library interface (ADR 0048). Do not edit.\n\
         \x20*\n\
         \x20* Lifecycle: {prefix}_init, then serialized wrapper calls, then\n\
         \x20* {prefix}_teardown. One invocation may be active at a time; the\n\
         \x20* owner serializes calls. Successful results stay valid until\n\
         \x20* teardown. A trap or exit status performs complete invocation\n\
         \x20* cleanup: the library returns to its uninitialized state and\n\
         \x20* previously returned values are invalidated.\n\
         \x20*/\n\
         #ifndef {guard}\n\
         #define {guard}\n\n\
         #include <stddef.h>\n\
         #include <stdint.h>\n\n\
         #ifdef __cplusplus\n\
         extern \"C\" {{\n\
         #endif\n\n\
         #define {upper}_ABI_VERSION {ABI_VERSION}\n\n\
         /* The native runtime's uniform boundary value: a tag byte and an\n\
         \x20  8-byte payload. Non-scalar payloads are runtime-private\n\
         \x20  pointers, opaque to the caller. */\n\
         typedef struct {prefix}_value {{\n    \
         uint8_t tag;\n    \
         uint8_t reserved[7];\n    \
         union {{\n        int64_t i;\n        double f;\n        void *ptr;\n    }} payload;\n\
         }} {prefix}_value;\n\n\
         enum {{\n    \
         {upper}_TAG_UNIT = 0,\n    \
         {upper}_TAG_BOOL = 1,\n    \
         {upper}_TAG_INT = 2,\n    \
         {upper}_TAG_AGG = 3,\n    \
         {upper}_TAG_PTR = 6,\n    \
         {upper}_TAG_BYTE = 7,\n    \
         {upper}_TAG_FLOAT = 8\n\
         }};\n\n\
         /* Every entry point's status. */\n\
         enum {{\n    \
         {upper}_OK = 0,\n    \
         {upper}_ERR_ARITY = 1,\n    \
         {upper}_ERR_TRAP = 2,\n    \
         {upper}_ERR_EXIT = 3,\n    \
         {upper}_ERR_STATE = 4,\n    \
         {upper}_ERR_VALUE = 5\n\
         }};\n\n\
         int {prefix}_init(void);\n\
         void {prefix}_teardown(void);\n\
         /* The last trap or exit description; empty after a fresh init. */\n\
         const char *{prefix}_error_message(void);\n\
         /* The status a contained exit request carried. */\n\
         int {prefix}_exit_status(void);\n\n\
         /* Logical value accessors: aggregate views, member reads, string\n\
         \x20  and array access, and the display-symbol table. See the\n\
         \x20  library boundary documentation (ADR 0048). */\n\
         int {prefix}_value_view({prefix}_value value, uint32_t *display, int32_t *tag, uint32_t *len);\n\
         int {prefix}_value_element({prefix}_value value, uint32_t index, {prefix}_value *out);\n\
         int {prefix}_string_read({prefix}_value value, const unsigned char **bytes, uint64_t *len);\n\
         int {prefix}_string_new({prefix}_value *out, const unsigned char *bytes, uint64_t len);\n\
         int {prefix}_array_word({prefix}_value base, uint64_t index, uint64_t *out);\n\
         int {prefix}_array_byte({prefix}_value base, uint64_t index, uint8_t *out);\n\
         int {prefix}_boxed_read(uint64_t word, {prefix}_value *out);\n\
         uint32_t {prefix}_symbol_count(void);\n\
         int {prefix}_symbol(uint32_t display, uint8_t *kind, uint32_t *module, uint32_t *local);\n\n"
    );
    for export in exports {
        let _ = writeln!(
            header,
            "/* export \"{}\", arity {} */\n\
             int {}({prefix}_value *out, const {prefix}_value *args, size_t argc);",
            comment(&export.name),
            export.arity,
            export.symbol,
        );
    }
    let _ = write!(
        header,
        "\nstatic inline {prefix}_value {prefix}_unit(void) {{\n    \
         {prefix}_value value = {{0}};\n    return value;\n}}\n\n\
         static inline {prefix}_value {prefix}_bool(int bit) {{\n    \
         {prefix}_value value = {{0}};\n    value.tag = {upper}_TAG_BOOL;\n    \
         value.payload.i = bit != 0;\n    return value;\n}}\n\n\
         static inline {prefix}_value {prefix}_int(int64_t number) {{\n    \
         {prefix}_value value = {{0}};\n    value.tag = {upper}_TAG_INT;\n    \
         value.payload.i = number;\n    return value;\n}}\n\n\
         static inline {prefix}_value {prefix}_float(double number) {{\n    \
         {prefix}_value value = {{0}};\n    value.tag = {upper}_TAG_FLOAT;\n    \
         value.payload.f = number;\n    return value;\n}}\n\n\
         static inline int64_t {prefix}_value_int({prefix}_value value) {{\n    \
         return value.payload.i;\n}}\n\n\
         static inline double {prefix}_value_float({prefix}_value value) {{\n    \
         return value.payload.f;\n}}\n\n\
         #ifdef __cplusplus\n\
         }}\n\
         #endif\n\n\
         #endif /* {guard} */\n"
    );
    header
}

/// Export names reach the output inside `/* */`, which does not nest.
fn comment(name: &str) -> String {
    name.replace("/*", "/ *").replace("*/", "* /")
}

/// Export names also reach the output inside C string literals.
fn string_escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"")
}
