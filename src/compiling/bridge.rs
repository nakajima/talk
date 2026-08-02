//! The frontend result bridge (ADR 0043 §5), validation half: walk a
//! structured parse result returned by the frontend artifact and check
//! every record identity, variant tag, payload arity, field count, and
//! array reference against the ABI descriptor. Unknown variants,
//! missing fields, and malformed references fail closed at this trust
//! seam — the adapter into compiler-private parse data builds on this
//! walk.

use crate::compiling::abi::{AbiSchema, AbiTy, AbiTypeKind};
use std::collections::HashMap;
use talk_runtime::interp::{RunOutcome, Value};
use talk_runtime::memory::Pointer;
use talk_runtime::symbol::Symbol;

pub struct ResultValidator<'a, 'io> {
    run: &'a RunOutcome<'io>,
    schema: &'a AbiSchema,
    /// Schema type name -> the runtime symbol its values must carry.
    symbols: HashMap<&'a str, Symbol>,
    string_symbol: Symbol,
    array_symbol: Symbol,
    storage_symbol: Symbol,
    optional_symbol: Symbol,
}

/// Look up core's `Optional` enum: the descriptor leaves core types as
/// leaf names, so the bridge resolves their identities from the core
/// program it was compiled with.
impl<'a, 'io> ResultValidator<'a, 'io> {
    pub fn new(run: &'a RunOutcome<'io>, schema: &'a AbiSchema) -> Result<Self, String> {
        let mut symbols = HashMap::new();
        for (name, ty) in &schema.types {
            symbols.insert(name.as_str(), ty.symbol.runtime()?);
        }
        Ok(Self {
            run,
            schema,
            symbols,
            string_symbol: crate::backend::runtime_symbol(
                crate::name_resolution::symbol::Symbol::String,
            ),
            array_symbol: crate::backend::runtime_symbol(
                crate::name_resolution::symbol::Symbol::Array,
            ),
            storage_symbol: crate::backend::runtime_symbol(
                crate::name_resolution::symbol::Symbol::Storage,
            ),
            optional_symbol: schema.optional.runtime()?,
        })
    }


    /// The UTF-8 text of a String-shaped value.
    pub fn string(&self, value: &Value) -> Result<String, String> {
        let view = self.run.aggregate(value)?;
        if view.symbol != Some(self.string_symbol) {
            return Err(format!("expected a String, got {value:?}"));
        }
        let bytes = self.run.string_bytes(value)?;
        String::from_utf8(bytes.to_vec()).map_err(|err| format!("string is not UTF-8: {err}"))
    }

    /// Read an array value's elements out of the machine: `[storage,
    /// count, capacity]`, elements at `storage.base`, one byte per Byte
    /// element, one 8-byte word otherwise (boxed-arena handles for
    /// record, enum, string, optional, and nested-array elements).
    pub fn array_elements(&self, value: &Value, element: &AbiTy) -> Result<Vec<Value>, String> {
        let view = self.run.aggregate(value)?;
        if view.symbol != Some(self.array_symbol) {
            return Err(format!("expected an array, got {value:?}"));
        }
        if view.len != 3 {
            return Err("array record does not have Array's shape".into());
        }
        let storage = self.run.element(value, 0)?;
        let storage_view = self.run.aggregate(&storage)?;
        if storage_view.symbol != Some(self.storage_symbol) {
            return Err("array storage carries the wrong identity".into());
        }
        let Value::Ptr(base) = self.run.element(&storage, 0)? else {
            return Err("array storage does not have Storage's shape".into());
        };
        let base = &base;
        let (Value::I64(count), Value::I64(capacity)) =
            (self.run.element(value, 1)?, self.run.element(value, 2)?)
        else {
            return Err("array count/capacity are not integers".into());
        };
        let (count, capacity) = (&count, &capacity);
        if *count < 0 || *capacity < 0 || count > capacity {
            return Err(format!("malformed array bounds: count {count}, capacity {capacity}"));
        }
        let count = usize::try_from(*count).map_err(|_| "array count out of range")?;
        let mut elements = Vec::with_capacity(count);
        for index in 0..count {
            let value = match element {
                AbiTy::Named(name) if name == "Byte" => {
                    let addr = element_addr(*base, index, 1)?;
                    Value::Byte(self.run.read_byte(addr)?)
                }
                AbiTy::Named(name) if name == "Int" => {
                    let addr = element_addr(*base, index, 8)?;
                    Value::I64(self.run.read_word(addr)? as i64)
                }
                AbiTy::Named(name) if name == "Bool" => {
                    let addr = element_addr(*base, index, 8)?;
                    Value::Bool(self.run.read_word(addr)? != 0)
                }
                AbiTy::Named(name) if name == "Float" => {
                    let addr = element_addr(*base, index, 8)?;
                    Value::F64(f64::from_bits(self.run.read_word(addr)?))
                }
                _ => {
                    let addr = element_addr(*base, index, 8)?;
                    self.run.boxed_value(self.run.read_word(addr)?)?.clone()
                }
            };
            elements.push(value);
        }
        Ok(elements)
    }
}

fn element_addr(base: Pointer, index: usize, stride: u64) -> Result<Pointer, String> {
    let offset = (index as u64)
        .checked_mul(stride)
        .and_then(|offset| usize::try_from(offset).ok())
        .ok_or_else(|| "array element address out of range".to_string())?;
    base.checked_add(offset)
        .ok_or_else(|| "array element address out of range".into())
}

// ===== The adapter (ADR 0043 §5) =====
//
// Convert a validated frontend result into the compiler's own parse
// data: the same `parsing` AST the Rust parser builds, with node ids
// minted here and node meta recorded only where token extents diverge
// from spans (`Func` declaration extents, the for-loop pattern
// replacement). Every sub-span (name, label, mode, member) and the
// call-arg origin cross the ABI from the frontend's own captures; a
// positional call argument's label span is its own span, matching the
// reference.

use crate::common::id_generator::IDGenerator;
use crate::node::Node;
use crate::node_id::{FileID, NodeID};
use crate::node_kinds::block::Block;
use crate::node_kinds::body::Body;
use crate::node_kinds::call_arg::{ArgMode, CallArg, CallArgOrigin};
use crate::node_kinds::decl::{
    Decl, DeclKind, Import, ImportPath, ImportedSymbol, ImportedSymbols, MacroParameter,
    ReceiverMode, Visibility,
};
use crate::node_kinds::expr::{Expr, ExprKind};
use crate::node_kinds::func::{
    CaptureMode, CaptureSpec, EffectSet, Func, FuncOrigin,
};
use crate::node_kinds::func_signature::FuncSignature;
use crate::node_kinds::generic_arg::{GenericArg, StaticExpr, StaticExprKind, StaticOpKind};
use crate::node_kinds::generic_decl::GenericDecl;
use crate::node_kinds::incomplete_expr::IncompleteExpr;
use crate::node_kinds::inline_ir_instruction::{
    InlineIRInstruction, InlineIRInstructionKind, Register, Value as IrValue,
};
use crate::node_kinds::match_arm::MatchArm;
use crate::node_kinds::parameter::{ParamLabel, ParamMode, Parameter};
use crate::node_kinds::pattern::{
    Pattern, PatternKind, RecordFieldPattern, RecordFieldPatternKind,
};
use crate::node_kinds::record_field::{RecordField, RecordFieldTypeAnnotation};
use crate::node_kinds::stmt::{Stmt, StmtKind};
use crate::node_kinds::type_annotation::{AnyAssocBinding, TypeAnnotation, TypeAnnotationKind};
use crate::node_kinds::type_application::TypeApplication;
use crate::node_kinds::where_clause::{WhereClause, WherePredicate, WherePredicateKind};
use crate::node_meta::NodeMeta;
use crate::node_meta_storage::NodeMetaStorage;
use crate::parsing::span::Span;
use crate::parsing::token::Token;
use crate::token_kind::TokenKind;

/// A frontend parse brought across the ABI: the compiler-side AST plus
/// the sections the dump renders around it.
/// A diagnostic that crossed the ABI: the reference code and rendered
/// message, plus the structured position and expected-token payloads
/// editor ranges and quick fixes read.
#[derive(Debug, Clone)]
pub struct BridgedFail {
    pub code: String,
    pub message: String,
    pub span: Option<Span>,
    pub expected: Option<TokenKind>,
}

pub struct BridgedParse {
    pub roots: Vec<Node>,
    pub meta: NodeMetaStorage,
    pub comments: Vec<(u32, u32)>,
    pub failure: Option<BridgedFail>,
    pub diags: Vec<BridgedFail>,
    /// The highest node id minted; consumers continue their own
    /// minting (desugaring, typing) above it.
    pub next_node_id: u32,
}

/// Decode a `lex_tokens` result: the token stream (comments included
/// as LineComment tokens) and whether the scan completed. A trailing
/// sentinel (start -1) marks a lex failure after the tokens produced
/// up to it.
pub fn lex_tokens(run: &RunOutcome, schema: &AbiSchema) -> Result<(Vec<Token>, bool), String> {
    crate::profile::init();
    profiling::scope!("frontend.bridge_lex");
    let validator = ResultValidator::new(run, schema)?;
    let elements = validator.array_elements(&run.value, &AbiTy::Named("MetaToken".into()))?;
    let mut tokens = Vec::new();
    let mut complete = true;
    for element in &elements {
        let view = run.aggregate(element)?;
        if view.symbol != Some(validator.symbols["MetaToken"]) {
            return Err(format!("expected a MetaToken, got {element:?}"));
        }
        if view.len != 5 {
            return Err("MetaToken does not have its declared shape".into());
        }
        let kind = run.element(element, 0)?;
        let (start, end, line, col) = (
            run.element(element, 1)?,
            run.element(element, 2)?,
            run.element(element, 3)?,
            run.element(element, 4)?,
        );
        let (start, end, line, col) = (&start, &end, &line, &col);
        let Some(tag) = run.aggregate(&kind)?.tag else {
            return Err(format!("expected a TokenKind, got {kind:?}"));
        };
        let Some(AbiTypeKind::Enum(variants)) =
            schema.types.get("TokenKind").map(|ty| &ty.kind)
        else {
            return Err("schema has no TokenKind".into());
        };
        let (name, _) = variants
            .get(usize::from(tag))
            .ok_or_else(|| format!("TokenKind has no variant tag {tag}"))?;
        if int(start)? < 0 {
            complete = false;
            continue;
        }
        let coord = |value: &Value| -> Result<u32, String> {
            u32::try_from(int(value)?).map_err(|_| "token coordinate out of range".into())
        };
        tokens.push(Token {
            kind: token_kind(name)?,
            start: coord(start)?,
            end: coord(end)?,
            line: coord(line)?,
            col: coord(col)?,
        });
    }
    Ok((tokens, complete))
}

pub fn adapt(
    run: &RunOutcome,
    schema: &AbiSchema,
    file_id: FileID,
) -> Result<BridgedParse, String> {
    crate::profile::init();
    profiling::scope!("frontend.bridge_parse");
    let mut adapter = ResultAdapter {
        v: ResultValidator::new(run, schema)?,
        boxed: AbiTy::Named("boxed".into()),
        ids: IDGenerator::default(),
        meta: NodeMetaStorage::default(),
        metas: Vec::new(),
        meta_cursor: 0,
        file_id,
    };
    let mut outcome = adapter.record(&run.value.clone(), "ParseOutcome")?;
    for meta in adapter.array(&take(&mut outcome, "metas")?)? {
        let decoded = adapter.node_meta(&meta)?;
        adapter.metas.push(decoded);
    }
    let failure = adapter
        .opt(&take(&mut outcome, "failure")?)?
        .map(|fail| adapter.fail(&fail))
        .transpose()?;
    let mut diags = Vec::new();
    for fail in adapter.array(&take(&mut outcome, "diags")?)? {
        diags.push(adapter.fail(&fail)?);
    }
    let mut comments = Vec::new();
    for comment in adapter.array(&take(&mut outcome, "comments")?)? {
        let mut fields = adapter.record(&comment, "Comment")?;
        comments.push((
            position(&take(&mut fields, "start")?)?,
            position(&take(&mut fields, "end")?)?,
        ));
    }
    let mut roots = Vec::new();
    for item in adapter.array(&take(&mut outcome, "items")?)? {
        roots.push(adapter.item(&item)?);
    }
    Ok(BridgedParse {
        roots,
        meta: adapter.meta,
        comments,
        failure,
        diags,
        next_node_id: adapter.ids.last,
    })
}

struct ResultAdapter<'a, 'io> {
    v: ResultValidator<'a, 'io>,
    /// Any non-scalar element type: selects the boxed read in
    /// `array_elements`.
    boxed: AbiTy,
    ids: IDGenerator,
    meta: NodeMetaStorage,
    /// The frontend's per-node meta stream, in the same pre-order this
    /// adapter constructs nodes; None marks a synthesized node.
    metas: Vec<Option<NodeMeta>>,
    meta_cursor: usize,
    /// The file identity minted into every node id and span.
    file_id: FileID,
}

fn take(map: &mut std::collections::HashMap<String, Value>, key: &str) -> Result<Value, String> {
    map.remove(key)
        .ok_or_else(|| format!("record is missing field `{key}`"))
}

fn int(value: &Value) -> Result<i64, String> {
    let Value::I64(value) = value else {
        return Err(format!("expected an Int, got {value:?}"));
    };
    Ok(*value)
}

fn boolean(value: &Value) -> Result<bool, String> {
    let Value::Bool(value) = value else {
        return Err(format!("expected a Bool, got {value:?}"));
    };
    Ok(*value)
}

/// A non-synthesized byte position (comment bounds).
fn position(value: &Value) -> Result<u32, String> {
    u32::try_from(int(value)?).map_err(|_| "byte position out of range".to_string())
}

fn opt_span(start: i64, end: i64) -> Result<Option<Span>, String> {
    if start < 0 {
        return Ok(None);
    }
    Ok(Some(span_from(start, end)?))
}

fn span_from(start: i64, end: i64) -> Result<Span, String> {
    if start < 0 {
        return Ok(Span::SYNTHESIZED);
    }
    Ok(Span {
        file_id: FileID(0),
        start: u32::try_from(start).map_err(|_| "span start out of range")?,
        end: u32::try_from(end).map_err(|_| "span end out of range")?,
    })
}

fn token_kind(name: &str) -> Result<TokenKind, String> {
    Ok(match name {
        "plus" => TokenKind::Plus,
        "minus" => TokenKind::Minus,
        "star" => TokenKind::Star,
        "slash" => TokenKind::Slash,
        "percent" => TokenKind::Percent,
        "bang" => TokenKind::Bang,
        "tilde" => TokenKind::Tilde,
        "caret" => TokenKind::Caret,
        "amp" => TokenKind::Amp,
        "amp_amp" => TokenKind::AmpAmp,
        "pipe" => TokenKind::Pipe,
        "pipe_pipe" => TokenKind::PipePipe,
        "less" => TokenKind::Less,
        "less_equals" => TokenKind::LessEquals,
        "less_less" => TokenKind::LessLess,
        "greater" => TokenKind::Greater,
        "greater_equals" => TokenKind::GreaterEquals,
        "greater_greater" => TokenKind::GreaterGreater,
        "equals_equals" => TokenKind::EqualsEquals,
        "bang_equals" => TokenKind::BangEquals,
        "dot_dot" => TokenKind::DotDot,
        "dot_dot_less" => TokenKind::DotDotLess,
        "identifier" => TokenKind::Identifier,
        "int_number" => TokenKind::Int,
        "float_number" => TokenKind::Float,
        "string_literal" => TokenKind::StringLiteral,
        "character_literal" => TokenKind::CharacterLiteral,
        "keyword_let" => TokenKind::Let,
        "keyword_true" => TokenKind::True,
        "keyword_false" => TokenKind::False,
        "equals" => TokenKind::Equals,
        "comma" => TokenKind::Comma,
        "dot" => TokenKind::Dot,
        "dot_dot_dot" => TokenKind::DotDotDot,
        "left_paren" => TokenKind::LeftParen,
        "right_paren" => TokenKind::RightParen,
        "left_bracket" => TokenKind::LeftBracket,
        "right_bracket" => TokenKind::RightBracket,
        "left_brace" => TokenKind::LeftBrace,
        "right_brace" => TokenKind::RightBrace,
        "newline" => TokenKind::Newline,
        "underscore" => TokenKind::Underscore,
        "keyword_any" => TokenKind::Any,
        "keyword_as" => TokenKind::As,
        "keyword_func" => TokenKind::Func,
        "keyword_if" => TokenKind::If,
        "keyword_else" => TokenKind::Else,
        "keyword_loop" => TokenKind::Loop,
        "keyword_enum" => TokenKind::Enum,
        "keyword_case" => TokenKind::Case,
        "keyword_match" => TokenKind::Match,
        "keyword_return" => TokenKind::Return,
        "keyword_struct" => TokenKind::Struct,
        "keyword_extend" => TokenKind::Extend,
        "keyword_break" => TokenKind::Break,
        "keyword_init" => TokenKind::Init,
        "keyword_protocol" => TokenKind::Protocol,
        "keyword_import" => TokenKind::Import,
        "keyword_use" => TokenKind::Use,
        "keyword_pub" => TokenKind::Pub,
        "keyword_public" => TokenKind::Public,
        "keyword_linear" => TokenKind::Linear,
        "keyword_macro" => TokenKind::Macro,
        "keyword_static" => TokenKind::Static,
        "keyword_associated" => TokenKind::Associated,
        "keyword_typealias" => TokenKind::Typealias,
        "keyword_effect" => TokenKind::Effect,
        "keyword_handling" => TokenKind::Handling,
        "keyword_in" => TokenKind::In,
        "keyword_continue" => TokenKind::Continue,
        "keyword_unreachable" => TokenKind::Unreachable,
        "keyword_mut" => TokenKind::Mut,
        "keyword_consuming" => TokenKind::Consuming,
        "keyword_for" => TokenKind::For,
        "plus_equals" => TokenKind::PlusEquals,
        "minus_equals" => TokenKind::MinusEquals,
        "arrow" => TokenKind::Arrow,
        "star_equals" => TokenKind::StarEquals,
        "slash_equals" => TokenKind::SlashEquals,
        "colon" => TokenKind::Colon,
        "double_colon" => TokenKind::DoubleColon,
        "question_mark" => TokenKind::QuestionMark,
        "semicolon" => TokenKind::Semicolon,
        "at_sign" => TokenKind::At,
        "tilde_equals" => TokenKind::TildeEquals,
        "caret_equals" => TokenKind::CaretEquals,
        "attribute" => TokenKind::Attribute,
        "dollar" => TokenKind::Dollar,
        "bound_var" => TokenKind::BoundVar,
        "hash" => TokenKind::Hash,
        "ir_register" => TokenKind::IRRegister,
        "effect_name" => TokenKind::EffectName,
        "single_quote" => TokenKind::SingleQuote,
        "eof" => TokenKind::EOF,
        "line_comment" => TokenKind::LineComment,
        other => return Err(format!("no operator mapping for token kind `{other}`")),
    })
}

impl ResultAdapter<'_, '_> {
    fn id(&mut self) -> NodeID {
        NodeID(self.file_id, self.ids.next_id())
    }

    fn span(&self, start: i64, end: i64) -> Result<Span, String> {
        let mut span = span_from(start, end)?;
        if start >= 0 {
            span.file_id = self.file_id;
        }
        Ok(span)
    }

    fn opt_span(&self, start: i64, end: i64) -> Result<Option<Span>, String> {
        Ok(match opt_span(start, end)? {
            Some(mut span) => {
                span.file_id = self.file_id;
                Some(span)
            }
            None => None,
        })
    }

    fn meta_token(&self, value: &Value) -> Result<Token, String> {
        let mut fields = self.record(value, "MetaToken")?;
        let coord = |value: Value| -> Result<u32, String> {
            u32::try_from(int(&value)?).map_err(|_| "meta token coordinate out of range".into())
        };
        // Meta consumers read spans only, never a kind — skip the
        // per-node variant resolution the wire field would cost.
        Ok(Token {
            kind: TokenKind::Generated,
            start: coord(take(&mut fields, "start")?)?,
            end: coord(take(&mut fields, "end")?)?,
            line: coord(take(&mut fields, "line")?)?,
            col: coord(take(&mut fields, "col")?)?,
        })
    }

    /// One frontend NodeMeta; a negative start marks a synthesized
    /// node carrying no meta.
    fn node_meta(&self, value: &Value) -> Result<Option<NodeMeta>, String> {
        let mut fields = self.record(value, "NodeMeta")?;
        let start_value = take(&mut fields, "start")?;
        let start_fields = self.record(&start_value, "MetaToken")?;
        if int(&start_fields["start"])? < 0 {
            return Ok(None);
        }
        let start = self.meta_token(&start_value)?;
        let end = self.meta_token(&take(&mut fields, "end")?)?;
        let mut identifiers = Vec::new();
        for identifier in self.array(&take(&mut fields, "identifiers")?)? {
            identifiers.push(self.meta_token(&identifier)?);
        }
        Ok(Some(NodeMeta {
            start,
            end,
            identifiers,
        }))
    }

    /// The next entry of the frontend's pre-order meta stream. The
    /// stream and this adapter's construction order are the same walk;
    /// running dry means they diverged — fail closed.
    fn take_meta(&mut self) -> Result<Option<NodeMeta>, String> {
        let meta = self
            .metas
            .get(self.meta_cursor)
            .cloned()
            .ok_or("meta stream exhausted: adapter walk diverged from the frontend's")?;
        self.meta_cursor += 1;
        Ok(meta)
    }

    fn put_meta(&mut self, id: NodeID, meta: Option<NodeMeta>) {
        if let Some(meta) = meta {
            self.meta.insert(id, meta);
        }
    }

    /// A record's fields keyed by their schema names, identity-checked.
    fn record(
        &self,
        value: &Value,
        ty: &str,
    ) -> Result<std::collections::HashMap<String, Value>, String> {
        let schema_type = self
            .v
            .schema
            .types
            .get(ty)
            .ok_or_else(|| format!("unknown ABI type `{ty}`"))?;
        let AbiTypeKind::Struct(fields) = &schema_type.kind else {
            return Err(format!("ABI type `{ty}` is not a struct"));
        };
        let view = self.v.run.aggregate(value)?;
        if view.symbol != Some(self.v.symbols[ty]) || view.tag.is_some() {
            return Err(format!("expected a `{ty}` record, got {value:?}"));
        }
        if view.len != fields.len() {
            return Err(format!(
                "`{ty}` has {} fields but the schema declares {}",
                view.len,
                fields.len()
            ));
        }
        fields
            .iter()
            .enumerate()
            .map(|(index, (name, _))| {
                Ok((name.clone(), self.v.run.element(value, index as u16)?))
            })
            .collect()
    }

    /// An enum value's schema variant name and payload values,
    /// identity- and arity-checked.
    fn variant(&self, value: &Value, ty: &str) -> Result<(String, Vec<Value>), String> {
        let schema_type = self
            .v
            .schema
            .types
            .get(ty)
            .ok_or_else(|| format!("unknown ABI type `{ty}`"))?;
        let AbiTypeKind::Enum(variants) = &schema_type.kind else {
            return Err(format!("ABI type `{ty}` is not an enum"));
        };
        let view = self.v.run.aggregate(value)?;
        if view.symbol != Some(self.v.symbols[ty]) {
            return Err(format!("expected a `{ty}` variant, got {value:?}"));
        }
        let Some(tag) = view.tag else {
            return Err(format!("expected a `{ty}` variant, got {value:?}"));
        };
        let (name, payload_types) = variants
            .get(usize::from(tag))
            .ok_or_else(|| format!("`{ty}` has no variant tag {tag}"))?;
        if view.len != payload_types.len() {
            return Err(format!(
                "`{ty}.{name}` has {} payloads but the schema declares {}",
                view.len,
                payload_types.len()
            ));
        }
        let payloads = (0..view.len)
            .map(|index| self.v.run.element(value, index as u16))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((name.clone(), payloads))
    }

    fn opt(&self, value: &Value) -> Result<Option<Value>, String> {
        let view = self.v.run.aggregate(value)?;
        if view.symbol != Some(self.v.optional_symbol) {
            return Err(format!("expected an Optional value, got {value:?}"));
        }
        match (view.tag, view.len) {
            (Some(0), 1) => Ok(Some(self.v.run.element(value, 0)?)),
            (Some(1), 0) => Ok(None),
            _ => Err("malformed Optional value".into()),
        }
    }

    fn array(&self, value: &Value) -> Result<Vec<Value>, String> {
        self.v.array_elements(value, &self.boxed)
    }

    /// An `[Int]` array: elements are raw words, not boxed handles.
    fn int_array(&self, value: &Value) -> Result<Vec<i64>, String> {
        self.v
            .array_elements(value, &AbiTy::Named("Int".into()))?
            .iter()
            .map(int)
            .collect()
    }

    fn string(&self, value: &Value) -> Result<String, String> {
        self.v.string(value)
    }

    fn name(&self, value: &Value) -> Result<crate::name::Name, String> {
        Ok(crate::name::Name::Raw(self.string(value)?))
    }

    fn fail(&self, value: &Value) -> Result<BridgedFail, String> {
        let mut fields = self.record(value, "Fail")?;
        let code = self.string(&take(&mut fields, "code")?)?;
        let message = self.string(&take(&mut fields, "message")?)?;
        let span = self.opt_span(
            int(&take(&mut fields, "start")?)?,
            int(&take(&mut fields, "end")?)?,
        )?;
        let expected = self
            .opt(&take(&mut fields, "expected")?)?
            .map(|kind| {
                let (name, _) = self.variant(&kind, "TokenKind")?;
                token_kind(&name)
            })
            .transpose()?;
        Ok(BridgedFail {
            code,
            message,
            span,
            expected,
        })
    }

    /// A node record's span from its start/end fields.
    fn node_span(
        &self,
        fields: &mut std::collections::HashMap<String, Value>,
    ) -> Result<Span, String> {
        self.span(int(&take(fields, "start")?)?, int(&take(fields, "end")?)?)
    }

    fn item(&mut self, value: &Value) -> Result<Node, String> {
        let (variant, p) = self.variant(value, "Item")?;
        Ok(match variant.as_str() {
            "decl_item" => Node::Decl(self.decl(&p[0])?),
            "stmt_item" => Node::Stmt(self.stmt(&p[0])?),
            "expr_item" => Node::Expr(self.expr(&p[0])?),
            "pattern_item" => Node::Pattern(self.pattern(&p[0])?),
            "type_item" => Node::TypeAnnotation(self.type_annotation(&p[0])?),
            other => return Err(format!("unknown Item variant `{other}`")),
        })
    }

    fn exprs(&mut self, value: &Value) -> Result<Vec<Expr>, String> {
        self.array(value)?
            .iter()
            .map(|element| self.expr(element))
            .collect()
    }

    fn one_expr(&mut self, value: &Value) -> Result<Expr, String> {
        let mut exprs = self.exprs(value)?;
        if exprs.len() != 1 {
            return Err(format!("expected a one-element operand array, got {}", exprs.len()));
        }
        Ok(exprs.remove(0))
    }

    fn two_exprs(&mut self, value: &Value) -> Result<(Expr, Expr), String> {
        let mut exprs = self.exprs(value)?;
        if exprs.len() != 2 {
            return Err(format!("expected a two-element operand array, got {}", exprs.len()));
        }
        let rhs = exprs.remove(1);
        Ok((exprs.remove(0), rhs))
    }

    fn opt_expr(&mut self, value: &Value) -> Result<Option<Expr>, String> {
        self.opt(value)?.map(|inner| self.expr(&inner)).transpose()
    }

    fn opt_block(&mut self, value: &Value) -> Result<Option<Block>, String> {
        self.opt(value)?.map(|inner| self.block(&inner)).transpose()
    }

    fn opt_type(&mut self, value: &Value) -> Result<Option<TypeAnnotation>, String> {
        self.opt(value)?
            .map(|inner| self.type_annotation(&inner))
            .transpose()
    }

    /// A zero-or-one-element array modeling an optional block (trailing
    /// blocks, spreads ride the same convention).
    fn block_slot(&mut self, value: &Value) -> Result<Option<Block>, String> {
        let mut blocks = self.array(value)?;
        match blocks.len() {
            0 => Ok(None),
            1 => Ok(Some(self.block(&blocks.remove(0))?)),
            n => Err(format!("expected at most one block, got {n}")),
        }
    }

    fn expr(&mut self, value: &Value) -> Result<Expr, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Expr")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let id = self.id();
        self.put_meta(id, meta);
        let (variant, p) = self.variant(&kind_value, "ExprKind")?;
        let kind = match variant.as_str() {
            "literal_int" => ExprKind::LiteralInt(self.string(&p[0])?),
            "literal_float" => ExprKind::LiteralFloat(self.string(&p[0])?),
            "literal_true" => ExprKind::LiteralTrue,
            "literal_false" => ExprKind::LiteralFalse,
            "literal_string" => ExprKind::LiteralString(self.string(&p[0])?),
            "literal_character" => ExprKind::LiteralCharacter(self.string(&p[0])?),
            "variable" => ExprKind::Variable(self.name(&p[0])?),
            "unary" => {
                let (op, _) = self.variant(&p[0], "TokenKind")?;
                ExprKind::Unary(token_kind(&op)?, Box::new(self.one_expr(&p[1])?))
            }
            "binary" => {
                let (op, _) = self.variant(&p[0], "TokenKind")?;
                let (lhs, rhs) = self.two_exprs(&p[1])?;
                ExprKind::Binary(Box::new(lhs), token_kind(&op)?, Box::new(rhs))
            }
            "call" => ExprKind::Call {
                callee: Box::new(self.one_expr(&p[0])?),
                type_args: self.generic_args(&p[1])?,
                args: self.call_args(&p[2])?,
                trailing_block: self.block_slot(&p[3])?,
                desugared_operator: None,
            },
            "constructor" => {
                let mut segments = Vec::new();
                for segment in self.array(&p[1])? {
                    segments.push(self.generic_args(&segment)?);
                }
                ExprKind::Constructor(self.name(&p[0])?, segments)
            }
            "member" => {
                let (label_variant, label_payload) = self.variant(&p[0], "MemberLabel")?;
                let label = match label_variant.as_str() {
                    "named" => crate::label::Label::Named(self.string(&label_payload[0])?),
                    "positional" => crate::label::Label::Positional(
                        usize::try_from(int(&label_payload[0])?)
                            .map_err(|_| "member index out of range")?,
                    ),
                    other => return Err(format!("unknown MemberLabel variant `{other}`")),
                };
                ExprKind::Member(
                    self.receiver(&p[3])?,
                    label,
                    self.span(int(&p[1])?, int(&p[2])?)?,
                )
            }
            "incomplete_member" => {
                ExprKind::Incomplete(IncompleteExpr::Member(self.receiver(&p[0])?))
            }
            "tuple" => ExprKind::Tuple(self.exprs(&p[0])?),
            "block" => ExprKind::Block(self.block(&p[0])?),
            "literal_array" => ExprKind::LiteralArray(self.exprs(&p[0])?),
            "subscript_expr" => {
                let (lhs, index) = self.two_exprs(&p[0])?;
                ExprKind::Subscript(Box::new(lhs), Box::new(index))
            }
            "func_expr" => ExprKind::Func(self.func(&p[0], FuncOrigin::Expr)?),
            "unsafe_expr" => ExprKind::Unsafe(self.block(&p[0])?),
            "if_expr" => ExprKind::If(
                Box::new(self.one_expr(&p[0])?),
                self.block(&p[1])?,
                self.block(&p[2])?,
            ),
            "match_expr" => {
                let scrutinee = Box::new(self.one_expr(&p[0])?);
                let mut arms = Vec::new();
                for arm in self.array(&p[1])? {
                    arms.push(self.match_arm(&arm)?);
                }
                ExprKind::Match(scrutinee, arms)
            }
            "as_cast" => ExprKind::As(
                Box::new(self.one_expr(&p[0])?),
                self.type_annotation(&p[1])?,
            ),
            "propagate" => ExprKind::Propagate(Box::new(self.one_expr(&p[0])?)),
            "force_unwrap" => {
                let (operand, failure) = self.two_exprs(&p[0])?;
                ExprKind::ForceUnwrap(Box::new(operand), Box::new(failure))
            }
            "unreachable_expr" => ExprKind::Unreachable,
            "call_effect" => ExprKind::CallEffect {
                effect_name: self.name(&p[0])?,
                effect_name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                type_args: self.generic_args(&p[3])?,
                args: self.call_args(&p[4])?,
            },
            "record_literal" => {
                let mut record_fields = Vec::new();
                for field in self.array(&p[0])? {
                    record_fields.push(self.record_field(&field)?);
                }
                let mut spreads = self.exprs(&p[1])?;
                let spread = match spreads.len() {
                    0 => None,
                    1 => Some(Box::new(spreads.remove(0))),
                    n => return Err(format!("expected at most one spread, got {n}")),
                };
                ExprKind::RecordLiteral {
                    fields: record_fields,
                    spread,
                }
            }
            "inline_ir" => {
                let binds = self.exprs(&p[0])?;
                ExprKind::InlineIR(self.ir_instruction(&p[1], binds, span)?)
            }
            "macro_call" => ExprKind::MacroCall {
                name: self.string(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                args: self.exprs(&p[3])?,
            },
            other => return Err(format!("unknown ExprKind variant `{other}`")),
        };
        Ok(Expr { id, kind, span })
    }

    fn receiver(&mut self, value: &Value) -> Result<Option<Box<Expr>>, String> {
        let mut receivers = self.exprs(value)?;
        match receivers.len() {
            0 => Ok(None),
            1 => Ok(Some(Box::new(receivers.remove(0)))),
            n => Err(format!("expected at most one receiver, got {n}")),
        }
    }

    fn call_args(&mut self, value: &Value) -> Result<Vec<CallArg>, String> {
        let mut args = Vec::new();
        for (index, arg) in self.array(value)?.iter().enumerate() {
            let meta = self.take_meta()?;
            let mut fields = self.record(arg, "CallArg")?;
            let label = match self.opt(&take(&mut fields, "label")?)? {
                Some(name) => crate::label::Label::Named(self.string(&name)?),
                None => crate::label::Label::Positional(index),
            };
            let mode = self
                .opt(&take(&mut fields, "mode")?)?
                .map(|mode| self.arg_mode(&mode))
                .transpose()?;
            let label_span = self.opt_span(
                int(&take(&mut fields, "label_start")?)?,
                int(&take(&mut fields, "label_end")?)?,
            )?;
            let mode_span = self.opt_span(
                int(&take(&mut fields, "mode_start")?)?,
                int(&take(&mut fields, "mode_end")?)?,
            )?;
            let origin = if boolean(&take(&mut fields, "bare_string")?)? {
                CallArgOrigin::BareString
            } else {
                CallArgOrigin::Written
            };
            let arg_value = self.expr(&take(&mut fields, "value")?)?;
            let span = self.node_span(&mut fields)?;
            args.push(CallArg {
                id: { let id = self.id(); self.put_meta(id, meta); id },
                label,
                // A positional argument's label span is its own span.
                label_span: label_span.unwrap_or(span),
                origin,
                value: arg_value,
                span,
                mode,
                mode_span,
            });
        }
        Ok(args)
    }

    fn arg_mode(&self, value: &Value) -> Result<ArgMode, String> {
        let (variant, _) = self.variant(value, "ArgMode")?;
        Ok(match variant.as_str() {
            "mut_mode" => ArgMode::Mut,
            "consume_mode" => ArgMode::Consume,
            "copy_mode" => ArgMode::Copy,
            "borrow_mode" => ArgMode::Borrow,
            other => return Err(format!("unknown ArgMode variant `{other}`")),
        })
    }

    fn block(&mut self, value: &Value) -> Result<Block, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Block")?;
        take(&mut fields, "copied")?;
        let mut args = Vec::new();
        for parameter in self.array(&take(&mut fields, "params")?)? {
            args.push(self.parameter(&parameter)?);
        }
        let mut body = Vec::new();
        for item in self.array(&take(&mut fields, "body")?)? {
            body.push(self.item(&item)?);
        }
        let span = self.node_span(&mut fields)?;
        Ok(Block {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            args,
            body,
            span,
        })
    }

    fn parameter(&mut self, value: &Value) -> Result<Parameter, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Parameter")?;
        let label = self
            .opt(&take(&mut fields, "label")?)?
            .map(|label| {
                let (variant, payload) = self.variant(&label, "ParamLabel")?;
                Ok::<_, String>(match variant.as_str() {
                    "named" => ParamLabel::Named(self.string(&payload[0])?),
                    "omitted" => ParamLabel::Omitted,
                    other => return Err(format!("unknown ParamLabel variant `{other}`")),
                })
            })
            .transpose()?;
        let name = self.name(&take(&mut fields, "name")?)?;
        let name_span = self.span(
            int(&take(&mut fields, "name_start")?)?,
            int(&take(&mut fields, "name_end")?)?,
        )?;
        let mode = self
            .opt(&take(&mut fields, "mode")?)?
            .map(|mode| {
                let (variant, _) = self.variant(&mode, "ParamMode")?;
                Ok::<_, String>(match variant.as_str() {
                    "borrow_param" => ParamMode::Borrow,
                    "mut_param" => ParamMode::Mut,
                    "consume_param" => ParamMode::Consume,
                    "consume_mut_param" => ParamMode::ConsumeMut,
                    other => return Err(format!("unknown ParamMode variant `{other}`")),
                })
            })
            .transpose()?;
        let label_span = self.opt_span(
            int(&take(&mut fields, "label_start")?)?,
            int(&take(&mut fields, "label_end")?)?,
        )?;
        let mode_span = self.opt_span(
            int(&take(&mut fields, "mode_start")?)?,
            int(&take(&mut fields, "mode_end")?)?,
        )?;
        let type_annotation = self.opt_type(&take(&mut fields, "annotation")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(Parameter {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            label,
            label_span,
            name,
            name_span,
            type_annotation,
            span,
            mode,
            mode_span,
        })
    }

    fn match_arm(&mut self, value: &Value) -> Result<MatchArm, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "MatchArm")?;
        let pattern = self.pattern(&take(&mut fields, "pattern")?)?;
        let body = self.block(&take(&mut fields, "body")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(MatchArm {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            pattern,
            body,
            span,
        })
    }

    fn record_field(&mut self, value: &Value) -> Result<RecordField, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "RecordField")?;
        let label = self.name(&take(&mut fields, "label")?)?;
        let label_span = self.span(
            int(&take(&mut fields, "label_start")?)?,
            int(&take(&mut fields, "label_end")?)?,
        )?;
        let field_value = self.expr(&take(&mut fields, "value")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(RecordField {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            label,
            label_span,
            value: field_value,
            span,
        })
    }

    fn ir_instruction(
        &mut self,
        value: &Value,
        binds: Vec<Expr>,
        span: Span,
    ) -> Result<InlineIRInstruction, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "IRInstruction")?;
        let name = self.string(&take(&mut fields, "name")?)?;
        let instr_name_span = self.span(
            int(&take(&mut fields, "name_start")?)?,
            int(&take(&mut fields, "name_end")?)?,
        )?;
        let dest = self
            .opt(&take(&mut fields, "dest")?)?
            .map(|dest| Ok::<_, String>(Register(self.string(&dest)?)))
            .transpose()?;
        let ty = self.opt_type(&take(&mut fields, "ty")?)?;
        let mut values = Vec::new();
        for ir_value in self.array(&take(&mut fields, "values")?)? {
            values.push(self.ir_value(&ir_value)?);
        }
        let op = self
            .opt(&take(&mut fields, "op")?)?
            .map(|op| {
                let (variant, _) = self.variant(&op, "TokenKind")?;
                token_kind(&variant)
            })
            .transpose()?;
        let missing = |what: &str| format!("@_ir `{name}` is missing its {what}");
        let mut values = values.into_iter();
        let mut next = |what: &str| values.next().ok_or_else(|| missing(what));
        let require_dest = dest.clone().ok_or_else(|| missing("destination"));
        let require_ty = ty.clone().ok_or_else(|| missing("type operand"));
        let kind = match name.as_str() {
            "cmp" => InlineIRInstructionKind::Cmp {
                dest: require_dest?,
                lhs: next("lhs")?,
                rhs: next("rhs")?,
                ty: require_ty?,
                op: op.ok_or_else(|| missing("comparator"))?,
            },
            "add" => InlineIRInstructionKind::Add { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "sub" => InlineIRInstructionKind::Sub { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "mul" => InlineIRInstructionKind::Mul { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "div" => InlineIRInstructionKind::Div { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "and" => InlineIRInstructionKind::And { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "or" => InlineIRInstructionKind::Or { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "xor" => InlineIRInstructionKind::Xor { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "shl" => InlineIRInstructionKind::Shl { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "shr" => InlineIRInstructionKind::Shr { dest: require_dest?, ty: require_ty?, a: next("a")?, b: next("b")? },
            "not" => InlineIRInstructionKind::Not { dest: require_dest?, ty: require_ty?, a: next("a")? },
            "alloc" => InlineIRInstructionKind::Alloc { dest: require_dest?, ty: require_ty?, count: next("count")? },
            "load" => InlineIRInstructionKind::Load { dest: require_dest?, ty: require_ty?, addr: next("addr")? },
            "take" => InlineIRInstructionKind::Take { dest: require_dest?, ty: require_ty?, value: next("value")? },
            "gep" => InlineIRInstructionKind::Gep {
                dest: require_dest?,
                ty: require_ty?,
                addr: next("addr")?,
                offset_index: next("offset")?,
            },
            "inline_get" => InlineIRInstructionKind::InlineGet {
                dest: require_dest?,
                ty: require_ty?,
                array: next("array")?,
                index: next("index")?,
            },
            "io" => InlineIRInstructionKind::Io {
                dest: require_dest?,
                op: next("op")?,
                a: next("a")?,
                b: next("b")?,
                c: next("c")?,
            },
            "trunc" => InlineIRInstructionKind::Trunc { dest: require_dest?, val: next("val")? },
            "is_unique" => InlineIRInstructionKind::IsUnique { dest: require_dest?, ptr: next("ptr")? },
            "itof" => InlineIRInstructionKind::IntToFloat { dest: require_dest?, val: next("val")? },
            "btoi" => InlineIRInstructionKind::ByteToInt { dest: require_dest?, val: next("val")? },
            "itob" => InlineIRInstructionKind::IntToByte { dest: require_dest?, val: next("val")? },
            "store" => InlineIRInstructionKind::Store { value: next("value")?, ty: require_ty?, addr: next("addr")? },
            "free" => InlineIRInstructionKind::Free { ptr: next("ptr")? },
            "retain" => InlineIRInstructionKind::Retain { ty: require_ty?, value: next("value")? },
            "copy" => InlineIRInstructionKind::Copy {
                ty: require_ty?,
                from: next("from")?,
                to: next("to")?,
                length: next("length")?,
            },
            "swap" => InlineIRInstructionKind::Swap { ty: require_ty?, a: next("a")?, b: next("b")? },
            other => return Err(format!("unknown @_ir instruction `{other}`")),
        };
        Ok(InlineIRInstruction {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            span,
            binds,
            instr_name_span,
            kind,
        })
    }

    fn ir_value(&self, value: &Value) -> Result<IrValue, String> {
        let (variant, payload) = self.variant(value, "IRValue")?;
        Ok(match variant.as_str() {
            "reg" => IrValue::Reg(
                u32::try_from(int(&payload[0])?).map_err(|_| "IR register out of range")?,
            ),
            "int_value" => IrValue::Int(int(&payload[0])?),
            "float_value" => IrValue::Float(
                self.string(&payload[0])?
                    .parse()
                    .map_err(|_| "malformed IR float")?,
            ),
            "bool_value" => IrValue::Bool(boolean(&payload[0])?),
            "void_value" => IrValue::Void,
            "bind" => IrValue::Bind(
                usize::try_from(int(&payload[0])?).map_err(|_| "IR bind out of range")?,
            ),
            other => return Err(format!("unknown IRValue variant `{other}`")),
        })
    }

    fn stmt(&mut self, value: &Value) -> Result<Stmt, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Stmt")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let id = self.id();
        self.put_meta(id, meta);
        let (variant, p) = self.variant(&kind_value, "StmtKind")?;
        let kind = match variant.as_str() {
            "expr_stmt" => StmtKind::Expr(self.expr(&p[0])?),
            "if_stmt" => StmtKind::If(
                self.expr(&p[0])?,
                self.block(&p[1])?,
                self.opt_block(&p[2])?,
            ),
            "return_stmt" => StmtKind::Return(self.opt_expr(&p[0])?),
            "break_stmt" => StmtKind::Break,
            "assignment" => {
                let (lhs, rhs) = self.two_exprs(&p[0])?;
                StmtKind::Assignment(Box::new(lhs), Box::new(rhs))
            }
            "loop_stmt" => StmtKind::Loop(self.opt_expr(&p[0])?, self.block(&p[1])?),
            "for_stmt" => {
                let source_mode = self
                    .opt(&p[3])?
                    .map(|mode| self.arg_mode(&mode))
                    .transpose()?;
                StmtKind::For {
                    iterable: Box::new(self.expr(&p[0])?),
                    source_mode,
                    pattern: self.pattern(&p[1])?,
                    body: self.block(&p[2])?,
                    hidden_source: format!("__for_src_{}", id.1).into(),
                    hidden_iter: format!("__for_iter_{}", id.1).into(),
                }
            }
            "continue_stmt" => StmtKind::Continue,
            "resume_stmt" => StmtKind::Resume(self.opt_expr(&p[0])?),
            "handle_stmt" => StmtKind::Handling {
                effect_name: self.name(&p[0])?,
                effect_name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                body: self.block(&p[3])?,
            },
            other => return Err(format!("unknown StmtKind variant `{other}`")),
        };
        Ok(Stmt { id, kind, span })
    }

    fn pattern(&mut self, value: &Value) -> Result<Pattern, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Pattern")?;
        let kind_value = take(&mut fields, "kind")?;
        take(&mut fields, "meta_start")?;
        take(&mut fields, "meta_end")?;
        let span = self.node_span(&mut fields)?;
        let id = self.id();
        self.put_meta(id, meta);
        let (variant, p) = self.variant(&kind_value, "PatternKind")?;
        let kind = match variant.as_str() {
            "bind" => PatternKind::Bind(self.name(&p[0])?),
            "wildcard" => PatternKind::Wildcard,
            "literal_int" => PatternKind::LiteralInt(self.string(&p[0])?),
            "literal_float" => PatternKind::LiteralFloat(self.string(&p[0])?),
            "literal_character" => PatternKind::LiteralCharacter(self.string(&p[0])?),
            "literal_string" => PatternKind::LiteralString(self.string(&p[0])?),
            "literal_true" => PatternKind::LiteralTrue,
            "literal_false" => PatternKind::LiteralFalse,
            "tuple" => PatternKind::Tuple(self.patterns(&p[0])?),
            "or_pattern" => PatternKind::Or(self.patterns(&p[0])?),
            "variant" => {
                let enum_name = self
                    .opt(&p[0])?
                    .map(|name| self.name(&name))
                    .transpose()?;
                let mut enum_generics = Vec::new();
                for segment in self.array(&p[1])? {
                    enum_generics.push(self.generic_args(&segment)?);
                }
                let mut field_labels = Vec::new();
                for label in self.array(&p[6])? {
                    field_labels.push(self.opt(&label)?.map(|name| self.name(&name)).transpose()?);
                }
                PatternKind::Variant {
                    enum_name,
                    enum_generics,
                    variant_name: self.string(&p[2])?,
                    variant_name_span: self.span(int(&p[3])?, int(&p[4])?)?,
                    fields: self.patterns(&p[5])?,
                    field_labels,
                }
            }
            "struct_pattern" => {
                let mut struct_generics = Vec::new();
                for segment in self.array(&p[1])? {
                    struct_generics.push(self.generic_args(&segment)?);
                }
                let mut field_names = Vec::new();
                for name in self.array(&p[3])? {
                    field_names.push(self.name(&name)?);
                }
                PatternKind::Struct {
                    struct_name: Some(self.name(&p[0])?),
                    struct_generics,
                    fields: self
                        .patterns(&p[2])?
                        .into_iter()
                        .map(Node::Pattern)
                        .collect(),
                    field_names,
                    rest: boolean(&p[4])?,
                }
            }
            "record" => {
                let mut record_fields = Vec::new();
                for field in self.array(&p[0])? {
                    record_fields.push(self.record_field_pattern(&field)?);
                }
                PatternKind::Record {
                    fields: record_fields,
                }
            }
            other => return Err(format!("unknown PatternKind variant `{other}`")),
        };
        Ok(Pattern { id, kind, span })
    }

    fn patterns(&mut self, value: &Value) -> Result<Vec<Pattern>, String> {
        self.array(value)?
            .iter()
            .map(|element| self.pattern(element))
            .collect()
    }

    fn record_field_pattern(&mut self, value: &Value) -> Result<RecordFieldPattern, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "RecordFieldPattern")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let (variant, p) = self.variant(&kind_value, "RecordFieldPatternKind")?;
        let kind = match variant.as_str() {
            "bind_field" => RecordFieldPatternKind::Bind(self.name(&p[0])?),
            "equals_field" => RecordFieldPatternKind::Equals {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                value: self.pattern(&p[3])?,
            },
            "rest_field" => RecordFieldPatternKind::Rest,
            other => return Err(format!("unknown RecordFieldPatternKind variant `{other}`")),
        };
        Ok(RecordFieldPattern {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            span,
            kind,
        })
    }

    fn type_annotation(&mut self, value: &Value) -> Result<TypeAnnotation, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "TypeAnnotation")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let (variant, p) = self.variant(&kind_value, "TypeAnnotationKind")?;
        let kind = match variant.as_str() {
            "borrow" => TypeAnnotationKind::Borrow {
                mutable: boolean(&p[0])?,
                inner: Box::new(self.one_type(&p[1])?),
            },
            "unique" => TypeAnnotationKind::Unique {
                inner: Box::new(self.one_type(&p[0])?),
            },
            "func_type" => TypeAnnotationKind::Func {
                params: self.types(&p[0])?,
                effects: self.effect_set(&p[1])?,
                returns: Box::new(self.one_type(&p[2])?),
            },
            "nominal_path" => TypeAnnotationKind::NominalPath {
                base: Box::new(self.one_type(&p[0])?),
                member: crate::label::Label::Named(self.string(&p[1])?),
                member_span: self.span(int(&p[2])?, int(&p[3])?)?,
                member_generics: self.generic_args(&p[4])?,
            },
            "nominal" => TypeAnnotationKind::Nominal {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                generics: self.generic_args(&p[3])?,
            },
            "tuple" => TypeAnnotationKind::Tuple(self.types(&p[0])?),
            "record_type" => {
                let mut record_fields = Vec::new();
                for field in self.array(&p[0])? {
                    let field_meta = self.take_meta()?;
                    let mut inner = self.record(&field, "RecordFieldTypeAnnotation")?;
                    let label = self.name(&take(&mut inner, "label")?)?;
                    let label_span = self.span(
                        int(&take(&mut inner, "label_start")?)?,
                        int(&take(&mut inner, "label_end")?)?,
                    )?;
                    let field_value = self.type_annotation(&take(&mut inner, "value")?)?;
                    let field_span = self.node_span(&mut inner)?;
                    record_fields.push(RecordFieldTypeAnnotation {
                        id: { let id = self.id(); self.put_meta(id, field_meta); id },
                        label,
                        label_span,
                        value: field_value,
                        span: field_span,
                    });
                }
                TypeAnnotationKind::Record {
                    fields: record_fields,
                }
            }
            "any_type" => {
                let mut bindings = Vec::new();
                for binding in self.array(&p[1])? {
                    let binding_meta = self.take_meta()?;
                    let mut inner = self.record(&binding, "AnyAssocBinding")?;
                    let name = self.name(&take(&mut inner, "name")?)?;
                    let name_span = self.span(
                        int(&take(&mut inner, "name_start")?)?,
                        int(&take(&mut inner, "name_end")?)?,
                    )?;
                    let binding_value = self.type_annotation(&take(&mut inner, "value")?)?;
                    let binding_span = self.node_span(&mut inner)?;
                    bindings.push(AnyAssocBinding {
                        id: { let id = self.id(); self.put_meta(id, binding_meta); id },
                        name,
                        name_span,
                        value: binding_value,
                        span: binding_span,
                    });
                }
                TypeAnnotationKind::Any {
                    protocol: Box::new(self.one_type(&p[0])?),
                    assoc_bindings: bindings,
                }
            }
            other => return Err(format!("unknown TypeAnnotationKind variant `{other}`")),
        };
        Ok(TypeAnnotation {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            kind,
            span,
        })
    }

    fn types(&mut self, value: &Value) -> Result<Vec<TypeAnnotation>, String> {
        self.array(value)?
            .iter()
            .map(|element| self.type_annotation(element))
            .collect()
    }

    fn one_type(&mut self, value: &Value) -> Result<TypeAnnotation, String> {
        let mut types = self.types(value)?;
        if types.len() != 1 {
            return Err(format!("expected a one-element type array, got {}", types.len()));
        }
        Ok(types.remove(0))
    }

    fn effect_set(&mut self, value: &Value) -> Result<EffectSet, String> {
        let mut fields = self.record(value, "EffectSet")?;
        let mut names = Vec::new();
        for name in self.array(&take(&mut fields, "names")?)? {
            names.push(self.name(&name)?);
        }
        let starts = self.int_array(&take(&mut fields, "name_starts")?)?;
        let ends = self.int_array(&take(&mut fields, "name_ends")?)?;
        if starts.len() != names.len() || ends.len() != names.len() {
            return Err("effect-name spans out of step with names".into());
        }
        let mut spans = Vec::new();
        for (start, end) in starts.iter().zip(&ends) {
            spans.push(self.span(*start, *end)?);
        }
        Ok(EffectSet {
            names,
            spans,
            is_open: boolean(&take(&mut fields, "open")?)?,
        })
    }

    fn generic_args(&mut self, value: &Value) -> Result<Vec<GenericArg>, String> {
        let mut args = Vec::new();
        for arg in self.array(value)? {
            args.push(self.generic_arg(&arg)?);
        }
        Ok(args)
    }

    fn generic_arg(&mut self, value: &Value) -> Result<GenericArg, String> {
        let (variant, p) = self.variant(value, "GenericArg")?;
        Ok(match variant.as_str() {
            "type_arg" => GenericArg::Type(self.type_annotation(&p[0])?),
            "static_arg" => GenericArg::Static(self.static_expr(&p[0])?),
            other => return Err(format!("unknown GenericArg variant `{other}`")),
        })
    }

    fn static_expr(&mut self, value: &Value) -> Result<StaticExpr, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "StaticExpr")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let (variant, p) = self.variant(&kind_value, "StaticExprKind")?;
        let kind = match variant.as_str() {
            "int_literal" => StaticExprKind::Int(self.string(&p[0])?),
            "bool_literal" => StaticExprKind::Bool(boolean(&p[0])?),
            "unqualified_case" => StaticExprKind::UnqualifiedCase {
                name: self.string(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
            },
            "static_path" => StaticExprKind::Path(self.type_annotation(&p[0])?),
            "static_group" => {
                let mut inner = self.static_exprs(&p[0])?;
                if inner.len() != 1 {
                    return Err("expected a one-element static group".into());
                }
                StaticExprKind::Group(Box::new(inner.remove(0)))
            }
            "static_op" => {
                let (op_variant, _) = self.variant(&p[0], "StaticOpKind")?;
                let op = match op_variant.as_str() {
                    "add" => StaticOpKind::Add,
                    "sub" => StaticOpKind::Sub,
                    "mul" => StaticOpKind::Mul,
                    other => return Err(format!("unknown StaticOpKind variant `{other}`")),
                };
                let mut operands = self.static_exprs(&p[1])?;
                if operands.len() != 2 {
                    return Err("expected two static operands".into());
                }
                let rhs = operands.remove(1);
                StaticExprKind::Op {
                    op,
                    lhs: Box::new(operands.remove(0)),
                    rhs: Box::new(rhs),
                }
            }
            other => return Err(format!("unknown StaticExprKind variant `{other}`")),
        };
        Ok(StaticExpr {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            kind,
            span,
        })
    }

    fn static_exprs(&mut self, value: &Value) -> Result<Vec<StaticExpr>, String> {
        self.array(value)?
            .iter()
            .map(|element| self.static_expr(element))
            .collect()
    }

    fn generic_decls(&mut self, value: &Value) -> Result<Vec<GenericDecl>, String> {
        self.array(value)?
            .iter()
            .map(|element| self.generic_decl(element))
            .collect()
    }

    fn generic_decl(&mut self, value: &Value) -> Result<GenericDecl, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "GenericDecl")?;
        let name = self.name(&take(&mut fields, "name")?)?;
        let name_span = self.span(
            int(&take(&mut fields, "name_start")?)?,
            int(&take(&mut fields, "name_end")?)?,
        )?;
        let generics = self.generic_decls(&take(&mut fields, "generics")?)?;
        let conformances = self.types(&take(&mut fields, "conformances")?)?;
        let default = self
            .opt(&take(&mut fields, "default_value")?)?
            .map(|arg| self.generic_arg(&arg))
            .transpose()?;
        let static_ty = self.opt_type(&take(&mut fields, "static_ty")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(GenericDecl {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            name,
            name_span,
            generics,
            conformances,
            default,
            static_ty,
            span,
        })
    }

    fn where_clause(&mut self, value: &Value) -> Result<Option<WhereClause>, String> {
        let Some(clause) = self.opt(value)? else {
            return Ok(None);
        };
        let clause_meta = self.take_meta()?;
        let mut fields = self.record(&clause, "WhereClause")?;
        let mut predicates = Vec::new();
        for predicate in self.array(&take(&mut fields, "predicates")?)? {
            let predicate_meta = self.take_meta()?;
            let mut inner = self.record(&predicate, "WherePredicate")?;
            let kind_value = take(&mut inner, "kind")?;
            let span = self.node_span(&mut inner)?;
            let (variant, p) = self.variant(&kind_value, "WherePredicateKind")?;
            let kind = match variant.as_str() {
                "type_eq" => WherePredicateKind::TypeEq {
                    lhs: self.generic_arg(&p[0])?,
                    rhs: self.generic_arg(&p[1])?,
                },
                "static_cmp" => WherePredicateKind::StaticCmp {
                    strict: boolean(&p[0])?,
                    lhs: self.generic_arg(&p[1])?,
                    rhs: self.generic_arg(&p[2])?,
                },
                "conforms" => WherePredicateKind::Conforms {
                    ty: self.type_annotation(&p[0])?,
                    protocols: self.types(&p[1])?,
                },
                other => return Err(format!("unknown WherePredicateKind variant `{other}`")),
            };
            predicates.push(WherePredicate {
                id: { let id = self.id(); self.put_meta(id, predicate_meta); id },
                span,
                kind,
            });
        }
        let span = self.node_span(&mut fields)?;
        Ok(Some(WhereClause {
            id: { let id = self.id(); self.put_meta(id, clause_meta); id },
            span,
            predicates,
        }))
    }

    fn func(&mut self, value: &Value, origin: FuncOrigin) -> Result<Func, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Func")?;
        let name = self.name(&take(&mut fields, "name")?)?;
        let name_span = self.span(
            int(&take(&mut fields, "name_start")?)?,
            int(&take(&mut fields, "name_end")?)?,
        )?;
        let effects = self.effect_set(&take(&mut fields, "effects")?)?;
        let generics = self.generic_decls(&take(&mut fields, "generics")?)?;
        let mut captures = Vec::new();
        for capture in self.array(&take(&mut fields, "captures")?)? {
            captures.push(self.capture_spec(&capture)?);
        }
        let where_clause = self.where_clause(&take(&mut fields, "where_clause")?)?;
        let mut params = Vec::new();
        for parameter in self.array(&take(&mut fields, "params")?)? {
            params.push(self.parameter(&parameter)?);
        }
        let body = self.block(&take(&mut fields, "body")?)?;
        let ret = self.opt_type(&take(&mut fields, "ret")?)?;
        take(&mut fields, "meta_start")?;
        take(&mut fields, "meta_end")?;
        take(&mut fields, "start")?;
        take(&mut fields, "end")?;
        let id = self.id();
        self.put_meta(id, meta);
        Ok(Func {
            id,
            name,
            name_span,
            origin,
            effects,
            generics,
            captures,
            where_clause,
            params,
            body,
            ret,
            attributes: vec![],
        })
    }

    fn capture_spec(&mut self, value: &Value) -> Result<CaptureSpec, String> {
        let mut fields = self.record(value, "CaptureSpec")?;
        let (variant, _) = self.variant(&take(&mut fields, "mode")?, "CaptureMode")?;
        let mode = match variant.as_str() {
            "copy_capture" => CaptureMode::Copy,
            "move_capture" => CaptureMode::Move,
            "borrow_shared" => CaptureMode::BorrowShared,
            "borrow_mut" => CaptureMode::BorrowMut,
            other => return Err(format!("unknown CaptureMode variant `{other}`")),
        };
        let name = self.name(&take(&mut fields, "name")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(CaptureSpec { mode, name, span })
    }

    fn func_signature(&mut self, value: &Value) -> Result<FuncSignature, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "FuncSignature")?;
        let name = self.name(&take(&mut fields, "name")?)?;
        let mut params = Vec::new();
        for parameter in self.array(&take(&mut fields, "params")?)? {
            params.push(self.parameter(&parameter)?);
        }
        let effects = self.effect_set(&take(&mut fields, "effects")?)?;
        let generics = self.generic_decls(&take(&mut fields, "generics")?)?;
        let where_clause = self.where_clause(&take(&mut fields, "where_clause")?)?;
        let ret = self.opt_type(&take(&mut fields, "ret")?)?.map(Box::new);
        let span = self.node_span(&mut fields)?;
        Ok(FuncSignature {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            span,
            name,
            params,
            effects,
            generics,
            where_clause,
            ret,
        })
    }

    fn body(&mut self, value: &Value) -> Result<Body, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Body")?;
        let mut decls = Vec::new();
        for decl in self.array(&take(&mut fields, "decls")?)? {
            decls.push(self.decl(&decl)?);
        }
        let span = self.node_span(&mut fields)?;
        Ok(Body {
            id: { let id = self.id(); self.put_meta(id, meta); id },
            decls,
            span,
        })
    }

    fn receiver_mode(&self, value: &Value) -> Result<ReceiverMode, String> {
        let (variant, _) = self.variant(value, "ReceiverMode")?;
        Ok(match variant.as_str() {
            "none_receiver" => ReceiverMode::None,
            "ref_receiver" => ReceiverMode::Ref,
            "consuming_receiver" => ReceiverMode::Consuming,
            other => return Err(format!("unknown ReceiverMode variant `{other}`")),
        })
    }

    fn decl(&mut self, value: &Value) -> Result<Decl, String> {
        let meta = self.take_meta()?;
        let mut fields = self.record(value, "Decl")?;
        let kind_value = take(&mut fields, "kind")?;
        let visibility = if boolean(&take(&mut fields, "is_public")?)? {
            Visibility::Public
        } else {
            Visibility::Private
        };
        let span = self.node_span(&mut fields)?;
        let id = self.id();
        self.put_meta(id, meta);
        let (variant, p) = self.variant(&kind_value, "DeclKind")?;
        let kind = match variant.as_str() {
            "let_decl" => DeclKind::Let {
                lhs: self.pattern(&p[0])?,
                type_annotation: self.opt_type(&p[1])?,
                rhs: self.opt_expr(&p[2])?,
            },
            "import_decl" => {
                let mut import = self.record(&p[0], "Import")?;
                let (symbols_variant, symbols_payload) =
                    self.variant(&take(&mut import, "symbols")?, "ImportedSymbols")?;
                let symbols = match symbols_variant.as_str() {
                    "all" => ImportedSymbols::All,
                    "named" => {
                        let mut named = Vec::new();
                        for symbol in self.array(&symbols_payload[0])? {
                            let mut inner = self.record(&symbol, "ImportedSymbol")?;
                            named.push(ImportedSymbol {
                                name: self.string(&take(&mut inner, "name")?)?,
                                span: self.span(
                                    int(&take(&mut inner, "name_start")?)?,
                                    int(&take(&mut inner, "name_end")?)?,
                                )?,
                                alias: self
                                    .opt(&take(&mut inner, "alias")?)?
                                    .map(|alias| self.string(&alias))
                                    .transpose()?,
                            });
                        }
                        ImportedSymbols::Named(named)
                    }
                    other => return Err(format!("unknown ImportedSymbols variant `{other}`")),
                };
                let path = self.string(&take(&mut import, "path")?)?;
                let path = if boolean(&take(&mut import, "local")?)? {
                    ImportPath::Local(path)
                } else {
                    ImportPath::Package(path)
                };
                DeclKind::Import(Import {
                    symbols,
                    path,
                    path_span: span_from(
                        int(&take(&mut import, "path_start")?)?,
                        int(&take(&mut import, "path_end")?)?,
                    )?,
                })
            }
            "func_decl" => DeclKind::Func(self.func(&p[0], FuncOrigin::Decl)?),
            "func_signature" => DeclKind::FuncSignature(self.func_signature(&p[0])?),
            "struct_decl" => DeclKind::Struct {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                generics: self.generic_decls(&p[3])?,
                where_clause: self.where_clause(&p[4])?,
                body: self.body(&p[5])?,
                linear: boolean(&p[6])?,
                heap: boolean(&p[7])?,
            },
            "enum_decl" => DeclKind::Enum {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                generics: self.generic_decls(&p[3])?,
                where_clause: self.where_clause(&p[4])?,
                body: self.body(&p[5])?,
                linear: boolean(&p[6])?,
                // Appended in the enum-'heap migration: absent from
                // artifacts built before it, and absence means unmarked.
                heap: p.get(7).map(boolean).transpose()?.unwrap_or(false),
            },
            "protocol_decl" => DeclKind::Protocol {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                generics: self.generic_decls(&p[3])?,
                where_clause: self.where_clause(&p[4])?,
                body: self.body(&p[5])?,
                conformances: self.types(&p[6])?,
            },
            "enum_variant" => {
                let mut payload_labels = Vec::new();
                for label in self.array(&p[5])? {
                    payload_labels
                        .push(self.opt(&label)?.map(|name| self.name(&name)).transpose()?);
                }
                DeclKind::EnumVariant {
                    name: self.name(&p[0])?,
                    name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                    generics: self.generic_decls(&p[3])?,
                    payloads: self.types(&p[4])?,
                    payload_labels,
                    result: self.opt_type(&p[6])?,
                }
            }
            "extend_decl" => {
                let binders = self.generic_decls(&p[0])?;
                let head_meta = self.take_meta()?;
                let mut application = self.record(&p[1], "TypeApplication")?;
                let head_name = self.name(&take(&mut application, "name")?)?;
                let head_name_span = span_from(
                    int(&take(&mut application, "name_start")?)?,
                    int(&take(&mut application, "name_end")?)?,
                )?;
                let head_args = self.generic_args(&take(&mut application, "args")?)?;
                let head_span = self.node_span(&mut application)?;
                DeclKind::Extend {
                    binders,
                    head: TypeApplication {
                        id: { let id = self.id(); self.put_meta(id, head_meta); id },
                        span: head_span,
                        name: head_name,
                        name_span: head_name_span,
                        args: head_args,
                    },
                    conformances: self.types(&p[2])?,
                    where_clause: self.where_clause(&p[3])?,
                    body: self.body(&p[4])?,
                }
            }
            "init_decl" => {
                let mut params = Vec::new();
                for parameter in self.array(&p[0])? {
                    params.push(self.parameter(&parameter)?);
                }
                DeclKind::Init {
                    name: crate::name::Name::Raw("init".into()),
                    params,
                    body: self.block(&p[1])?,
                }
            }
            "property" => DeclKind::Property {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                is_static: boolean(&p[3])?,
                type_annotation: self.opt_type(&p[4])?,
                default_value: self.opt_expr(&p[5])?,
            },
            "method" => DeclKind::Method {
                func: Box::new(self.func(&p[0], FuncOrigin::Decl)?),
                is_static: boolean(&p[1])?,
                receiver_mode: self.receiver_mode(&p[2])?,
            },
            "method_requirement" => DeclKind::MethodRequirement {
                signature: self.func_signature(&p[0])?,
                receiver_mode: self.receiver_mode(&p[1])?,
            },
            "init_requirement" => DeclKind::InitRequirement {
                signature: self.func_signature(&p[0])?,
            },
            "typealias_decl" => DeclKind::TypeAlias(
                self.name(&p[0])?,
                self.span(int(&p[1])?, int(&p[2])?)?,
                self.type_annotation(&p[3])?,
            ),
            "effect_decl" => DeclKind::Effect {
                name: self.name(&p[0])?,
                name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                generics: self.generic_decls(&p[3])?,
                where_clause: self.where_clause(&p[4])?,
                params: {
                    let mut params = Vec::new();
                    for parameter in self.array(&p[5])? {
                        params.push(self.parameter(&parameter)?);
                    }
                    params
                },
                ret: self.type_annotation(&p[6])?,
            },
            "associated_decl" => DeclKind::Associated {
                generic: self.generic_decl(&p[0])?,
                where_clause: self.where_clause(&p[1])?,
            },
            "macro_decl" => {
                let mut params = Vec::new();
                for param in self.array(&p[3])? {
                    let mut inner = self.record(&param, "MacroParam")?;
                    let name = self.string(&take(&mut inner, "name")?)?;
                    let span = span_from(
                        int(&take(&mut inner, "start")?)?,
                        int(&take(&mut inner, "end")?)?,
                    )?;
                    params.push(MacroParameter { name, span });
                }
                DeclKind::Macro {
                    name: self.string(&p[0])?,
                    name_span: self.span(int(&p[1])?, int(&p[2])?)?,
                    params,
                    template: self.expr(&p[4])?,
                }
            }
            other => return Err(format!("unknown DeclKind variant `{other}`")),
        };
        Ok(Decl {
            id,
            kind,
            span,
            visibility,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::compiling::abi::parse_schema;

    /// The descriptor's own round trip: what `describe` emits,
    /// `parse_schema` reads back, and the checked-in copy is it.
    #[test]
    fn checked_in_descriptor_parses_and_names_the_root() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let abi_text = std::fs::read_to_string(crate::compiling::frontend::abi_path(root))
            .expect("ABI descriptor exists");
        let schema = parse_schema(&abi_text).expect("ABI descriptor parses");
        assert_eq!(schema.root, crate::compiling::frontend::SCHEMA_ROOT);
        assert!(schema.types.len() > 40, "unexpectedly small schema");
    }
}
