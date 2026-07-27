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
fn optional_symbol() -> Result<Symbol, String> {
    let core = crate::compiling::core::typed_program();
    let symbol = core
        .types()
        .catalog
        .enums
        .keys()
        .find(|symbol| {
            core.resolved_names()
                .symbol_names
                .get(symbol)
                .is_some_and(|name| name == "Optional")
        })
        .copied()
        .ok_or("core has no Optional enum")?;
    Ok(crate::backend::runtime_symbol(symbol))
}

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
            optional_symbol: optional_symbol()?,
        })
    }

    /// Validate the outcome's root value as the schema's root type.
    /// Returns the number of schema-typed nodes walked.
    pub fn validate(&self) -> Result<usize, String> {
        let mut visited = 0usize;
        self.check(
            &self.run.value,
            &AbiTy::Named(self.schema.root.clone()),
            &mut visited,
        )?;
        Ok(visited)
    }

    fn check(&self, value: &Value, ty: &AbiTy, visited: &mut usize) -> Result<(), String> {
        match ty {
            AbiTy::Named(name) => self.check_named(value, name, visited),
            AbiTy::Optional(inner) => {
                let Value::Variant(symbol, tag, payloads) = value else {
                    return Err(format!("expected an Optional value, got {value:?}"));
                };
                if *symbol != self.optional_symbol {
                    return Err("optional value carries the wrong enum identity".into());
                }
                match (tag, payloads.len()) {
                    // core/Optional.tlk declaration order: some, none.
                    (0, 1) => self.check(&payloads[0], inner, visited),
                    (1, 0) => Ok(()),
                    _ => Err(format!(
                        "malformed Optional value: tag {tag} with {} payloads",
                        payloads.len()
                    )),
                }
            }
            AbiTy::Array(element) => {
                for element_value in self.array_elements(value, element)? {
                    self.check(&element_value, element, visited)?;
                }
                Ok(())
            }
            AbiTy::Tuple(items) => {
                let Value::Tuple(values) = value else {
                    return Err(format!("expected a tuple value, got {value:?}"));
                };
                if values.len() != items.len() {
                    return Err(format!(
                        "tuple arity {} does not match the schema's {}",
                        values.len(),
                        items.len()
                    ));
                }
                for (value, item) in values.iter().zip(items) {
                    self.check(value, item, visited)?;
                }
                Ok(())
            }
        }
    }

    fn check_named(&self, value: &Value, name: &str, visited: &mut usize) -> Result<(), String> {
        match name {
            "Int" => {
                let Value::I64(_) = value else {
                    return Err(format!("expected an Int, got {value:?}"));
                };
                return Ok(());
            }
            "Bool" => {
                let Value::Bool(_) = value else {
                    return Err(format!("expected a Bool, got {value:?}"));
                };
                return Ok(());
            }
            "Byte" => {
                let Value::Byte(_) = value else {
                    return Err(format!("expected a Byte, got {value:?}"));
                };
                return Ok(());
            }
            "Float" => {
                let Value::F64(_) = value else {
                    return Err(format!("expected a Float, got {value:?}"));
                };
                return Ok(());
            }
            "String" => return self.string(value).map(|_| ()),
            _ => {}
        }
        let schema_type = self
            .schema
            .types
            .get(name)
            .ok_or_else(|| format!("value of unknown ABI type `{name}`"))?;
        let expected = self.symbols[name];
        *visited += 1;
        match &schema_type.kind {
            AbiTypeKind::Struct(fields) => {
                let Value::Record(symbol, values) = value else {
                    return Err(format!("expected a `{name}` record, got {value:?}"));
                };
                if *symbol != expected {
                    return Err(format!("record carries the wrong identity for `{name}`"));
                }
                if values.len() != fields.len() {
                    return Err(format!(
                        "`{name}` has {} fields but the schema declares {}",
                        values.len(),
                        fields.len()
                    ));
                }
                for (value, (field, ty)) in values.iter().zip(fields) {
                    self.check(value, ty, visited)
                        .map_err(|err| format!("{name}.{field}: {err}"))?;
                }
                Ok(())
            }
            AbiTypeKind::Enum(variants) => {
                let Value::Variant(symbol, tag, payloads) = value else {
                    return Err(format!("expected a `{name}` variant, got {value:?}"));
                };
                if *symbol != expected {
                    return Err(format!("variant carries the wrong identity for `{name}`"));
                }
                let (variant, payload_types) = variants
                    .get(*tag as usize)
                    .ok_or_else(|| format!("`{name}` has no variant tag {tag}"))?;
                if payloads.len() != payload_types.len() {
                    return Err(format!(
                        "`{name}.{variant}` has {} payloads but the schema declares {}",
                        payloads.len(),
                        payload_types.len()
                    ));
                }
                for (value, ty) in payloads.iter().zip(payload_types) {
                    self.check(value, ty, visited)
                        .map_err(|err| format!("{name}.{variant}: {err}"))?;
                }
                Ok(())
            }
        }
    }

    /// The UTF-8 text of a String-shaped value.
    pub fn string(&self, value: &Value) -> Result<String, String> {
        let Value::Record(symbol, _) = value else {
            return Err(format!("expected a String, got {value:?}"));
        };
        if *symbol != self.string_symbol {
            return Err("string value carries the wrong identity".into());
        }
        let bytes = self.run.string_bytes(value)?;
        String::from_utf8(bytes.to_vec()).map_err(|err| format!("string is not UTF-8: {err}"))
    }

    /// Read an array value's elements out of the machine: `[storage,
    /// count, capacity]`, elements at `storage.base`, one byte per Byte
    /// element, one 8-byte word otherwise (boxed-arena handles for
    /// record, enum, string, optional, and nested-array elements).
    pub fn array_elements(&self, value: &Value, element: &AbiTy) -> Result<Vec<Value>, String> {
        let Value::Record(symbol, fields) = value else {
            return Err(format!("expected an array, got {value:?}"));
        };
        if *symbol != self.array_symbol {
            return Err("array value carries the wrong identity".into());
        }
        let [storage, count, capacity] = fields.as_slice() else {
            return Err("array record does not have Array's shape".into());
        };
        let Value::Record(storage_symbol, storage_fields) = storage else {
            return Err("array storage is not a record".into());
        };
        if *storage_symbol != self.storage_symbol {
            return Err("array storage carries the wrong identity".into());
        }
        let [Value::Ptr(base)] = storage_fields.as_slice() else {
            return Err("array storage does not have Storage's shape".into());
        };
        let (Value::I64(count), Value::I64(capacity)) = (count, capacity) else {
            return Err("array count/capacity are not integers".into());
        };
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

fn element_addr(base: u32, index: usize, stride: u64) -> Result<u32, String> {
    let addr = u64::from(base) + (index as u64) * stride;
    u32::try_from(addr).map_err(|_| "array element address out of range".into())
}

// ===== The adapter (ADR 0043 §5) =====
//
// Convert a validated frontend result into the compiler's own parse
// data: the same `parsing` AST the Rust parser builds, with node ids
// minted here and node meta recorded only where token extents diverge
// from spans (`Func` declaration extents, the for-loop pattern
// replacement). Sub-spans the Talk AST does not yet carry (name spans,
// label spans) and call-arg origins are fabricated as synthesized /
// written for now — they are invisible to the dump round trip and get
// real values as consumers demand them.

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
pub struct BridgedParse {
    pub roots: Vec<Node>,
    pub meta: NodeMetaStorage,
    pub comments: Vec<(u32, u32)>,
    pub failure: Option<(String, String)>,
    pub diags: Vec<(String, String)>,
}

pub fn adapt(run: &RunOutcome, schema: &AbiSchema) -> Result<BridgedParse, String> {
    let mut adapter = ResultAdapter {
        v: ResultValidator::new(run, schema)?,
        boxed: AbiTy::Named("boxed".into()),
        ids: IDGenerator::default(),
        meta: NodeMetaStorage::default(),
    };
    let mut outcome = adapter.record(&run.value.clone(), "ParseOutcome")?;
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
    })
}

struct ResultAdapter<'a, 'io> {
    v: ResultValidator<'a, 'io>,
    /// Any non-scalar element type: selects the boxed read in
    /// `array_elements`.
    boxed: AbiTy,
    ids: IDGenerator,
    meta: NodeMetaStorage,
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

/// A fabricated token pair carrying nothing but extents, for the two
/// places the dump renders `tokens=` (node meta wider than the span).
fn extent_meta(start: u32, end: u32) -> NodeMeta {
    let token = |at: u32| Token {
        kind: TokenKind::Generated,
        start: at,
        end: at,
        line: 0,
        col: 0,
    };
    NodeMeta {
        start: token(start),
        end: token(end),
        identifiers: vec![],
    }
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
        other => return Err(format!("no operator mapping for token kind `{other}`")),
    })
}

impl ResultAdapter<'_, '_> {
    fn id(&mut self) -> NodeID {
        NodeID(FileID(0), self.ids.next_id())
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
        let Value::Record(symbol, values) = value else {
            return Err(format!("expected a `{ty}` record, got {value:?}"));
        };
        if *symbol != self.v.symbols[ty] {
            return Err(format!("record carries the wrong identity for `{ty}`"));
        }
        if values.len() != fields.len() {
            return Err(format!(
                "`{ty}` has {} fields but the schema declares {}",
                values.len(),
                fields.len()
            ));
        }
        Ok(fields
            .iter()
            .zip(values.iter())
            .map(|((name, _), value)| (name.clone(), value.clone()))
            .collect())
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
        let Value::Variant(symbol, tag, payloads) = value else {
            return Err(format!("expected a `{ty}` variant, got {value:?}"));
        };
        if *symbol != self.v.symbols[ty] {
            return Err(format!("variant carries the wrong identity for `{ty}`"));
        }
        let (name, payload_types) = variants
            .get(*tag as usize)
            .ok_or_else(|| format!("`{ty}` has no variant tag {tag}"))?;
        if payloads.len() != payload_types.len() {
            return Err(format!(
                "`{ty}.{name}` has {} payloads but the schema declares {}",
                payloads.len(),
                payload_types.len()
            ));
        }
        Ok((name.clone(), payloads.to_vec()))
    }

    fn opt(&self, value: &Value) -> Result<Option<Value>, String> {
        let Value::Variant(symbol, tag, payloads) = value else {
            return Err(format!("expected an Optional value, got {value:?}"));
        };
        if *symbol != self.v.optional_symbol {
            return Err("optional value carries the wrong enum identity".into());
        }
        match (tag, payloads.len()) {
            (0, 1) => Ok(Some(payloads[0].clone())),
            (1, 0) => Ok(None),
            _ => Err("malformed Optional value".into()),
        }
    }

    fn array(&self, value: &Value) -> Result<Vec<Value>, String> {
        self.v.array_elements(value, &self.boxed)
    }

    fn string(&self, value: &Value) -> Result<String, String> {
        self.v.string(value)
    }

    fn name(&self, value: &Value) -> Result<crate::name::Name, String> {
        Ok(crate::name::Name::Raw(self.string(value)?))
    }

    fn fail(&self, value: &Value) -> Result<(String, String), String> {
        let mut fields = self.record(value, "Fail")?;
        Ok((
            self.string(&take(&mut fields, "code")?)?,
            self.string(&take(&mut fields, "message")?)?,
        ))
    }

    /// A node record's span from its start/end fields.
    fn node_span(
        &self,
        fields: &mut std::collections::HashMap<String, Value>,
    ) -> Result<Span, String> {
        span_from(int(&take(fields, "start")?)?, int(&take(fields, "end")?)?)
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
        let mut fields = self.record(value, "Expr")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let id = self.id();
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
                ExprKind::Member(self.receiver(&p[1])?, label, Span::SYNTHESIZED)
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
                let mut arms = Vec::new();
                for arm in self.array(&p[1])? {
                    arms.push(self.match_arm(&arm)?);
                }
                ExprKind::Match(Box::new(self.one_expr(&p[0])?), arms)
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
                effect_name_span: Span::SYNTHESIZED,
                type_args: self.generic_args(&p[1])?,
                args: self.call_args(&p[2])?,
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
                name_span: Span::SYNTHESIZED,
                args: self.exprs(&p[1])?,
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
            let mut fields = self.record(arg, "CallArg")?;
            let label = match self.opt(&take(&mut fields, "label")?)? {
                Some(name) => crate::label::Label::Named(self.string(&name)?),
                None => crate::label::Label::Positional(index),
            };
            let mode = self
                .opt(&take(&mut fields, "mode")?)?
                .map(|mode| self.arg_mode(&mode))
                .transpose()?;
            let arg_value = self.expr(&take(&mut fields, "value")?)?;
            let span = self.node_span(&mut fields)?;
            args.push(CallArg {
                id: self.id(),
                label,
                label_span: Span::SYNTHESIZED,
                origin: CallArgOrigin::Written,
                value: arg_value,
                span,
                mode,
                mode_span: None,
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
        let mut fields = self.record(value, "Block")?;
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
            id: self.id(),
            args,
            body,
            span,
        })
    }

    fn parameter(&mut self, value: &Value) -> Result<Parameter, String> {
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
        let name_span = span_from(
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
        let type_annotation = self.opt_type(&take(&mut fields, "annotation")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(Parameter {
            id: self.id(),
            label,
            label_span: None,
            name,
            name_span,
            type_annotation,
            span,
            mode,
            mode_span: None,
        })
    }

    fn match_arm(&mut self, value: &Value) -> Result<MatchArm, String> {
        let mut fields = self.record(value, "MatchArm")?;
        let pattern = self.pattern(&take(&mut fields, "pattern")?)?;
        let body = self.block(&take(&mut fields, "body")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(MatchArm {
            id: self.id(),
            pattern,
            body,
            span,
        })
    }

    fn record_field(&mut self, value: &Value) -> Result<RecordField, String> {
        let mut fields = self.record(value, "RecordField")?;
        let label = self.name(&take(&mut fields, "label")?)?;
        let field_value = self.expr(&take(&mut fields, "value")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(RecordField {
            id: self.id(),
            label,
            label_span: Span::SYNTHESIZED,
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
        let mut fields = self.record(value, "IRInstruction")?;
        let name = self.string(&take(&mut fields, "name")?)?;
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
            id: self.id(),
            span,
            binds,
            instr_name_span: Span::SYNTHESIZED,
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
        let mut fields = self.record(value, "Stmt")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let id = self.id();
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
                effect_name_span: Span::SYNTHESIZED,
                body: self.block(&p[1])?,
            },
            other => return Err(format!("unknown StmtKind variant `{other}`")),
        };
        Ok(Stmt { id, kind, span })
    }

    fn pattern(&mut self, value: &Value) -> Result<Pattern, String> {
        let mut fields = self.record(value, "Pattern")?;
        let kind_value = take(&mut fields, "kind")?;
        let meta_start = int(&take(&mut fields, "meta_start")?)?;
        let meta_end = int(&take(&mut fields, "meta_end")?)?;
        let span = self.node_span(&mut fields)?;
        let id = self.id();
        if meta_start >= 0 {
            self.meta.insert(
                id,
                extent_meta(
                    u32::try_from(meta_start).map_err(|_| "pattern extent out of range")?,
                    u32::try_from(meta_end).map_err(|_| "pattern extent out of range")?,
                ),
            );
        }
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
                for label in self.array(&p[4])? {
                    field_labels.push(self.opt(&label)?.map(|name| self.name(&name)).transpose()?);
                }
                PatternKind::Variant {
                    enum_name,
                    enum_generics,
                    variant_name: self.string(&p[2])?,
                    variant_name_span: Span::SYNTHESIZED,
                    fields: self.patterns(&p[3])?,
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
        let mut fields = self.record(value, "RecordFieldPattern")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let (variant, p) = self.variant(&kind_value, "RecordFieldPatternKind")?;
        let kind = match variant.as_str() {
            "bind_field" => RecordFieldPatternKind::Bind(self.name(&p[0])?),
            "equals_field" => RecordFieldPatternKind::Equals {
                name: self.name(&p[0])?,
                name_span: Span::SYNTHESIZED,
                value: self.pattern(&p[1])?,
            },
            "rest_field" => RecordFieldPatternKind::Rest,
            other => return Err(format!("unknown RecordFieldPatternKind variant `{other}`")),
        };
        Ok(RecordFieldPattern {
            id: self.id(),
            span,
            kind,
        })
    }

    fn type_annotation(&mut self, value: &Value) -> Result<TypeAnnotation, String> {
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
                member_span: Span::SYNTHESIZED,
                member_generics: self.generic_args(&p[2])?,
            },
            "nominal" => TypeAnnotationKind::Nominal {
                name: self.name(&p[0])?,
                name_span: Span::SYNTHESIZED,
                generics: self.generic_args(&p[1])?,
            },
            "tuple" => TypeAnnotationKind::Tuple(self.types(&p[0])?),
            "record_type" => {
                let mut record_fields = Vec::new();
                for field in self.array(&p[0])? {
                    let mut inner = self.record(&field, "RecordFieldTypeAnnotation")?;
                    let label = self.name(&take(&mut inner, "label")?)?;
                    let field_value = self.type_annotation(&take(&mut inner, "value")?)?;
                    let field_span = self.node_span(&mut inner)?;
                    record_fields.push(RecordFieldTypeAnnotation {
                        id: self.id(),
                        label,
                        label_span: Span::SYNTHESIZED,
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
                    let mut inner = self.record(&binding, "AnyAssocBinding")?;
                    let name = self.name(&take(&mut inner, "name")?)?;
                    let binding_value = self.type_annotation(&take(&mut inner, "value")?)?;
                    let binding_span = self.node_span(&mut inner)?;
                    bindings.push(AnyAssocBinding {
                        id: self.id(),
                        name,
                        name_span: Span::SYNTHESIZED,
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
            id: self.id(),
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
        let spans = vec![Span::SYNTHESIZED; names.len()];
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
        let mut fields = self.record(value, "StaticExpr")?;
        let kind_value = take(&mut fields, "kind")?;
        let span = self.node_span(&mut fields)?;
        let (variant, p) = self.variant(&kind_value, "StaticExprKind")?;
        let kind = match variant.as_str() {
            "int_literal" => StaticExprKind::Int(self.string(&p[0])?),
            "bool_literal" => StaticExprKind::Bool(boolean(&p[0])?),
            "unqualified_case" => StaticExprKind::UnqualifiedCase {
                name: self.string(&p[0])?,
                name_span: Span::SYNTHESIZED,
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
            id: self.id(),
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
        let mut fields = self.record(value, "GenericDecl")?;
        let name = self.name(&take(&mut fields, "name")?)?;
        let generics = self.generic_decls(&take(&mut fields, "generics")?)?;
        let conformances = self.types(&take(&mut fields, "conformances")?)?;
        let default = self
            .opt(&take(&mut fields, "default_value")?)?
            .map(|arg| self.generic_arg(&arg))
            .transpose()?;
        let static_ty = self.opt_type(&take(&mut fields, "static_ty")?)?;
        let span = self.node_span(&mut fields)?;
        Ok(GenericDecl {
            id: self.id(),
            name,
            name_span: Span::SYNTHESIZED,
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
        let mut fields = self.record(&clause, "WhereClause")?;
        let mut predicates = Vec::new();
        for predicate in self.array(&take(&mut fields, "predicates")?)? {
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
                id: self.id(),
                span,
                kind,
            });
        }
        let span = self.node_span(&mut fields)?;
        Ok(Some(WhereClause {
            id: self.id(),
            span,
            predicates,
        }))
    }

    fn func(&mut self, value: &Value, origin: FuncOrigin) -> Result<Func, String> {
        let mut fields = self.record(value, "Func")?;
        let name = self.name(&take(&mut fields, "name")?)?;
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
        let meta_start = int(&take(&mut fields, "meta_start")?)?;
        let meta_end = int(&take(&mut fields, "meta_end")?)?;
        let start = int(&take(&mut fields, "start")?)?;
        let end = int(&take(&mut fields, "end")?)?;
        let id = self.id();
        if meta_start >= 0 && (meta_start != start || meta_end != end) {
            self.meta.insert(
                id,
                extent_meta(
                    u32::try_from(meta_start).map_err(|_| "func extent out of range")?,
                    u32::try_from(meta_end).map_err(|_| "func extent out of range")?,
                ),
            );
        }
        Ok(Func {
            id,
            name,
            name_span: Span::SYNTHESIZED,
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
            id: self.id(),
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
        let mut fields = self.record(value, "Body")?;
        let mut decls = Vec::new();
        for decl in self.array(&take(&mut fields, "decls")?)? {
            decls.push(self.decl(&decl)?);
        }
        let span = self.node_span(&mut fields)?;
        Ok(Body {
            id: self.id(),
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
        let mut fields = self.record(value, "Decl")?;
        let kind_value = take(&mut fields, "kind")?;
        let visibility = if boolean(&take(&mut fields, "is_public")?)? {
            Visibility::Public
        } else {
            Visibility::Private
        };
        let span = self.node_span(&mut fields)?;
        let id = self.id();
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
                                alias: self
                                    .opt(&take(&mut inner, "alias")?)?
                                    .map(|alias| self.string(&alias))
                                    .transpose()?,
                                span: Span::SYNTHESIZED,
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
                    path_span: Span::SYNTHESIZED,
                })
            }
            "func_decl" => DeclKind::Func(self.func(&p[0], FuncOrigin::Decl)?),
            "func_signature" => DeclKind::FuncSignature(self.func_signature(&p[0])?),
            "struct_decl" => DeclKind::Struct {
                name: self.name(&p[0])?,
                name_span: Span::SYNTHESIZED,
                generics: self.generic_decls(&p[1])?,
                where_clause: self.where_clause(&p[2])?,
                body: self.body(&p[3])?,
                linear: boolean(&p[4])?,
                heap: boolean(&p[5])?,
            },
            "enum_decl" => DeclKind::Enum {
                name: self.name(&p[0])?,
                name_span: Span::SYNTHESIZED,
                generics: self.generic_decls(&p[1])?,
                where_clause: self.where_clause(&p[2])?,
                body: self.body(&p[3])?,
                linear: boolean(&p[4])?,
            },
            "protocol_decl" => DeclKind::Protocol {
                name: self.name(&p[0])?,
                name_span: Span::SYNTHESIZED,
                generics: self.generic_decls(&p[1])?,
                where_clause: self.where_clause(&p[2])?,
                body: self.body(&p[3])?,
                conformances: self.types(&p[4])?,
            },
            "enum_variant" => {
                let mut payload_labels = Vec::new();
                for label in self.array(&p[3])? {
                    payload_labels
                        .push(self.opt(&label)?.map(|name| self.name(&name)).transpose()?);
                }
                DeclKind::EnumVariant {
                    name: self.name(&p[0])?,
                    name_span: Span::SYNTHESIZED,
                    generics: self.generic_decls(&p[1])?,
                    payloads: self.types(&p[2])?,
                    payload_labels,
                    result: self.opt_type(&p[4])?,
                }
            }
            "extend_decl" => {
                let mut application = self.record(&p[1], "TypeApplication")?;
                let head_name = self.name(&take(&mut application, "name")?)?;
                let head_args = self.generic_args(&take(&mut application, "args")?)?;
                let head_span = self.node_span(&mut application)?;
                DeclKind::Extend {
                    binders: self.generic_decls(&p[0])?,
                    head: TypeApplication {
                        id: self.id(),
                        span: head_span,
                        name: head_name,
                        name_span: Span::SYNTHESIZED,
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
                name_span: Span::SYNTHESIZED,
                is_static: boolean(&p[1])?,
                type_annotation: self.opt_type(&p[2])?,
                default_value: self.opt_expr(&p[3])?,
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
                Span::SYNTHESIZED,
                self.type_annotation(&p[1])?,
            ),
            "effect_decl" => DeclKind::Effect {
                name: self.name(&p[0])?,
                name_span: Span::SYNTHESIZED,
                generics: self.generic_decls(&p[1])?,
                where_clause: self.where_clause(&p[2])?,
                params: {
                    let mut params = Vec::new();
                    for parameter in self.array(&p[3])? {
                        params.push(self.parameter(&parameter)?);
                    }
                    params
                },
                ret: self.type_annotation(&p[4])?,
            },
            "associated_decl" => DeclKind::Associated {
                generic: self.generic_decl(&p[0])?,
                where_clause: self.where_clause(&p[1])?,
            },
            "macro_decl" => {
                let mut params = Vec::new();
                for name in self.array(&p[1])? {
                    params.push(MacroParameter {
                        name: self.string(&name)?,
                        span: Span::SYNTHESIZED,
                    });
                }
                DeclKind::Macro {
                    name: self.string(&p[0])?,
                    name_span: Span::SYNTHESIZED,
                    params,
                    template: self.expr(&p[2])?,
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
    use super::*;
    use crate::compiling::abi::parse_schema;
    use talk_runtime::interp::{Budgets, HostValue};
    use talk_runtime::io::CaptureIO;

    /// Every structured parse result the frontend artifact produces over
    /// the corpus validates against the checked-in ABI descriptor: the
    /// trust seam holds for real crossings, not just for the schema's
    /// own round-trip.
    #[test]
    fn structured_results_validate_over_corpus() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let module = crate::compiling::frontend::load(root).expect("frontend artifact loads");
        let abi_text = std::fs::read_to_string(crate::compiling::frontend::abi_path(root))
            .expect("ABI descriptor exists");
        let schema = parse_schema(&abi_text).expect("ABI descriptor parses");

        let mut covered: Vec<std::path::PathBuf> = Vec::new();
        for dir in [
            "tests/parser",
            "tests/parser/expr",
            "tests/parser/pattern",
            "tests/parser/type",
            "tests/parser/block",
            "tests/parser/tokentree",
            "tests/parser/lenient",
            "tests/parser/unicode",
            "core",
            "stdlib",
            "tests/examples",
            "examples",
        ] {
            for entry in std::fs::read_dir(root.join(dir)).expect("corpus dir") {
                let path = entry.expect("corpus entry").path();
                if path.extension().is_some_and(|ext| ext == "tlk") {
                    covered.push(path);
                }
            }
        }
        covered.sort();
        assert!(!covered.is_empty());

        let mut walked = 0usize;
        for path in covered {
            let source = std::fs::read_to_string(&path).expect("read corpus source");
            let mut io = CaptureIO::default();
            let run = talk_runtime::interp::run_export(
                &module,
                "parse_file_source",
                &[HostValue::String(source.into_bytes())],
                crate::backend::string_shape(),
                Budgets::default(),
                &mut io,
            )
            .unwrap_or_else(|error| panic!("parse_file_source failed on {}: {error}", path.display()));
            let validator = ResultValidator::new(&run, &schema).expect("validator builds");
            walked += validator
                .validate()
                .unwrap_or_else(|error| panic!("validation failed on {}: {error}", path.display()));
        }
        assert!(walked > 10_000, "suspiciously few schema nodes: {walked}");
    }

    /// The adapter round trip (ADR 0043 §5): bridge every corpus file's
    /// structured result into the compiler's own parse AST and render it
    /// through the reference dump machinery — byte-identical to what the
    /// Rust parser's own AST renders (token section excluded; tokens are
    /// internal to the frontend and do not cross the ABI).
    #[test]
    fn bridged_results_render_identically_over_corpus() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let module = crate::compiling::frontend::load(root).expect("frontend artifact loads");
        let abi_text = std::fs::read_to_string(crate::compiling::frontend::abi_path(root))
            .expect("ABI descriptor exists");
        let schema = parse_schema(&abi_text).expect("ABI descriptor parses");

        let mut covered: Vec<std::path::PathBuf> = Vec::new();
        for dir in [
            "tests/parser",
            "tests/parser/expr",
            "tests/parser/pattern",
            "tests/parser/type",
            "tests/parser/block",
            "tests/parser/tokentree",
            "tests/parser/lenient",
            "tests/parser/unicode",
            "core",
            "stdlib",
            "tests/examples",
            "examples",
        ] {
            for entry in std::fs::read_dir(root.join(dir)).expect("corpus dir") {
                let path = entry.expect("corpus entry").path();
                if path.extension().is_some_and(|ext| ext == "tlk") {
                    covered.push(path);
                }
            }
        }
        covered.sort();

        for path in covered {
            let source = std::fs::read_to_string(&path).expect("read corpus source");
            let mut io = CaptureIO::default();
            let run = talk_runtime::interp::run_export(
                &module,
                "parse_file_source",
                &[HostValue::String(source.clone().into_bytes())],
                crate::backend::string_shape(),
                Budgets::default(),
                &mut io,
            )
            .unwrap_or_else(|error| panic!("parse_file_source failed on {}: {error}", path.display()));
            let bridged = adapt(&run, &schema)
                .unwrap_or_else(|error| panic!("bridging failed on {}: {error}", path.display()));
            let rendered = crate::parsing::dump::render_bridged(
                &source,
                &bridged.roots,
                &bridged.meta,
                &bridged.comments,
                bridged.failure.as_ref(),
                &bridged.diags,
            );
            let expected = crate::parsing::dump::dump_after_tokens(&source);
            assert_eq!(rendered, expected, "bridge divergence on {}", path.display());
        }
    }

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
