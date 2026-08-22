//! The typed compiler tree: an owned, desugared tree produced by the typed
//! program builder. Flow and lowering consume this typed tree instead of the
//! parser AST, so a single semantic representation serves both.
//!
//! Design notes (see the staged plan):
//! - **Owned, no lifetimes** — built once, freely shared/stored.
//! - **NodeID-preserving** — every node carries the same `NodeID` as the AST node
//!   it came from, so the type checker's NodeID-keyed tables still resolve.
//! - **Stripped** — surface-only and already-desugared forms are gone:
//!   `Unary`/`Binary` (→ protocol calls), `For` (→ loop+match), `Incomplete`
//!   (LSP-only), `Import` (resolved away), comments/trivia, and `*_span` fields
//!   (a single `span` is kept for diagnostics).

pub mod facts;


use derive_visitor::{Drive, DriveMut};

use crate::label::Label;
use crate::{
    name::Name,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute,
        decl::{Import, ReceiverMode, Visibility},
        func::{CaptureSpec, EffectSet},
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        type_annotation::TypeAnnotation,
        type_application::TypeApplication,
        where_clause::WhereClause,
    },
    parsing::span::Span,
};

/// One source file in the typed compiler tree: the analogue of
/// `AST<NameResolved>` for downstream phases. Carries the same `file_id` and the
/// lowered roots.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TypedFile {
    pub file_id: crate::node_id::FileID,
    pub roots: Vec<Node>,
    /// Wrapper grafts (`x as T`, 1-tuples, `?`/`!` plans) keep the
    /// wrapper's id; the erased inner node's id is recorded here as
    /// (inner, wrapper) so editor queries at the inner id resolve to the
    /// grafted node's facts instead of a hole.
    #[serde(default)]
    pub grafted: Vec<(NodeID, NodeID)>,
}

/// The umbrella node type for a block body (`Vec<Node>`), mirroring the AST's
/// heterogeneous `Node` but only the variants a block body actually holds.
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum Node {
    Decl(Decl),
    Stmt(Stmt),
    Expr(Expr),
}

// ----- Expressions ---------------------------------------------------------

/// Per-expression clone facts selected by type checking.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ExprOwnership {
    /// This expression contains an explicit clone coercion.
    pub auto_clone: bool,
}

#[derive(Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Expr {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: ExprKind,
    #[drive(skip)]
    pub span: Span,
    /// Clone facts for this expression (see [`ExprOwnership`]).
    #[drive(skip)]
    pub ownership: ExprOwnership,
    /// This expression's type, baked on by the typed-program builder (read once
    /// from the checker's tables). Every checked expression has one — `Ty::Error`
    /// at worst — so downstream stages read it here instead of a NodeID-keyed
    /// table.
    #[drive(skip)]
    pub ty: crate::types::ty::Ty,
    /// How a member access / construction resolved (the checker's
    /// `member_resolutions`), baked on by the typed-program builder; `None`
    /// where the node is not a resolved member.
    #[drive(skip)]
    pub member_resolution: Option<crate::types::output::MemberResolution>,
    /// The one concrete assignment a stored rank-N closure compiles at
    /// (the checker's `field_specializations`), when this node stores a
    /// polymorphic closure — a func literal field or a generic
    /// reference. Lowering extends its frame substitution with these.
    #[drive(skip)]
    pub specialization: Option<Vec<(Symbol, crate::types::ty::Ty)>>,
    /// When this projection reads a rigidly compiled closure: the
    /// hidden witness-block layout the call must append, as
    /// (rigid parameter, this use's argument) pairs in scheme order.
    #[drive(skip)]
    pub witness_layout: Option<Vec<(Symbol, crate::types::ty::Ty)>>,
    /// This call/constructor's per-call-site type instantiation (the checker's
    /// `instantiations`), baked on by the typed-program builder; read for θ at
    /// the call site.
    #[drive(skip)]
    pub instantiation: Option<Vec<(Symbol, crate::types::ty::Ty)>>,
    /// The existential pack the checker recorded at this node (the checker's
    /// `existential_packs`), baked on by the typed-program builder; raw
    /// (un-substituted).
    #[drive(skip)]
    pub existential_pack: Option<crate::types::output::ExistentialPack>,
    /// The callable symbol typing selected for this statically resolved
    /// call node (ADR 0041), baked on by the typed-program builder.
    #[drive(skip)]
    pub selected_callable: Option<Symbol>,
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expr(id: {:?}, kind: {:?})", self.id, self.kind)
    }
}

/// A checked float literal value. Equality is bit identity — these are
/// canonical literal values, never arithmetic results.
#[derive(Debug, Clone, Copy, serde::Serialize, serde::Deserialize)]
pub struct FloatValue(pub f64);

impl PartialEq for FloatValue {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for FloatValue {}

/// A literal constant — one atom form instead of five expression forms,
/// carrying the checked canonical value (LIT-01 integers; lexer-validated
/// escapes). Lowering never reparses source text (ADR 0038); the source
/// spelling stays on the parse tree for diagnostics and formatting.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Literal {
    Int(i64),
    Float(FloatValue),
    Bool(bool),
    String(String),
    Character(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum ExprKind {
    InlineIR(InlineIRInstruction),
    CallEffect {
        #[drive(skip)]
        effect_name: Name,
        #[drive(skip)]
        type_args: Vec<crate::node_kinds::generic_arg::GenericArg>,
        args: Vec<CallArg>,
        /// The effect's checked contract (ADR 0038): declared parameter
        /// types and the type-generic witness-block layout.
        #[drive(skip)]
        contract: crate::types::output::EffectContract,
    },
    LiteralArray(Vec<Expr>),
    Lit(#[drive(skip)] Literal),
    Tuple(Vec<Expr>),
    Block(Block),
    /// A lexical compile-time unsafe boundary. Lowering executes its body
    /// as an ordinary block; the marker remains for validation.
    Unsafe(Block),
    Call {
        callee: Box<Expr>,
        #[drive(skip)]
        type_args: Vec<crate::node_kinds::generic_arg::GenericArg>,
        args: Vec<CallArg>,
    },
    /// Lowered form of the real Copy/Clone `clone()` method.
    Clone(Box<Expr>),
    Member(Option<Box<Expr>>, #[drive(skip)] Label),
    /// An enum-variant construction (`.some(x)`, `Optional.some(x)`,
    /// payload-less `.none`), split from `Call`/`Member` at build time by
    /// the checker's member resolution against the enum catalog. Payloads
    /// are in source order; the node's baked `instantiation` is the
    /// constructor's (for GADT evidence). A payload-carrying variant used
    /// bare (as a function value) stays a `Member`.
    Con {
        #[drive(skip)]
        enum_symbol: crate::name_resolution::symbol::Symbol,
        #[drive(skip)]
        tag: u16,
        #[drive(skip)]
        variant_symbol: crate::name_resolution::symbol::Symbol,
        args: Vec<Expr>,
    },
    /// A stored-field read (`x.f` where `f` is a struct field), split from
    /// `Member` at build time by the checker's member resolution — the same
    /// judgment (`stored_field_symbol`) the place computation uses, so
    /// "what is a place" is structural from here on. `Member` keeps method
    /// references and leading-dot variant forms.
    Proj(
        Box<Expr>,
        #[drive(skip)] Label,
        #[drive(skip)] crate::name_resolution::symbol::Symbol,
    ),
    Func(Box<Func>),
    Variable(#[drive(skip)] Name),
    Constructor(#[drive(skip)] Name),
    Match(Box<Expr>, Vec<MatchArm>),
    /// A reference to a MIR-statement-produced temporary — the operand
    /// bridge. The builder substitutes one where a flattened construct
    /// (an expression-position match, whose arms deliver the value to the
    /// construct's join) stood in a consuming statement's expression.
    /// An atom: no place, no transfer effects (its value's consumption
    /// happened at the arm tails); lowering resolves it from the join
    /// continuation's parameter. Never appears in the typed tree itself —
    /// only in builder-emitted statement copies.
    Temp(#[drive(skip)] u32),
    RecordLiteral {
        fields: Vec<RecordField>,
        spread: Option<Box<Expr>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct InlineIRInstruction {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    pub binds: Vec<Expr>,
    /// The checked, target-neutral operation (ADR 0038): typing
    /// validated the operation, scalar types, and operands; lowering
    /// only emits the corresponding MIR instruction.
    #[drive(skip)]
    pub kind: crate::types::output::CheckedIrKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct CallArg {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Label,
    pub value: Expr,
    /// The call-site ownership marker, if the source spelled one
    /// (ADR 0018): `consume`/`copy`/`borrow`/`mut` on the argument.
    #[drive(skip)]
    pub mode: Option<crate::node_kinds::call_arg::ArgMode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct RecordField {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct MatchArm {
    #[drive(skip)]
    pub id: NodeID,
    pub pattern: Pattern,
    pub body: Block,
}

// ----- Patterns ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Pattern {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: PatternKind,
    #[drive(skip)]
    pub span: Span,
    /// This occurrence's checked type (ADR 0038), pre-view — a binder's
    /// type keeps the borrow it holds. `None` only on synthesized
    /// patterns, whose types come from their construction site.
    #[drive(skip)]
    pub ty: Option<crate::types::ty::Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum PatternKind {
    LiteralInt(#[drive(skip)] i64),
    LiteralFloat(#[drive(skip)] FloatValue),
    /// The unescaped character value.
    LiteralCharacter(#[drive(skip)] String),
    /// The unescaped string value.
    LiteralString(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    Bind(#[drive(skip)] Name),
    Tuple(Vec<Pattern>),
    Or(Vec<Pattern>),
    Wildcard,
    Variant {
        #[drive(skip)]
        enum_name: Option<Name>,
        #[drive(skip)]
        variant_name: String,
        /// The checked constructor identity (typing's member resolution),
        /// baked at build time. `None` only on elaboration-synthesized
        /// patterns, whose enum comes from the scrutinee type (ADR 0038).
        #[drive(skip)]
        resolved: Option<Symbol>,
        fields: Vec<Pattern>,
    },
    Record {
        fields: Vec<RecordFieldPattern>,
        /// One slot per row field in layout order (ADR 0038): the slot
        /// type and the index into `fields` of the written field
        /// covering it. `None` for the whole table when the row stayed
        /// open or unresolved — lowering rejects those as unsupported.
        #[drive(skip)]
        slots: Option<Vec<(crate::types::ty::Ty, Option<usize>)>>,
    },
    Struct {
        #[drive(skip)]
        struct_name: Option<Name>,
        fields: Vec<Pattern>,
        #[drive(skip)]
        field_names: Vec<Name>,
        #[drive(skip)]
        rest: bool,
        /// One slot per stored field in declaration order (ADR 0038):
        /// the instantiated field type and the index into `fields` of
        /// the written sub-pattern covering it (`None` = left to `..`,
        /// matched as a wildcard).
        #[drive(skip)]
        slots: Vec<(crate::types::ty::Ty, Option<usize>)>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct RecordFieldPattern {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: RecordFieldPatternKind,
    /// The slot's checked type (ADR 0038) — also the type of the label
    /// bind a pun or `label: pattern` introduces. `None` only on
    /// synthesized fields.
    #[drive(skip)]
    pub ty: Option<crate::types::ty::Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum RecordFieldPatternKind {
    Bind(#[drive(skip)] Name),
    Equals {
        #[drive(skip)]
        name: Name,
        value: Pattern,
    },
    Rest,
}

impl Pattern {
    pub fn collect_binders(&self) -> Vec<(NodeID, Symbol)> {
        let mut result: Vec<(NodeID, Symbol)> = vec![];
        match &self.kind {
            PatternKind::LiteralInt(_)
            | PatternKind::LiteralFloat(_)
            | PatternKind::LiteralCharacter(_)
            | PatternKind::LiteralString(_)
            | PatternKind::LiteralTrue
            | PatternKind::LiteralFalse
            | PatternKind::Wildcard => {}
            PatternKind::Or(patterns) => {
                // Every alternative binds the same names to the same
                // symbols; collect each binder once, not once per
                // alternative (a duplicate would double its scope drop).
                for pattern in patterns {
                    for (id, symbol) in pattern.collect_binders() {
                        if !result.iter().any(|(_, seen)| *seen == symbol) {
                            result.push((id, symbol));
                        }
                    }
                }
            }
            PatternKind::Tuple(patterns) => {
                for pattern in patterns {
                    result.extend(pattern.collect_binders());
                }
            }
            PatternKind::Bind(name) => {
                if let Ok(sym) = name.symbol() {
                    result.push((self.id, sym));
                }
            }
            PatternKind::Variant { fields, .. } => {
                for pattern in fields {
                    result.extend(pattern.collect_binders());
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    match &field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            if let Ok(sym) = name.symbol() {
                                result.push((field.id, sym));
                            }
                        }
                        RecordFieldPatternKind::Equals { name, value } => {
                            if let Ok(sym) = name.symbol() {
                                result.push((field.id, sym));
                            }
                            result.extend(value.collect_binders());
                        }
                        RecordFieldPatternKind::Rest => {}
                    }
                }
            }
            PatternKind::Struct { fields, .. } => {
                for pattern in fields {
                    result.extend(pattern.collect_binders());
                }
            }
        }
        result
    }
}

// ----- Parameters ---------------------------------------------------------

/// A function/closure parameter with its checker-assigned type baked on
/// (`None` when the checker recorded no type for this binder). The typed tree carries
/// the type here so downstream stages never look it up by `NodeID`.
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Parameter {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub name_span: Span,
    pub type_annotation: Option<TypeAnnotation>,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub ty: Option<crate::types::ty::Ty>,
}

// ----- Blocks and statements ----------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Block {
    #[drive(skip)]
    pub id: NodeID,
    pub args: Vec<Parameter>,
    pub body: Vec<Node>,
    #[drive(skip)]
    pub span: Span,
    /// Frame facts, published only on blocks that are frame roots — a
    /// function or initializer body or a handler clause (ADR 0038).
    /// Interior blocks carry `None`.
    #[drive(skip)]
    pub frame: Option<FrameFacts>,
}

/// Frame-level lexical facts, computed once at typed-tree build: the
/// closure environment and assignment-conversion sets that lowering
/// consumes without re-walking the tree (ADR 0038 checked captures,
/// structural half — modes and Copy evidence follow with the checker's
/// capture legality).
#[derive(Debug, Clone, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub struct FrameFacts {
    /// Free frame-local variables — used in this frame or under one of
    /// its nested function values, bound in an enclosing frame — in
    /// first-use order (the closure-environment layout).
    pub captured: Vec<Symbol>,
    /// Assignment-converted symbols: assigned somewhere in the frame and
    /// referenced under a nested function value, so the binding becomes
    /// a shared mutable cell (Kranz et al., ORBIT, SIGPLAN 1986).
    pub celled: rustc_hash::FxHashSet<Symbol>,
    /// Symbols referenced from inside a nested function value (the
    /// letrec decision for local function binders).
    pub nested_refs: rustc_hash::FxHashSet<Symbol>,
    /// Symbols assigned anywhere in the frame (a superset of `celled`):
    /// a loan binding that is later reassigned cannot stay a loan —
    /// the slot must own from birth (docs/ownership.md).
    pub assigned: rustc_hash::FxHashSet<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Stmt {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: StmtKind,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum StmtKind {
    Expr(Expr),
    If(Expr, Block, Option<Block>),
    Return(Option<Expr>),
    Break,
    Assignment(Box<Expr>, Box<Expr>),
    Loop(Option<Expr>, Block),
    Continue,
    /// `'continue` — resumes the enclosing handler's perform, optionally
    /// with a value.
    Resume(Option<Expr>),
    Handling {
        #[drive(skip)]
        effect_name: Name,
        body: Block,
        /// The effect's checked contract (ADR 0038), mirroring the
        /// perform side's witness-block layout.
        #[drive(skip)]
        contract: crate::types::output::EffectContract,
    },
}

// ----- Functions and declarations -----------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Func {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub name: Name,
    #[drive(skip)]
    pub effects: EffectSet,
    /// The function's finalized callable contract. Explicit effect
    /// annotations appear here as conservative bounds; inferred functions
    /// carry their solved latent row.
    #[drive(skip)]
    pub scheme: crate::types::ty::Scheme,
    /// The one concrete assignment this closure compiles at, when it is
    /// a stored rank-N field literal (see `Expr::specialization`).
    #[drive(skip)]
    pub specialization: Option<Vec<(Symbol, crate::types::ty::Ty)>>,
    /// The declared receiver mode (ADR 0038): `mut func` receivers write
    /// back through the private tuple-return convention. `None` off
    /// methods.
    #[drive(skip)]
    pub receiver: ReceiverMode,
    /// The binding symbol when the top-level `let name = <func>` desugar
    /// (a `func name` declaration) binds this function: the binding is
    /// the callable's identity for calls and entry selection (ADR 0038).
    #[drive(skip)]
    pub bound_as: Option<Symbol>,
    pub generics: Vec<GenericDecl>,
    #[drive(skip)]
    pub captures: Vec<CaptureSpec>,
    #[drive(skip)]
    pub where_clause: Option<WhereClause>,
    pub params: Vec<Parameter>,
    pub body: Block,
    #[drive(skip)]
    pub ret: Option<TypeAnnotation>,
    #[drive(skip)]
    pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Body {
    #[drive(skip)]
    pub id: NodeID,
    pub decls: Vec<Decl>,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub struct Decl {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: DeclKind,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub visibility: Visibility,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut, serde::Serialize, serde::Deserialize)]
pub enum DeclKind {
    Effect {
        #[drive(skip)]
        name: Name,
        generics: Vec<GenericDecl>,
        #[drive(skip)]
        where_clause: Option<WhereClause>,
        params: Vec<Parameter>,
        #[drive(skip)]
        ret: TypeAnnotation,
    },
    Struct {
        #[drive(skip)]
        name: Name,
        generics: Vec<GenericDecl>,
        #[drive(skip)]
        where_clause: Option<WhereClause>,
        body: Body,
    },
    Let {
        lhs: Pattern,
        #[drive(skip)]
        type_annotation: Option<TypeAnnotation>,
        rhs: Option<Expr>,
        /// A `consume`/`mut` mark on the binding's source, preserved on
        /// the elaborated hidden-source bind of a `for` statement.
        #[drive(skip)]
        source_mode: Option<crate::node_kinds::call_arg::ArgMode>,
    },
    Protocol {
        #[drive(skip)]
        name: Name,
        generics: Vec<GenericDecl>,
        #[drive(skip)]
        where_clause: Option<WhereClause>,
        body: Body,
        #[drive(skip)]
        conformances: Vec<TypeAnnotation>,
    },
    Init {
        #[drive(skip)]
        name: Name,
        params: Vec<Parameter>,
        body: Block,
    },
    Property {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        is_static: bool,
        #[drive(skip)]
        type_annotation: Option<TypeAnnotation>,
        default_value: Option<Expr>,
    },
    Method {
        func: Box<Func>,
        #[drive(skip)]
        is_static: bool,
        #[drive(skip)]
        receiver_mode: ReceiverMode,
    },
    Associated {
        generic: GenericDecl,
        #[drive(skip)]
        where_clause: Option<WhereClause>,
    },
    Func(Func),
    Extend {
        binders: Vec<GenericDecl>,
        #[drive(skip)]
        head: TypeApplication,
        #[drive(skip)]
        conformances: Vec<TypeAnnotation>,
        #[drive(skip)]
        where_clause: Option<WhereClause>,
        body: Body,
    },
    Enum {
        #[drive(skip)]
        name: Name,
        generics: Vec<GenericDecl>,
        #[drive(skip)]
        where_clause: Option<WhereClause>,
        body: Body,
    },
    EnumVariant {
        #[drive(skip)]
        name: Name,
        generics: Vec<GenericDecl>,
        #[drive(skip)]
        payloads: Vec<TypeAnnotation>,
        #[drive(skip)]
        payload_labels: Vec<Option<Name>>,
        #[drive(skip)]
        result: Option<TypeAnnotation>,
    },
    FuncSignature(#[drive(skip)] FuncSignature),
    MethodRequirement {
        #[drive(skip)]
        signature: FuncSignature,
        #[drive(skip)]
        receiver_mode: ReceiverMode,
    },
    InitRequirement {
        #[drive(skip)]
        signature: FuncSignature,
    },
    TypeAlias(#[drive(skip)] Name, #[drive(skip)] TypeAnnotation),
    /// Imports are resolved away during name resolution; kept as an inert marker
    /// so a 1:1 lowering can carry the original node id, never traversed.
    Import(#[drive(skip)] Import),
}
