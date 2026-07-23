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

#[cfg(test)]
mod typed_ast_tests;

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
        inline_ir_instruction::InlineIRInstructionKind,
        type_annotation::TypeAnnotation,
        type_application::TypeApplication,
        where_clause::WhereClause,
    },
    parsing::span::Span,
};

/// One source file in the typed compiler tree: the analogue of
/// `AST<NameResolved>` for downstream phases. Carries the same `file_id` and the
/// lowered roots.
#[derive(Clone, Debug)]
pub struct TypedFile {
    pub file_id: crate::node_id::FileID,
    pub roots: Vec<Node>,
}

/// The umbrella node type for a block body (`Vec<Node>`), mirroring the AST's
/// heterogeneous `Node` but only the variants a block body actually holds.
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum Node {
    Decl(Decl),
    Stmt(Stmt),
    Expr(Expr),
}

// ----- Expressions ---------------------------------------------------------

/// Per-expression clone facts selected by type checking.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExprOwnership {
    /// This expression contains an explicit clone coercion.
    pub auto_clone: bool,
}

#[derive(Clone, PartialEq, Eq, Drive, DriveMut)]
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
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expr(id: {:?}, kind: {:?})", self.id, self.kind)
    }
}

/// A literal constant — one atom form instead of five expression forms.
/// Numeric text stays as written (the checker typed it; lowering parses it).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Int(String),
    Float(String),
    Bool(bool),
    String(String),
    Character(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum ExprKind {
    InlineIR(InlineIRInstruction),
    CallEffect {
        #[drive(skip)]
        effect_name: Name,
        #[drive(skip)]
        type_args: Vec<crate::node_kinds::generic_arg::GenericArg>,
        args: Vec<CallArg>,
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
    /// Lowered form of the real Copy/CheapClone `clone()` method.
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

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct InlineIRInstruction {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub span: Span,
    pub binds: Vec<Expr>,
    #[drive(skip)]
    pub kind: InlineIRInstructionKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
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

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct RecordField {
    #[drive(skip)]
    pub id: NodeID,
    #[drive(skip)]
    pub label: Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct MatchArm {
    #[drive(skip)]
    pub id: NodeID,
    pub pattern: Pattern,
    pub body: Block,
}

// ----- Patterns ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct Pattern {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: PatternKind,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum PatternKind {
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralCharacter(#[drive(skip)] String),
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
        fields: Vec<Pattern>,
    },
    Record {
        fields: Vec<RecordFieldPattern>,
    },
    Struct {
        #[drive(skip)]
        struct_name: Option<Name>,
        fields: Vec<Pattern>,
        #[drive(skip)]
        field_names: Vec<Name>,
        #[drive(skip)]
        rest: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct RecordFieldPattern {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: RecordFieldPatternKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
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
            PatternKind::Record { fields } => {
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
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
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

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Block {
    #[drive(skip)]
    pub id: NodeID,
    pub args: Vec<Parameter>,
    pub body: Vec<Node>,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct Stmt {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: StmtKind,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
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
    },
}

// ----- Functions and declarations -----------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
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

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Body {
    #[drive(skip)]
    pub id: NodeID,
    pub decls: Vec<Decl>,
    #[drive(skip)]
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct Decl {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: DeclKind,
    #[drive(skip)]
    pub span: Span,
    #[drive(skip)]
    pub visibility: Visibility,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
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
