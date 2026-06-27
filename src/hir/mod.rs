//! The HIR (high-level IR): an owned, desugared tree the surface AST lowers
//! into. Ownership checking and lowering consume the HIR instead of the parser
//! AST, so a single canonical IR (and, later, a single MIR build) serves both.
//!
//! Design notes (see the staged plan):
//! - **Owned, no lifetimes** — built once, freely shared/stored.
//! - **NodeID-preserving** — every node carries the same `NodeID` as the AST node
//!   it came from, so the type checker's NodeID-keyed tables still resolve.
//! - **Stripped** — surface-only and already-desugared forms are gone:
//!   `Unary`/`Binary` (→ protocol calls), `For` (→ loop+match), `Incomplete`
//!   (LSP-only), `Import` (resolved away), comments/trivia, and `*_span` fields
//!   (a single `span` is kept for diagnostics).
//!
//! This module currently defines the owned node types only. The `build_hir`
//! AST→HIR transform and the consumer re-pointing land in later stages.
#![allow(dead_code)]

pub mod build;

#[cfg(test)]
mod hir_tests;

use derive_visitor::{Drive, DriveMut};

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
        parameter::Parameter,
        type_annotation::TypeAnnotation,
        where_clause::WhereClause,
    },
    parsing::span::Span,
};
use crate::label::Label;

/// The umbrella node type for a block body (`Vec<Node>`), mirroring the AST's
/// heterogeneous `Node` but only the variants a block body actually holds.
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum Node {
    Decl(Decl),
    Stmt(Stmt),
    Expr(Expr),
}

// ----- Expressions ---------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct Expr {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: ExprKind,
    #[drive(skip)]
    pub span: Span,
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expr(id: {:?}, kind: {:?})", self.id, self.kind)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum ExprKind {
    InlineIR(InlineIRInstruction),
    As(Box<Expr>, #[drive(skip)] TypeAnnotation),
    CallEffect {
        #[drive(skip)]
        effect_name: Name,
        #[drive(skip)]
        type_args: Vec<TypeAnnotation>,
        args: Vec<CallArg>,
    },
    LiteralArray(Vec<Expr>),
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(#[drive(skip)] String),
    Tuple(Vec<Expr>),
    Block(Block),
    Call {
        callee: Box<Expr>,
        #[drive(skip)]
        type_args: Vec<TypeAnnotation>,
        args: Vec<CallArg>,
        trailing_block: Option<Block>,
    },
    Member(Option<Box<Expr>>, #[drive(skip)] Label),
    Func(Func),
    Variable(#[drive(skip)] Name),
    Constructor(#[drive(skip)] Name),
    If(Box<Expr>, Block, Block),
    Match(Box<Expr>, Vec<MatchArm>),
    RecordLiteral {
        fields: Vec<RecordField>,
        spread: Option<Box<Expr>>,
    },
    RowVariable(#[drive(skip)] Name),
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
            | PatternKind::LiteralTrue
            | PatternKind::LiteralFalse
            | PatternKind::Wildcard => {}
            PatternKind::Or(patterns) | PatternKind::Tuple(patterns) => {
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
    Continue(Option<Expr>),
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
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        conformances: Vec<TypeAnnotation>,
        generics: Vec<GenericDecl>,
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
        result: Option<TypeAnnotation>,
    },
    FuncSignature(#[drive(skip)] FuncSignature),
    MethodRequirement {
        #[drive(skip)]
        signature: FuncSignature,
        #[drive(skip)]
        receiver_mode: ReceiverMode,
    },
    TypeAlias(#[drive(skip)] Name, #[drive(skip)] TypeAnnotation),
    /// Imports are resolved away during name resolution; kept as an inert marker
    /// so a 1:1 lowering can carry the original node id, never traversed.
    Import(#[drive(skip)] Import),
}
