use derive_visitor::{Drive, DriveMut};

use crate::{node_id::NodeID, node_kinds::type_annotation::TypeAnnotation, parsing::span::Span};

/// One generic argument (ADR 0035): a type, or a static value expression.
/// The parser distinguishes them syntactically where it can (literals,
/// arithmetic); a bare name parses as `Type` and the checker reinterprets
/// it against the declared parameter's kind.
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum GenericArg {
    Type(TypeAnnotation),
    Static(StaticExpr),
}

impl GenericArg {
    pub fn id(&self) -> NodeID {
        match self {
            GenericArg::Type(annotation) => annotation.id,
            GenericArg::Static(expr) => expr.id,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            GenericArg::Type(annotation) => annotation.span,
            GenericArg::Static(expr) => expr.span,
        }
    }

    /// The annotation when this argument is (or wraps) a plain type.
    pub fn as_type(&self) -> Option<&TypeAnnotation> {
        match self {
            GenericArg::Type(annotation) => Some(annotation),
            GenericArg::Static(_) => None,
        }
    }

    /// Every name-like annotation inside this argument: a type argument
    /// is one; a static expression contributes each `Path` operand —
    /// both sides of arithmetic — so hover/goto reach every name.
    pub fn annotations(&self) -> Vec<&TypeAnnotation> {
        match self {
            GenericArg::Type(annotation) => vec![annotation],
            GenericArg::Static(expr) => {
                let mut paths = vec![];
                expr.path_annotations(&mut paths);
                paths
            }
        }
    }
}

/// A static value expression (ADR 0035 §3): the restricted index language.
/// Deliberately NOT the ordinary expression AST — the index language is a
/// separate, total fragment.
#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct StaticExpr {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: StaticExprKind,
    #[drive(skip)]
    pub span: Span,
}

impl StaticExpr {
    /// Collect the `Path` operands under this expression in source order.
    fn path_annotations<'e>(&'e self, out: &mut Vec<&'e TypeAnnotation>) {
        match &self.kind {
            StaticExprKind::Path(annotation) => out.push(annotation),
            StaticExprKind::Group(inner) => inner.path_annotations(out),
            StaticExprKind::Op { lhs, rhs, .. } => {
                lhs.path_annotations(out);
                rhs.path_annotations(out);
            }
            StaticExprKind::Int(_) | StaticExprKind::Bool(_) => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum StaticExprKind {
    /// An integer literal, e.g. the `4` in `[Int; 4]`.
    Int(#[drive(skip)] String),
    Bool(#[drive(skip)] bool),
    /// A name-like operand — a static parameter reference or a fieldless
    /// enum case path. Kept as an annotation so name resolution visits it
    /// like every other type reference.
    Path(TypeAnnotation),
    /// Parenthesized grouping.
    Group(Box<StaticExpr>),
    /// `+`, `-`, or multiplication by a literal (the checker enforces the
    /// literal-operand rule).
    Op {
        #[drive(skip)]
        op: StaticOpKind,
        lhs: Box<StaticExpr>,
        rhs: Box<StaticExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StaticOpKind {
    Add,
    Sub,
    Mul,
}

impl StaticOpKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
        }
    }
}
