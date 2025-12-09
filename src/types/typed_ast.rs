use indexmap::IndexMap;

use crate::{
    label::Label,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::{
        inline_ir_instruction::InlineIRInstruction,
        pattern::{Pattern, PatternKind},
    },
    types::{conformance::Conformance, ty::SomeType, type_error::TypeError},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedPattern<T: SomeType> {
    pub id: NodeID,
    pub ty: T,
    pub kind: PatternKind,
}

#[derive(Debug, Clone)]
pub struct TypedAST<T: SomeType> {
    pub decls: Vec<TypedDecl<T>>,
    pub stmts: Vec<TypedStmt<T>>,
}

#[derive(Debug, Clone)]
pub enum TypedDeclKind<T: SomeType> {
    Err(TypeError),
    Let {
        pattern: TypedPattern<T>,
        ty: T,
    },
    StructDef {
        symbol: Symbol,
        properties: IndexMap<Label, T>,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        typealiases: IndexMap<Label, T>,
        conformances: Vec<Conformance<T>>,
    },
    Extend {
        symbol: Symbol,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        typealiases: IndexMap<Label, T>,
        conformances: Vec<Conformance<T>>,
    },
    EnumDef {
        symbol: Symbol,
        variants: IndexMap<Label, Vec<T>>,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        typealiases: IndexMap<Label, T>,
        conformances: Vec<Conformance<T>>,
    },
    ProtocolDef {
        symbol: Symbol,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        instance_method_requirements: IndexMap<Label, T>,
        typealiases: IndexMap<Label, T>,
        associated_types: IndexMap<Label, T>,
    },
}

#[derive(Debug, Clone)]
pub enum TypedNode<T: SomeType> {
    Decl(TypedDecl<T>),
    Expr(TypedExpr<T>),
    Stmt(TypedStmt<T>),
}

impl<T: SomeType> TypedNode<T> {
    pub fn ty(&self) -> T {
        if let Self::Expr(expr) = self {
            expr.ty.clone()
        } else if let Self::Stmt(TypedStmt {
            kind: TypedStmtKind::Expr(expr),
            ..
        }) = self
        {
            expr.ty.clone()
        } else {
            T::void()
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypedStmt<T: SomeType> {
    pub id: NodeID,
    pub kind: TypedStmtKind<T>,
}

#[derive(Debug, Clone)]
pub enum TypedStmtKind<T: SomeType> {
    Expr(TypedExpr<T>),
    Assignment(TypedExpr<T>, TypedExpr<T>),
    Return(Option<TypedExpr<T>>),
    Loop(TypedExpr<T>, TypedBlock<T>),
    Break,
}

#[derive(Debug, Clone)]
pub struct TypedDecl<T: SomeType> {
    pub id: NodeID,
    pub kind: TypedDeclKind<T>,
}

#[derive(Debug, Clone)]
pub struct TypedBlock<T: SomeType> {
    pub id: NodeID,
    pub body: Vec<TypedNode<T>>,
    pub ret: T,
}

#[derive(Debug, Clone)]
pub struct TypedParameter<T: SomeType> {
    pub name: Symbol,
    pub ty: T,
}

#[derive(Debug, Clone)]
pub struct TypedFunc<T: SomeType> {
    pub name: Symbol,
    pub params: Vec<TypedParameter<T>>,
    pub body: TypedBlock<T>,
    pub ret: T,
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm<T: SomeType> {
    pub pattern: TypedPattern<T>,
    pub body: TypedBlock<T>,
}

#[derive(Debug, Clone)]
pub struct TypedRecordField<T: SomeType> {
    pub name: Label,
    pub value: TypedExpr<T>,
}

#[derive(Debug, Clone)]
pub enum TypedExprKind<T: SomeType> {
    Hole,
    InlineIR(Box<InlineIRInstruction>),
    Let(Symbol, Box<TypedExpr<T>>),
    LiteralArray(Vec<TypedExpr<T>>),
    LiteralInt(String),
    LiteralFloat(String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(String),
    Tuple(Vec<TypedExpr<T>>),
    Block(TypedBlock<T>),
    Call {
        callee: Box<TypedExpr<T>>,
        type_args: Vec<T>,
        args: Vec<TypedExpr<T>>,
    },

    Loop(Box<Option<TypedExpr<T>>>, TypedBlock<T>),
    Break,
    Continue,

    // A dot thing
    Member(Box<TypedExpr<T>>, Label),

    // Function stuff
    Func(TypedFunc<T>),

    Variable(Symbol),

    Constructor(Symbol, Vec<T>),

    If(
        Box<TypedExpr<T>>, /* condition */
        TypedBlock<T>,     /* condition block */
        TypedBlock<T>,     /* else block */
    ),

    // Match expression
    Match(
        Box<TypedExpr<T>>,     // scrutinee: the value being matched
        Vec<TypedMatchArm<T>>, // arms: [MatchArm(pattern, body)]
    ),

    // Record literal: {x: 1, y: 2}
    RecordLiteral {
        fields: Vec<TypedRecordField<T>>,
    },
}

#[derive(Debug, Clone)]
pub struct TypedExpr<T: SomeType> {
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedExprKind<T>,
}
