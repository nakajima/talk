use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;

use crate::{
    label::Label,
    name_resolution::{name_resolver::ResolvedNames, symbol::Symbol},
    node_id::NodeID,
    node_kinds::{inline_ir_instruction::TypedInlineIRInstruction, pattern::PatternKind},
    types::{
        infer_ty::InferTy,
        scheme::ForAll,
        ty::{SomeType, Ty},
        type_operations::UnificationSubstitutions,
        type_session::TypeSession,
    },
};

pub trait TyMappable<T: SomeType, U: SomeType> {
    type Output;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output;
}

#[derive(Debug, Clone)]
pub struct TypedAST<T: SomeType> {
    pub decls: Vec<TypedDecl<T>>,
    pub stmts: Vec<TypedStmt<T>>,
    pub phase: ResolvedNames,
}

impl TypedAST<Ty> {
    pub fn roots(&self) -> Vec<TypedNode<Ty>> {
        let mut result = vec![];
        result.extend(self.decls.iter().cloned().map(TypedNode::Decl));
        result.extend(self.stmts.iter().cloned().map(TypedNode::Stmt));
        result.sort_by(|a, b| a.node_id().1.cmp(&b.node_id().1));
        result
    }
}

impl TypedAST<InferTy> {
    pub fn apply(
        self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Self {
        self.map_ty(&mut |ty| session.apply(ty.clone(), substitutions))
    }

    /// Transforms types from InferTy to Ty and converts Member to ProtocolMember where we have witnesses
    pub fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedAST<Ty> {
        TypedAST::<Ty> {
            decls: self
                .decls
                .into_iter()
                .map(|d| d.finalize(session, witnesses))
                .collect(),
            stmts: self
                .stmts
                .into_iter()
                .map(|s| s.finalize(session, witnesses))
                .collect(),
            phase: self.phase,
        }
    }
}

impl TypedStmt<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedStmt<Ty> {
        TypedStmt {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.finalize(session, witnesses),
        }
    }
}

impl TypedStmtKind<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedStmtKind<Ty> {
        use TypedStmtKind::*;
        match self {
            Expr(typed_expr) => Expr(typed_expr.finalize(session, witnesses)),
            Assignment(lhs, rhs) => Assignment(
                lhs.finalize(session, witnesses),
                rhs.finalize(session, witnesses),
            ),
            Return(typed_expr) => Return(typed_expr.map(|e| e.finalize(session, witnesses))),
            Loop(cond, block) => Loop(
                cond.finalize(session, witnesses),
                block.finalize(session, witnesses),
            ),
            Break => Break,
        }
    }
}

impl TypedDecl<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedDecl<Ty> {
        TypedDecl {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.finalize(session, witnesses),
        }
    }
}

impl TypedBlock<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedBlock<Ty> {
        TypedBlock {
            id: self.id,
            body: self
                .body
                .into_iter()
                .map(|e| e.finalize(session, witnesses))
                .collect(),
            ret: session.finalize_ty(self.ret).as_mono_ty().clone(),
        }
    }
}

impl TypedFunc<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedFunc<Ty> {
        TypedFunc {
            name: self.name,
            foralls: self.foralls,
            params: self
                .params
                .into_iter()
                .map(|p| TypedParameter {
                    name: p.name,
                    ty: session.finalize_ty(p.ty).as_mono_ty().clone(),
                })
                .collect(),
            body: self.body.finalize(session, witnesses),
            ret: session.finalize_ty(self.ret).as_mono_ty().clone(),
        }
    }
}

impl TypedMatchArm<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedMatchArm<Ty> {
        TypedMatchArm {
            pattern: self.pattern.finalize(session),
            body: self.body.finalize(session, witnesses),
        }
    }
}

impl TypedPattern<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedPattern<Ty> {
        TypedPattern {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind,
        }
    }
}

impl TypedRecordField<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedRecordField<Ty> {
        TypedRecordField {
            name: self.name,
            value: self.value.finalize(session, witnesses),
        }
    }
}

impl TypedNode<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedNode<Ty> {
        match self {
            TypedNode::Decl(d) => TypedNode::Decl(d.finalize(session, witnesses)),
            TypedNode::Expr(e) => TypedNode::Expr(e.finalize(session, witnesses)),
            TypedNode::Stmt(s) => TypedNode::Stmt(s.finalize(session, witnesses)),
        }
    }
}

impl TypedDeclKind<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedDeclKind<Ty> {
        use TypedDeclKind::*;
        match self {
            Let {
                pattern,
                ty,
                initializer,
            } => Let {
                pattern: pattern.finalize(session),
                ty: session.finalize_ty(ty).as_mono_ty().clone(),
                initializer: initializer.map(|e| e.finalize(session, witnesses)),
            },
            StructDef {
                symbol,
                initializers,
                properties,
                instance_methods,
                typealiases,
            } => StructDef {
                symbol,
                initializers: initializers
                    .into_iter()
                    .map(|(k, v)| (k, v.finalize(session, witnesses)))
                    .collect(),
                properties: properties
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.finalize(session, witnesses)))
                    .collect(),
                typealiases: typealiases
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
            },
            Extend {
                symbol,
                instance_methods,
                typealiases,
            } => Extend {
                symbol,
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.finalize(session, witnesses)))
                    .collect(),
                typealiases: typealiases
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
            },
            EnumDef {
                symbol,
                variants,
                instance_methods,
                typealiases,
            } => EnumDef {
                symbol,
                variants: variants
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k,
                            v.into_iter()
                                .map(|t| session.finalize_ty(t).as_mono_ty().clone())
                                .collect(),
                        )
                    })
                    .collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.finalize(session, witnesses)))
                    .collect(),
                typealiases: typealiases
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
            },
            ProtocolDef {
                symbol,
                instance_methods,
                instance_method_requirements,
                typealiases,
                associated_types,
            } => ProtocolDef {
                symbol,
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.finalize(session, witnesses)))
                    .collect(),
                instance_method_requirements: instance_method_requirements
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
                typealiases: typealiases
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
                associated_types: associated_types
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
            },
        }
    }
}

impl TypedExpr<InferTy> {
    fn finalize(
        self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedExpr<Ty> {
        TypedExpr {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.finalize(self.id, session, witnesses),
        }
    }
}

impl TypedExprKind<InferTy> {
    fn finalize(
        self,
        node_id: NodeID,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedExprKind<Ty> {
        use TypedExprKind::*;
        match self {
            Hole => Hole,
            InlineIR(inline_ir) => InlineIR(
                inline_ir
                    .map_ty(&mut |t| session.finalize_ty(t.clone()).as_mono_ty().clone())
                    .into(),
            ),
            LiteralArray(exprs) => LiteralArray(
                exprs
                    .into_iter()
                    .map(|e| e.finalize(session, witnesses))
                    .collect(),
            ),
            LiteralInt(v) => LiteralInt(v),
            LiteralFloat(v) => LiteralFloat(v),
            LiteralTrue => LiteralTrue,
            LiteralFalse => LiteralFalse,
            LiteralString(v) => LiteralString(v),
            Tuple(exprs) => Tuple(
                exprs
                    .into_iter()
                    .map(|e| e.finalize(session, witnesses))
                    .collect(),
            ),
            Block(block) => Block(block.finalize(session, witnesses)),
            Call {
                callee,
                type_args,
                args,
            } => Call {
                callee: callee.finalize(session, witnesses).into(),
                type_args: type_args
                    .into_iter()
                    .map(|t| session.finalize_ty(t).as_mono_ty().clone())
                    .collect(),
                args: args
                    .into_iter()
                    .map(|e| e.finalize(session, witnesses))
                    .collect(),
            },
            Member { receiver, label } => {
                // Check if this member access has a recorded witness (protocol member)
                // if let Some(&witness) = witnesses.get(&node_id) {
                //     ProtocolMember {
                //         receiver: receiver.finalize(session, witnesses).into(),
                //         label,
                //         witness,
                //     }
                // } else {
                Member {
                    receiver: receiver.finalize(session, witnesses).into(),
                    label,
                }
                // }
            }
            // ProtocolMember {
            //     receiver,
            //     label,
            //     witness,
            // } => ProtocolMember {
            //     receiver: receiver.finalize(session, witnesses).into(),
            //     label,
            //     witness,
            // },
            Func(func) => Func(func.finalize(session, witnesses)),
            Variable(sym) => Variable(sym),
            Constructor(sym, items) => Constructor(
                sym,
                items
                    .into_iter()
                    .map(|t| session.finalize_ty(t).as_mono_ty().clone())
                    .collect(),
            ),
            If(cond, conseq, alt) => If(
                cond.finalize(session, witnesses).into(),
                conseq.finalize(session, witnesses),
                alt.finalize(session, witnesses),
            ),
            Match(scrutinee, arms) => Match(
                scrutinee.finalize(session, witnesses).into(),
                arms.into_iter()
                    .map(|a| a.finalize(session, witnesses))
                    .collect(),
            ),
            RecordLiteral { fields } => RecordLiteral {
                fields: fields
                    .into_iter()
                    .map(|f| f.finalize(session, witnesses))
                    .collect(),
            },
        }
    }
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedAST<T> {
    type Output = TypedAST<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedAST::<U> {
            decls: self.decls.into_iter().map(|d| d.map_ty(m)).collect(),
            stmts: self.stmts.into_iter().map(|d| d.map_ty(m)).collect(),
            phase: self.phase,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedPattern<T: SomeType> {
    pub id: NodeID,
    pub ty: T,
    pub kind: PatternKind,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedPattern<T> {
    type Output = TypedPattern<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedPattern::<U> {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedDeclKind<T: SomeType> {
    Let {
        pattern: TypedPattern<T>,
        ty: T,
        initializer: Option<TypedExpr<T>>,
    },
    StructDef {
        symbol: Symbol,
        initializers: IndexMap<Label, TypedFunc<T>>,
        properties: IndexMap<Label, T>,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        typealiases: IndexMap<Label, T>,
    },
    Extend {
        symbol: Symbol,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        typealiases: IndexMap<Label, T>,
    },
    EnumDef {
        symbol: Symbol,
        variants: IndexMap<Label, Vec<T>>,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        typealiases: IndexMap<Label, T>,
    },
    ProtocolDef {
        symbol: Symbol,
        instance_methods: IndexMap<Label, TypedFunc<T>>,
        instance_method_requirements: IndexMap<Label, T>,
        typealiases: IndexMap<Label, T>,
        associated_types: IndexMap<Label, T>,
    },
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedDeclKind<T> {
    type Output = TypedDeclKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        use TypedDeclKind::*;
        match self {
            Let {
                pattern,
                ty,
                initializer,
            } => Let {
                pattern: pattern.map_ty(m),
                ty: m(&ty),
                initializer: initializer.map(|e| e.map_ty(m)),
            },
            TypedDeclKind::StructDef {
                symbol,
                initializers,
                properties,
                instance_methods,
                typealiases,
            } => StructDef {
                symbol,
                initializers: initializers
                    .into_iter()
                    .map(|(k, v)| (k, v.map_ty(m)))
                    .collect(),
                properties: properties.into_iter().map(|(k, v)| (k, m(&v))).collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.map_ty(m)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(&v))).collect(),
            },
            TypedDeclKind::Extend {
                symbol,
                instance_methods,
                typealiases,
            } => Extend {
                symbol,
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.map_ty(m)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(&v))).collect(),
            },
            TypedDeclKind::EnumDef {
                symbol,
                variants,
                instance_methods,
                typealiases,
            } => EnumDef {
                symbol,
                variants: variants
                    .into_iter()
                    .map(|(k, v)| (k, v.iter().map(&mut *m).collect()))
                    .collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.map_ty(m)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(&v))).collect(),
            },
            TypedDeclKind::ProtocolDef {
                symbol,
                instance_methods,
                instance_method_requirements,
                typealiases,
                associated_types,
            } => ProtocolDef {
                symbol,
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.map_ty(m)))
                    .collect(),
                instance_method_requirements: instance_method_requirements
                    .into_iter()
                    .map(|(k, v)| (k, m(&v)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(&v))).collect(),
                associated_types: associated_types
                    .into_iter()
                    .map(|(k, v)| (k, m(&v)))
                    .collect(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedNode<T: SomeType> {
    Decl(TypedDecl<T>),
    Expr(TypedExpr<T>),
    Stmt(TypedStmt<T>),
}

impl<T: SomeType> TypedNode<T> {
    pub fn ty(&self) -> T {
        match self {
            TypedNode::Expr(e) => e.ty.clone(),
            TypedNode::Stmt(s) => s.ty.clone(),
            TypedNode::Decl(d) => d.ty.clone(),
        }
    }

    pub fn node_id(&self) -> NodeID {
        match self {
            TypedNode::Expr(n) => n.id,
            TypedNode::Stmt(n) => n.id,
            TypedNode::Decl(n) => n.id,
        }
    }
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedNode<T> {
    type Output = TypedNode<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        match self {
            TypedNode::Decl(typed_decl) => TypedNode::Decl(typed_decl.map_ty(m)),
            TypedNode::Expr(typed_expr) => TypedNode::Expr(typed_expr.map_ty(m)),
            TypedNode::Stmt(typed_stmt) => TypedNode::Stmt(typed_stmt.map_ty(m)),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedStmt<T: SomeType> {
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedStmtKind<T>,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedStmt<T> {
    type Output = TypedStmt<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedStmt {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedStmtKind<T: SomeType> {
    Expr(TypedExpr<T>),
    Assignment(TypedExpr<T>, TypedExpr<T>),
    Return(Option<TypedExpr<T>>),
    Loop(TypedExpr<T>, TypedBlock<T>),
    Break,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedStmtKind<T> {
    type Output = TypedStmtKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        use TypedStmtKind::*;
        match self {
            Expr(typed_expr) => Expr(typed_expr.map_ty(m)),
            Assignment(lhs, rhs) => Assignment(lhs.map_ty(m), rhs.map_ty(m)),
            Return(typed_expr) => Return(typed_expr.map(|e| e.map_ty(m))),
            Loop(cond, block) => Loop(cond.map_ty(m), block.map_ty(m)),
            Break => Break,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDecl<T: SomeType> {
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedDeclKind<T>,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedDecl<T> {
    type Output = TypedDecl<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedDecl {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedBlock<T: SomeType> {
    pub id: NodeID,
    pub body: Vec<TypedNode<T>>,
    pub ret: T,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedBlock<T> {
    type Output = TypedBlock<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedBlock {
            id: self.id,
            body: self.body.into_iter().map(|e| e.map_ty(m)).collect(),
            ret: m(&self.ret),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedParameter<T: SomeType> {
    pub name: Symbol,
    pub ty: T,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedFunc<T: SomeType> {
    pub name: Symbol,
    pub foralls: IndexSet<ForAll>,
    pub params: Vec<TypedParameter<T>>,
    pub body: TypedBlock<T>,
    pub ret: T,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedFunc<T> {
    type Output = TypedFunc<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedFunc {
            name: self.name,
            foralls: self.foralls,
            params: self
                .params
                .into_iter()
                .map(|p| TypedParameter {
                    name: p.name,
                    ty: m(&p.ty),
                })
                .collect(),
            body: self.body.map_ty(m),
            ret: m(&self.ret),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedMatchArm<T: SomeType> {
    pub pattern: TypedPattern<T>,
    pub body: TypedBlock<T>,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedMatchArm<T> {
    type Output = TypedMatchArm<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedMatchArm {
            pattern: self.pattern.map_ty(m),
            body: self.body.map_ty(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedRecordField<T: SomeType> {
    pub name: Label,
    pub value: TypedExpr<T>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedExprKind<T: SomeType> {
    Hole,
    InlineIR(Box<TypedInlineIRInstruction<T>>),
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
    // A member access on a concrete type (property, instance method, etc.)
    Member {
        receiver: Box<TypedExpr<T>>,
        label: Label,
    },
    // A protocol method call on a type parameter, with the method requirement as witness
    // ProtocolMember {
    //     receiver: Box<TypedExpr<T>>,
    //     label: Label,
    //     witness: Symbol,
    // },
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedExprKind<T> {
    type Output = TypedExprKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        use TypedExprKind::*;
        match self {
            Hole => Hole,
            InlineIR(inline_irinstruction) => InlineIR(inline_irinstruction.map_ty(m).into()),
            LiteralArray(typed_exprs) => {
                LiteralArray(typed_exprs.into_iter().map(|e| e.map_ty(m)).collect())
            }
            LiteralInt(v) => LiteralInt(v),
            LiteralFloat(v) => LiteralFloat(v),
            LiteralTrue => LiteralTrue,
            LiteralFalse => LiteralFalse,
            LiteralString(v) => LiteralString(v),
            Tuple(typed_exprs) => Tuple(typed_exprs.into_iter().map(|e| e.map_ty(m)).collect()),
            Block(typed_block) => Block(typed_block.map_ty(m)),
            Call {
                callee,
                type_args,
                args,
            } => Call {
                callee: callee.map_ty(m).into(),
                type_args: type_args.iter().map(&mut *m).collect(),
                args: args.into_iter().map(|e| e.map_ty(m)).collect(),
            },
            Member { receiver, label } => Member {
                receiver: receiver.map_ty(m).into(),
                label,
            },
            // ProtocolMember {
            //     receiver,
            //     label,
            //     witness,
            // } => ProtocolMember {
            //     receiver: receiver.map_ty(m).into(),
            //     label,
            //     witness,
            // },
            Func(typed_func) => Func(typed_func.map_ty(m)),
            Variable(symbol) => Variable(symbol),
            Constructor(symbol, items) => Constructor(symbol, items.iter().map(m).collect()),
            If(cond, conseq, alt) => If(cond.map_ty(m).into(), conseq.map_ty(m), alt.map_ty(m)),
            Match(typed_expr, typed_match_arms) => Match(
                typed_expr.map_ty(m).into(),
                typed_match_arms.into_iter().map(|e| e.map_ty(m)).collect(),
            ),
            RecordLiteral { fields } => RecordLiteral {
                fields: fields
                    .into_iter()
                    .map(|f| TypedRecordField {
                        name: f.name,
                        value: f.value.map_ty(m),
                    })
                    .collect(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr<T: SomeType> {
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedExprKind<T>,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedExpr<T> {
    type Output = TypedExpr<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::Output {
        TypedExpr {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
        }
    }
}
