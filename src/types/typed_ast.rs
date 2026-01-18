use derive_visitor::{Drive, DriveMut};
use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;

use crate::{
    compiling::module::ModuleId,
    label::Label,
    map_into,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::inline_ir_instruction::TypedInlineIRInstruction,
    types::{
        infer_ty::InferTy,
        mappable::Mappable,
        scheme::ForAll,
        ty::{SomeType, Ty},
        type_operations::UnificationSubstitutions,
        type_session::TypeSession,
        variational::DimensionId,
    },
};

#[derive(Debug, Clone, Drive, DriveMut)]
pub struct TypedAST<T: SomeType> {
    pub decls: Vec<TypedDecl<T>>,
    pub stmts: Vec<TypedStmt<T>>,
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
        self.mapping(
            &mut |ty| session.apply(ty, substitutions),
            &mut |row| row, /* session.apply handles rows */
        )
    }

    pub fn finalize(self, session: &mut TypeSession) -> TypedAST<Ty> {
        TypedAST::<Ty> {
            decls: self
                .decls
                .into_iter()
                .map(|d| d.finalize(session))
                .collect(),
            stmts: self
                .stmts
                .into_iter()
                .map(|s| s.finalize(session))
                .collect(),
        }
    }
}

impl TypedStmt<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedStmt<Ty> {
        TypedStmt {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.finalize(session),
        }
    }
}

impl TypedStmtKind<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedStmtKind<Ty> {
        use TypedStmtKind::*;
        match self {
            Expr(typed_expr) => Expr(typed_expr.finalize(session)),
            Assignment(lhs, rhs) => Assignment(lhs.finalize(session), rhs.finalize(session)),
            Handler { effect, func } => Handler {
                effect,
                func: func.finalize(session),
            },
            Return(typed_expr) => Return(typed_expr.map(|e| e.finalize(session))),
            Continue(typed_expr) => Continue(typed_expr.map(|e| e.finalize(session))),
            Loop(cond, block) => Loop(cond.finalize(session), block.finalize(session)),
            Break => Break,
        }
    }
}

impl TypedDecl<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedDecl<Ty> {
        TypedDecl {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.finalize(session),
        }
    }
}

impl TypedBlock<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedBlock<Ty> {
        TypedBlock {
            id: self.id,
            body: self.body.into_iter().map(|e| e.finalize(session)).collect(),
            ret: session.finalize_ty(self.ret).as_mono_ty().clone(),
        }
    }
}

impl TypedFunc<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedFunc<Ty> {
        TypedFunc {
            name: self.name,
            foralls: self.foralls,
            params: map_into!(self.params, |p| TypedParameter {
                name: p.name,
                ty: session.finalize_ty(p.ty).as_mono_ty().clone(),
            }),
            effects: map_into!(self.effects, |e| {
                TypedEffect {
                    name: e.name,
                    ty: session.finalize_ty(e.ty).as_mono_ty().clone(),
                }
            }),
            effects_row: session.finalize_row(self.effects_row),
            body: self.body.finalize(session),
            ret: session.finalize_ty(self.ret).as_mono_ty().clone(),
        }
    }
}

impl TypedMatchArm<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedMatchArm<Ty> {
        TypedMatchArm {
            pattern: self.pattern.finalize(session),
            body: self.body.finalize(session),
        }
    }
}

impl TypedPattern<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedPattern<Ty> {
        TypedPattern {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.mapping(
                &mut |ty| session.finalize_ty(ty.clone()).as_mono_ty().clone(),
                &mut |row| row.into(),
            ),
        }
    }
}

impl TypedRecordField<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedRecordField<Ty> {
        TypedRecordField {
            name: self.name,
            value: self.value.finalize(session),
        }
    }
}

impl TypedNode<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedNode<Ty> {
        match self {
            TypedNode::Decl(d) => TypedNode::Decl(d.finalize(session)),
            TypedNode::Expr(e) => TypedNode::Expr(e.finalize(session)),
            TypedNode::Stmt(s) => TypedNode::Stmt(s.finalize(session)),
        }
    }
}

impl TypedDeclKind<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedDeclKind<Ty> {
        use TypedDeclKind::*;
        match self {
            Let {
                pattern,
                ty,
                initializer,
            } => Let {
                pattern: pattern.finalize(session),
                ty: session.finalize_ty(ty).as_mono_ty().clone(),
                initializer: initializer.map(|e| e.finalize(session)),
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
                    .map(|(k, v)| (k, v.finalize(session)))
                    .collect(),
                properties: properties
                    .into_iter()
                    .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                    .collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.finalize(session)))
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
                    .map(|(k, v)| (k, v.finalize(session)))
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
                    .map(|(k, v)| (k, v.finalize(session)))
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
                    .map(|(k, v)| (k, v.finalize(session)))
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
    fn finalize(self, session: &mut TypeSession) -> TypedExpr<Ty> {
        TypedExpr {
            id: self.id,
            ty: session.finalize_ty(self.ty).as_mono_ty().clone(),
            kind: self.kind.finalize(session),
        }
    }
}

impl TypedExprKind<InferTy> {
    fn finalize(self, session: &mut TypeSession) -> TypedExprKind<Ty> {
        use TypedExprKind::*;
        match self {
            Hole => Hole,
            InlineIR(inline_ir) => InlineIR(
                inline_ir
                    .mapping(
                        &mut |t| session.finalize_ty(t.clone()).as_mono_ty().clone(),
                        &mut |r| r.into(),
                    )
                    .into(),
            ),
            LiteralArray(exprs) => {
                LiteralArray(exprs.into_iter().map(|e| e.finalize(session)).collect())
            }
            LiteralInt(v) => LiteralInt(v),
            LiteralFloat(v) => LiteralFloat(v),
            LiteralTrue => LiteralTrue,
            LiteralFalse => LiteralFalse,
            LiteralString(v) => LiteralString(v),
            Tuple(exprs) => Tuple(exprs.into_iter().map(|e| e.finalize(session)).collect()),
            Block(block) => Block(block.finalize(session)),
            CallEffect { effect, args } => CallEffect {
                effect,
                args: args.into_iter().map(|a| a.finalize(session)).collect(),
            },
            Call {
                callee,
                callee_ty,
                type_args,
                args,
                callee_sym,
            } => {
                let callee = callee.finalize(session);
                let callee_ty = session.finalize_ty(callee_ty).as_mono_ty().clone();
                let type_args = type_args
                    .into_iter()
                    .map(|t| session.finalize_ty(t).as_mono_ty().clone())
                    .collect();
                let args: Vec<_> = args.into_iter().map(|e| e.finalize(session)).collect();
                Call {
                    callee: callee.into(),
                    callee_ty,
                    type_args,
                    args,
                    callee_sym,
                }
            }
            Member { receiver, label } => Member {
                receiver: receiver.finalize(session).into(),
                label,
            },
            Func(func) => Func(func.finalize(session)),
            Variable(sym) => Variable(sym),
            Constructor(sym, items) => Constructor(
                sym,
                items
                    .into_iter()
                    .map(|t| session.finalize_ty(t).as_mono_ty().clone())
                    .collect(),
            ),
            If(cond, conseq, alt) => If(
                cond.finalize(session).into(),
                conseq.finalize(session),
                alt.finalize(session),
            ),
            Match(scrutinee, arms) => Match(
                scrutinee.finalize(session).into(),
                arms.into_iter().map(|a| a.finalize(session)).collect(),
            ),
            RecordLiteral { fields } => RecordLiteral {
                fields: fields.into_iter().map(|f| f.finalize(session)).collect(),
            },
            Choice {
                dimension,
                alternatives,
            } => Choice {
                dimension,
                alternatives: alternatives.into_iter().map(|e| e.finalize(session)).collect(),
            },
        }
    }
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedAST<T> {
    type Output = TypedAST<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedAST::<U> {
            decls: self.decls.into_iter().map(|d| d.mapping(m, r)).collect(),
            stmts: self.stmts.into_iter().map(|d| d.mapping(m, r)).collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum TypedRecordFieldPatternKind<T: SomeType> {
    Bind(#[drive(skip)] Symbol),
    Equals {
        #[drive(skip)]
        name: Symbol,
        value: TypedPattern<T>,
    },
    Rest,
}
#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct TypedRecordFieldPattern<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: TypedRecordFieldPatternKind<T>,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedRecordFieldPattern<T> {
    type Output = TypedRecordFieldPattern<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedRecordFieldPattern {
            id: self.id,
            kind: match self.kind {
                TypedRecordFieldPatternKind::Bind(sym) => TypedRecordFieldPatternKind::Bind(sym),
                TypedRecordFieldPatternKind::Equals { name, value } => {
                    TypedRecordFieldPatternKind::Equals {
                        name,
                        value: value.mapping(m, r),
                    }
                }
                TypedRecordFieldPatternKind::Rest => TypedRecordFieldPatternKind::Rest,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum TypedPatternKind<T: SomeType> {
    // Literals that must match exactly
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    Bind(#[drive(skip)] Symbol),

    Tuple(Vec<TypedPattern<T>>),

    Or(Vec<TypedPattern<T>>),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        #[drive(skip)]
        enum_name: Option<Symbol>, // None for .some, Some for Option.some
        #[drive(skip)]
        variant_name: String,
        fields: Vec<TypedPattern<T>>, // Recursive patterns for fields
    },

    Record {
        fields: Vec<TypedRecordFieldPattern<T>>,
    },

    // Struct/Record destructuring
    Struct {
        #[drive(skip)]
        struct_name: Symbol, // The struct type name
        fields: Vec<TypedPattern<T>>, // Field patterns (we'll store field names separately)
        #[drive(skip)]
        field_names: Vec<Symbol>, // Field names corresponding to patterns
        #[drive(skip)]
        rest: bool, // Whether there's a .. pattern to ignore remaining fields
    },
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedPatternKind<T> {
    type Output = TypedPatternKind<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        use TypedPatternKind::*;
        match self {
            LiteralInt(val) => LiteralInt(val),
            LiteralFloat(val) => LiteralFloat(val),
            LiteralTrue => LiteralTrue,
            LiteralFalse => LiteralFalse,
            Bind(symbol) => Bind(symbol),
            Tuple(typed_patterns) => Tuple(
                typed_patterns
                    .into_iter()
                    .map(|p| p.mapping(m, r))
                    .collect(),
            ),
            Or(typed_patterns) => Or(typed_patterns
                .into_iter()
                .map(|p| p.mapping(m, r))
                .collect()),
            Wildcard => Wildcard,
            Variant {
                enum_name,
                variant_name,
                fields,
            } => Variant {
                enum_name,
                variant_name,
                fields: fields.into_iter().map(|f| f.mapping(m, r)).collect(),
            },
            Record { fields } => Record {
                fields: fields.into_iter().map(|f| f.mapping(m, r)).collect(),
            },
            Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => Struct {
                struct_name,
                fields: fields.into_iter().map(|f| f.mapping(m, r)).collect(),
                field_names,
                rest,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct TypedPattern<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedPatternKind<T>,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedPattern<T> {
    type Output = TypedPattern<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedPattern::<U> {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
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

impl<T: SomeType> Drive for TypedDeclKind<T> {
    fn drive<V: derive_visitor::Visitor>(&self, visitor: &mut V) {
        match self {
            TypedDeclKind::Let {
                pattern,
                ty,
                initializer,
            } => {
                pattern.drive(visitor);
                ty.drive(visitor);
                initializer.drive(visitor);
            }
            TypedDeclKind::StructDef {
                initializers,
                properties,
                instance_methods,
                typealiases,
                ..
            } => {
                for val in initializers.values() {
                    val.drive(visitor);
                }
                for val in properties.values() {
                    val.drive(visitor);
                }
                for val in instance_methods.values() {
                    val.drive(visitor);
                }
                for val in typealiases.values() {
                    val.drive(visitor);
                }
            }
            TypedDeclKind::Extend {
                instance_methods,
                typealiases,
                ..
            } => {
                for val in instance_methods.values() {
                    val.drive(visitor);
                }
                for val in typealiases.values() {
                    val.drive(visitor);
                }
            }
            TypedDeclKind::EnumDef {
                variants,
                instance_methods,
                typealiases,
                ..
            } => {
                for val in variants.values() {
                    val.drive(visitor);
                }
                for val in instance_methods.values() {
                    val.drive(visitor);
                }
                for val in typealiases.values() {
                    val.drive(visitor);
                }
            }
            TypedDeclKind::ProtocolDef {
                instance_methods,
                instance_method_requirements,
                typealiases,
                associated_types,
                ..
            } => {
                for val in associated_types.values() {
                    val.drive(visitor);
                }
                for val in instance_method_requirements.values() {
                    val.drive(visitor);
                }
                for val in instance_methods.values() {
                    val.drive(visitor);
                }
                for val in typealiases.values() {
                    val.drive(visitor);
                }
            }
        }
    }
}

impl<T: SomeType> DriveMut for TypedDeclKind<T> {
    fn drive_mut<V: derive_visitor::VisitorMut>(&mut self, visitor: &mut V) {
        match self {
            TypedDeclKind::Let {
                pattern,
                ty,
                initializer,
            } => {
                pattern.drive_mut(visitor);
                ty.drive_mut(visitor);
                initializer.drive_mut(visitor);
            }
            TypedDeclKind::StructDef {
                initializers,
                properties,
                instance_methods,
                typealiases,
                ..
            } => {
                for val in initializers.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in properties.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in instance_methods.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in typealiases.values_mut() {
                    val.drive_mut(visitor);
                }
            }
            TypedDeclKind::Extend {
                instance_methods,
                typealiases,
                ..
            } => {
                for val in instance_methods.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in typealiases.values_mut() {
                    val.drive_mut(visitor);
                }
            }
            TypedDeclKind::EnumDef {
                variants,
                instance_methods,
                typealiases,
                ..
            } => {
                for val in variants.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in instance_methods.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in typealiases.values_mut() {
                    val.drive_mut(visitor);
                }
            }
            TypedDeclKind::ProtocolDef {
                instance_methods,
                instance_method_requirements,
                typealiases,
                associated_types,
                ..
            } => {
                for val in associated_types.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in instance_method_requirements.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in instance_methods.values_mut() {
                    val.drive_mut(visitor);
                }
                for val in typealiases.values_mut() {
                    val.drive_mut(visitor);
                }
            }
        }
    }
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedDeclKind<T> {
    type Output = TypedDeclKind<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        use TypedDeclKind::*;
        match self {
            Let {
                pattern,
                ty,
                initializer,
            } => Let {
                pattern: pattern.mapping(m, r),
                ty: m(ty),
                initializer: initializer.map(|e| e.mapping(m, r)),
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
                    .map(|(k, v)| (k, v.mapping(m, r)))
                    .collect(),
                properties: properties.into_iter().map(|(k, v)| (k, m(v))).collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.mapping(m, r)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(v))).collect(),
            },
            TypedDeclKind::Extend {
                symbol,
                instance_methods,
                typealiases,
            } => Extend {
                symbol,
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.mapping(m, r)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(v))).collect(),
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
                    .map(|(k, v)| (k, v.into_iter().map(&mut *m).collect()))
                    .collect(),
                instance_methods: instance_methods
                    .into_iter()
                    .map(|(k, v)| (k, v.mapping(m, r)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(v))).collect(),
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
                    .map(|(k, v)| (k, v.mapping(m, r)))
                    .collect(),
                instance_method_requirements: instance_method_requirements
                    .into_iter()
                    .map(|(k, v)| (k, m(v)))
                    .collect(),
                typealiases: typealiases.into_iter().map(|(k, v)| (k, m(v))).collect(),
                associated_types: associated_types
                    .into_iter()
                    .map(|(k, v)| (k, m(v)))
                    .collect(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
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

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedNode<T> {
    type Output = TypedNode<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        match self {
            TypedNode::Decl(typed_decl) => TypedNode::Decl(typed_decl.mapping(m, r)),
            TypedNode::Expr(typed_expr) => TypedNode::Expr(typed_expr.mapping(m, r)),
            TypedNode::Stmt(typed_stmt) => TypedNode::Stmt(typed_stmt.mapping(m, r)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedStmt<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedStmtKind<T>,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedStmt<T> {
    type Output = TypedStmt<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedStmt {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub enum TypedStmtKind<T: SomeType> {
    Expr(TypedExpr<T>),
    Assignment(TypedExpr<T>, TypedExpr<T>),
    Return(Option<TypedExpr<T>>),
    Continue(Option<TypedExpr<T>>),
    Loop(TypedExpr<T>, TypedBlock<T>),
    Handler {
        #[drive(skip)]
        effect: Symbol,
        func: TypedFunc<T>,
    },
    Break,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedStmtKind<T> {
    type Output = TypedStmtKind<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        use TypedStmtKind::*;
        match self {
            Handler { effect, func } => Handler {
                effect,
                func: func.mapping(m, r),
            },
            Expr(typed_expr) => Expr(typed_expr.mapping(m, r)),
            Assignment(lhs, rhs) => Assignment(lhs.mapping(m, r), rhs.mapping(m, r)),
            Return(typed_expr) => Return(typed_expr.map(|e| e.mapping(m, r))),
            Loop(cond, block) => Loop(cond.mapping(m, r), block.mapping(m, r)),
            Continue(expr) => Continue(expr.map(|e| e.mapping(m, r))),
            Break => Break,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedDecl<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedDeclKind<T>,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedDecl<T> {
    type Output = TypedDecl<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedDecl {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedBlock<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub body: Vec<TypedNode<T>>,
    pub ret: T,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedBlock<T> {
    type Output = TypedBlock<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedBlock {
            id: self.id,
            body: self.body.into_iter().map(|e| e.mapping(m, r)).collect(),
            ret: m(self.ret),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedParameter<T: SomeType> {
    #[drive(skip)]
    pub name: Symbol,
    pub ty: T,
}

impl From<TypedParameter<InferTy>> for TypedParameter<Ty> {
    fn from(value: TypedParameter<InferTy>) -> Self {
        TypedParameter {
            name: value.name,
            ty: value.ty.into(),
        }
    }
}

impl From<TypedParameter<Ty>> for TypedParameter<InferTy> {
    fn from(value: TypedParameter<Ty>) -> Self {
        TypedParameter {
            name: value.name,
            ty: value.ty.into(),
        }
    }
}

impl<T: SomeType> TypedParameter<T> {
    pub fn import(self, module_id: ModuleId) -> Self {
        TypedParameter {
            name: self.name.import(module_id),
            ty: self.ty.import(module_id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedEffect<T: SomeType> {
    #[drive(skip)]
    pub name: Symbol,
    pub ty: T,
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedFunc<T: SomeType> {
    #[drive(skip)]
    pub name: Symbol,
    #[drive(skip)]
    pub foralls: IndexSet<ForAll>,
    pub params: Vec<TypedParameter<T>>,
    pub effects: Vec<TypedEffect<T>>,
    pub effects_row: T::RowType,
    pub body: TypedBlock<T>,
    pub ret: T,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedFunc<T> {
    type Output = TypedFunc<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedFunc {
            name: self.name,
            foralls: self.foralls,
            params: map_into!(self.params, |p| TypedParameter {
                name: p.name,
                ty: m(p.ty),
            }),
            effects: map_into!(self.effects, |e| TypedEffect {
                name: e.name,
                ty: m(e.ty)
            }),
            effects_row: r(self.effects_row),
            body: self.body.mapping(m, r),
            ret: m(self.ret),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedMatchArm<T: SomeType> {
    pub pattern: TypedPattern<T>,
    pub body: TypedBlock<T>,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedMatchArm<T> {
    type Output = TypedMatchArm<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedMatchArm {
            pattern: self.pattern.mapping(m, r),
            body: self.body.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedRecordField<T: SomeType> {
    #[drive(skip)]
    pub name: Label,
    pub value: TypedExpr<T>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedCallTarget {
    pub symbol: Symbol,
    /// Maps `@MethodRequirement` symbols to their concrete implementations for this call site.
    pub witness_subs: FxHashMap<Symbol, Symbol>,
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub enum TypedExprKind<T: SomeType> {
    Hole,
    InlineIR(#[drive(skip)] Box<TypedInlineIRInstruction<T>>),
    LiteralArray(Vec<TypedExpr<T>>),
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(#[drive(skip)] String),
    Tuple(Vec<TypedExpr<T>>),
    Block(TypedBlock<T>),
    CallEffect {
        #[drive(skip)]
        effect: Symbol,
        args: Vec<TypedExpr<T>>,
    },
    Call {
        callee: Box<TypedExpr<T>>,
        callee_ty: T,
        type_args: Vec<T>,
        args: Vec<TypedExpr<T>>,
        #[drive(skip)]
        callee_sym: Option<Symbol>,
    },
    // A member access on a concrete type (property, instance method, etc.)
    Member {
        receiver: Box<TypedExpr<T>>,
        #[drive(skip)]
        label: Label,
    },
    // Function stuff
    Func(TypedFunc<T>),
    Variable(#[drive(skip)] Symbol),
    Constructor(#[drive(skip)] Symbol, Vec<T>),

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

    /// Variational choice: alternatives for overloaded calls.
    /// During constraint solving, we create Choice nodes when we can't
    /// immediately determine which implementation to use. After resolution,
    /// these are specialized to the selected alternative.
    Choice {
        #[drive(skip)]
        dimension: DimensionId,
        alternatives: Vec<TypedExpr<T>>,
    },
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedExprKind<T> {
    type Output = TypedExprKind<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        use TypedExprKind::*;
        match self {
            Hole => Hole,
            CallEffect { effect, args } => CallEffect {
                effect,
                args: args.into_iter().map(|a| a.mapping(m, r)).collect(),
            },
            InlineIR(inline_irinstruction) => InlineIR(inline_irinstruction.mapping(m, r).into()),
            LiteralArray(typed_exprs) => {
                LiteralArray(typed_exprs.into_iter().map(|e| e.mapping(m, r)).collect())
            }
            LiteralInt(v) => LiteralInt(v),
            LiteralFloat(v) => LiteralFloat(v),
            LiteralTrue => LiteralTrue,
            LiteralFalse => LiteralFalse,
            LiteralString(v) => LiteralString(v),
            Tuple(typed_exprs) => Tuple(typed_exprs.into_iter().map(|e| e.mapping(m, r)).collect()),
            Block(typed_block) => Block(typed_block.mapping(m, r)),
            Call {
                callee,
                callee_ty,
                type_args,
                args,
                callee_sym,
            } => Call {
                callee: callee.mapping(m, r).into(),
                callee_ty: m(callee_ty),
                type_args: type_args.into_iter().map(&mut *m).collect(),
                args: args.into_iter().map(|e| e.mapping(m, r)).collect(),
                callee_sym,
            },
            Member { receiver, label } => Member {
                receiver: receiver.mapping(m, r).into(),
                label,
            },
            Func(typed_func) => Func(typed_func.mapping(m, r)),
            Variable(symbol) => Variable(symbol),
            Constructor(symbol, items) => Constructor(symbol, items.into_iter().map(m).collect()),
            If(cond, conseq, alt) => If(
                cond.mapping(m, r).into(),
                conseq.mapping(m, r),
                alt.mapping(m, r),
            ),
            Match(typed_expr, typed_match_arms) => Match(
                typed_expr.mapping(m, r).into(),
                typed_match_arms
                    .into_iter()
                    .map(|e| e.mapping(m, r))
                    .collect(),
            ),
            RecordLiteral { fields } => RecordLiteral {
                fields: fields
                    .into_iter()
                    .map(|f| TypedRecordField {
                        name: f.name,
                        value: f.value.mapping(m, r),
                    })
                    .collect(),
            },
            Choice {
                dimension,
                alternatives,
            } => Choice {
                dimension,
                alternatives: alternatives.into_iter().map(|e| e.mapping(m, r)).collect(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedExpr<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedExprKind<T>,
}

impl<T: SomeType, U: SomeType> Mappable<T, U> for TypedExpr<T> {
    type Output = TypedExpr<U>;
    fn mapping(
        self,
        m: &mut impl FnMut(T) -> U,
        r: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output {
        TypedExpr {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}
