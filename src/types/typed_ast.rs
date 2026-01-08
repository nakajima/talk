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
        conformance::ConformanceKey,
        constraints::call::CallId,
        infer_ty::InferTy,
        scheme::ForAll,
        ty::{SomeType, Ty},
        type_operations::{InstantiationSubstitutions, UnificationSubstitutions},
        type_session::TypeSession,
    },
};

pub trait TyMappable<T: SomeType, U: SomeType> {
    type OutputTy;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy;
}

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
        self.map_ty(&mut |ty| session.apply(ty.clone(), substitutions))
    }

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
            Handler { effect, func } => Handler {
                effect,
                func: func.finalize(session, witnesses),
            },
            Return(typed_expr) => Return(typed_expr.map(|e| e.finalize(session, witnesses))),
            Continue(typed_expr) => Continue(typed_expr.map(|e| e.finalize(session, witnesses))),
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
            kind: self
                .kind
                .map_ty(&mut |ty| session.finalize_ty(ty.clone()).as_mono_ty().clone()),
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
        mut self,
        session: &mut TypeSession,
        witnesses: &FxHashMap<NodeID, Symbol>,
    ) -> TypedExpr<Ty> {
        if let Some(instantiations) = session.instantiations_by_call.get(&CallId(self.id)) {
            self.instantiations.extend(instantiations.clone());
        }

        let ty = session.finalize_ty(self.ty).as_mono_ty().clone();
        let kind = self.kind.finalize(self.id, session, witnesses);
        let mut instantiations = InstantiationSubstitutions {
            row: self
                .instantiations
                .row
                .into_iter()
                .map(|(k, v)| (k, session.finalize_row(v)))
                .collect(),
            ty: self
                .instantiations
                .ty
                .into_iter()
                .map(|(k, v)| (k, session.finalize_ty(v).as_mono_ty().clone()))
                .collect(),
            witnesses: self.instantiations.witnesses.clone(),
        };
        instantiations
            .witnesses
            .extend(call_witness_substitutions(&kind));

        TypedExpr {
            id: self.id,
            ty,
            kind,
            instantiations, // .instantiations
                             // .map_ty(&mut |t| session.finalize_ty(t.clone()).as_mono_ty().clone()),
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
            CallEffect { effect, args } => CallEffect {
                effect,
                args: args
                    .into_iter()
                    .map(|a| a.finalize(session, witnesses))
                    .collect(),
            },
            Call {
                callee,
                type_args,
                args,
                resolved,
            } => {
                let callee = callee.finalize(session, witnesses);
                let type_args = type_args
                    .into_iter()
                    .map(|t| session.finalize_ty(t).as_mono_ty().clone())
                    .collect();
                let args: Vec<_> = args
                    .into_iter()
                    .map(|e| e.finalize(session, witnesses))
                    .collect();

                let resolved = resolved.or_else(|| {
                    try_resolve_protocol_constructor_default_call(&callee, &args, session)
                });

                Call {
                    callee: callee.into(),
                    type_args,
                    args,
                    resolved,
                }
            }
            Member { receiver, label } => {
                // Check if this member access has a recorded witness (protocol member)
                if let Some(&witness) = witnesses.get(&node_id) {
                    ProtocolMember {
                        receiver: receiver.finalize(session, witnesses).into(),
                        label,
                        witness,
                    }
                } else {
                    Member {
                        receiver: receiver.finalize(session, witnesses).into(),
                        label,
                    }
                }
            }
            ProtocolMember {
                receiver,
                label,
                witness,
            } => ProtocolMember {
                receiver: receiver.finalize(session, witnesses).into(),
                label,
                witness,
            },
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
    type OutputTy = TypedAST<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedAST::<U> {
            decls: self.decls.into_iter().map(|d| d.map_ty(m)).collect(),
            stmts: self.stmts.into_iter().map(|d| d.map_ty(m)).collect(),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedRecordFieldPattern<T> {
    type OutputTy = TypedRecordFieldPattern<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedRecordFieldPattern {
            id: self.id,
            kind: match self.kind {
                TypedRecordFieldPatternKind::Bind(sym) => TypedRecordFieldPatternKind::Bind(sym),
                TypedRecordFieldPatternKind::Equals { name, value } => {
                    TypedRecordFieldPatternKind::Equals {
                        name,
                        value: value.map_ty(m),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedPatternKind<T> {
    type OutputTy = TypedPatternKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        use TypedPatternKind::*;
        match self {
            LiteralInt(val) => LiteralInt(val),
            LiteralFloat(val) => LiteralFloat(val),
            LiteralTrue => LiteralTrue,
            LiteralFalse => LiteralFalse,
            Bind(symbol) => Bind(symbol),
            Tuple(typed_patterns) => {
                Tuple(typed_patterns.into_iter().map(|p| p.map_ty(m)).collect())
            }
            Or(typed_patterns) => Or(typed_patterns.into_iter().map(|p| p.map_ty(m)).collect()),
            Wildcard => Wildcard,
            Variant {
                enum_name,
                variant_name,
                fields,
            } => Variant {
                enum_name,
                variant_name,
                fields: fields.into_iter().map(|f| f.map_ty(m)).collect(),
            },
            Record { fields } => Record {
                fields: fields.into_iter().map(|f| f.map_ty(m)).collect(),
            },
            Struct {
                struct_name,
                fields,
                field_names,
                rest,
            } => Struct {
                struct_name,
                fields: fields.into_iter().map(|f| f.map_ty(m)).collect(),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedPattern<T> {
    type OutputTy = TypedPattern<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedPattern::<U> {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedDeclKind<T> {
    type OutputTy = TypedDeclKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedNode<T> {
    type OutputTy = TypedNode<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        match self {
            TypedNode::Decl(typed_decl) => TypedNode::Decl(typed_decl.map_ty(m)),
            TypedNode::Expr(typed_expr) => TypedNode::Expr(typed_expr.map_ty(m)),
            TypedNode::Stmt(typed_stmt) => TypedNode::Stmt(typed_stmt.map_ty(m)),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedStmt<T> {
    type OutputTy = TypedStmt<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedStmt {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedStmtKind<T> {
    type OutputTy = TypedStmtKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        use TypedStmtKind::*;
        match self {
            Handler { effect, func } => Handler {
                effect,
                func: func.map_ty(m),
            },
            Expr(typed_expr) => Expr(typed_expr.map_ty(m)),
            Assignment(lhs, rhs) => Assignment(lhs.map_ty(m), rhs.map_ty(m)),
            Return(typed_expr) => Return(typed_expr.map(|e| e.map_ty(m))),
            Loop(cond, block) => Loop(cond.map_ty(m), block.map_ty(m)),
            Continue(expr) => Continue(expr.map(|e| e.map_ty(m))),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedDecl<T> {
    type OutputTy = TypedDecl<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedDecl {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedBlock<T> {
    type OutputTy = TypedBlock<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedBlock {
            id: self.id,
            body: self.body.into_iter().map(|e| e.map_ty(m)).collect(),
            ret: m(&self.ret),
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

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedFunc<T> {
    type OutputTy = TypedFunc<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedFunc {
            name: self.name,
            foralls: self.foralls,
            params: map_into!(self.params, |p| TypedParameter {
                name: p.name,
                ty: m(&p.ty),
            }),
            effects: map_into!(self.effects, |e| TypedEffect {
                name: e.name,
                ty: m(&e.ty)
            }),
            effects_row: self.effects_row.map_ty(m),
            body: self.body.map_ty(m),
            ret: m(&self.ret),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedMatchArm<T: SomeType> {
    pub pattern: TypedPattern<T>,
    pub body: TypedBlock<T>,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedMatchArm<T> {
    type OutputTy = TypedMatchArm<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedMatchArm {
            pattern: self.pattern.map_ty(m),
            body: self.body.map_ty(m),
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
        type_args: Vec<T>,
        args: Vec<TypedExpr<T>>,
        #[drive(skip)]
        resolved: Option<ResolvedCallTarget>,
    },
    // A member access on a concrete type (property, instance method, etc.)
    Member {
        receiver: Box<TypedExpr<T>>,
        #[drive(skip)]
        label: Label,
    },
    ProtocolMember {
        receiver: Box<TypedExpr<T>>,
        #[drive(skip)]
        label: Label,
        #[drive(skip)]
        witness: Symbol,
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
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedExprKind<T> {
    type OutputTy = TypedExprKind<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        use TypedExprKind::*;
        match self {
            Hole => Hole,
            CallEffect { effect, args } => CallEffect {
                effect,
                args: args.into_iter().map(|a| a.map_ty(m)).collect(),
            },
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
                resolved,
            } => Call {
                callee: callee.map_ty(m).into(),
                type_args: type_args.iter().map(&mut *m).collect(),
                args: args.into_iter().map(|e| e.map_ty(m)).collect(),
                resolved,
            },
            Member { receiver, label } => Member {
                receiver: receiver.map_ty(m).into(),
                label,
            },
            ProtocolMember {
                receiver,
                label,
                witness,
            } => ProtocolMember {
                receiver: receiver.map_ty(m).into(),
                label,
                witness,
            },
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

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedExpr<T: SomeType> {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: T,
    pub kind: TypedExprKind<T>,
    #[drive(skip)]
    pub instantiations: InstantiationSubstitutions<T>,
}

impl<T: SomeType, U: SomeType> TyMappable<T, U> for TypedExpr<T> {
    type OutputTy = TypedExpr<U>;
    fn map_ty(self, m: &mut impl FnMut(&T) -> U) -> Self::OutputTy {
        TypedExpr {
            id: self.id,
            ty: m(&self.ty),
            kind: self.kind.map_ty(m),
            instantiations: self.instantiations.map_ty(m),
        }
    }
}

fn symbol_for_concrete_ty(ty: &Ty) -> Option<Symbol> {
    match ty {
        Ty::Primitive(sym) => Some(*sym),
        Ty::Nominal { symbol, .. } => Some(*symbol),
        _ => None,
    }
}

fn call_witness_substitutions(kind: &TypedExprKind<Ty>) -> FxHashMap<Symbol, Symbol> {
    let TypedExprKind::Call { resolved, .. } = kind else {
        return Default::default();
    };

    let mut witnesses = FxHashMap::default();
    if let Some(target) = resolved {
        witnesses.extend(target.witness_subs.clone());
    }

    witnesses
}

fn witness_subs_for_conformance(
    session: &mut TypeSession,
    protocol_sym: Symbol,
    conforming_sym: Symbol,
) -> FxHashMap<Symbol, Symbol> {
    let Symbol::Protocol(protocol_id) = protocol_sym else {
        return Default::default();
    };

    let key = ConformanceKey {
        protocol_id,
        conforming_id: conforming_sym,
    };
    session
        .lookup_conformance(&key)
        .map(|c| c.witnesses.requirements)
        .unwrap_or_default()
}

fn try_resolve_protocol_constructor_default_call(
    callee: &TypedExpr<Ty>,
    args: &[TypedExpr<Ty>],
    session: &mut TypeSession,
) -> Option<ResolvedCallTarget> {
    let TypedExprKind::Member { receiver, label } = &callee.kind else {
        return None;
    };
    let TypedExprKind::Constructor(protocol_sym @ Symbol::Protocol(_), _) = &receiver.kind else {
        return None;
    };

    let member_sym = session
        .type_catalog
        .lookup_member(protocol_sym, label)
        .map(|(sym, _src)| sym)
        .or_else(|| session.modules.lookup_member(protocol_sym, label))?;
    if !matches!(member_sym, Symbol::InstanceMethod(_)) {
        return None;
    }

    let self_arg = args.first()?;
    let conforming_sym = symbol_for_concrete_ty(&self_arg.ty)?;

    let witness_subs = witness_subs_for_conformance(session, *protocol_sym, conforming_sym);
    Some(ResolvedCallTarget {
        symbol: member_sym,
        witness_subs,
    })
}
