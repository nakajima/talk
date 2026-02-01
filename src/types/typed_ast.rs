use derive_visitor::{Drive, DriveMut};
use indexmap::{IndexMap, IndexSet};

use crate::{
    compiling::module::ModuleId,
    label::Label,
    map_into,
    name_resolution::symbol::Symbol,
    node_id::NodeID,
    node_kinds::inline_ir_instruction::TypedInlineIRInstruction,
    types::{
        infer_row::Row, infer_ty::Ty, scheme::ForAll, type_operations::UnificationSubstitutions,
        type_session::TypeSession, variational::DimensionId,
    },
};

#[derive(Debug, Clone, Drive, DriveMut)]
pub struct TypedAST {
    pub decls: Vec<TypedDecl>,
    pub stmts: Vec<TypedStmt>,
}

impl TypedAST {
    pub fn roots(&self) -> Vec<TypedNode> {
        let mut result = vec![];
        result.extend(self.decls.iter().cloned().map(TypedNode::Decl));
        result.extend(self.stmts.iter().cloned().map(TypedNode::Stmt));
        result.sort_by(|a, b| a.node_id().1.cmp(&b.node_id().1));
        result
    }

    pub fn apply(
        self,
        substitutions: &mut UnificationSubstitutions,
        session: &mut TypeSession,
    ) -> Self {
        // We need to apply substitutions and then generalize types.
        // shallow_generalize handles nested rows, so we only need to handle types.
        // For the row closure, we just return the row as-is since shallow_generalize
        // on types will handle any nested rows.
        self.mapping(
            &mut |ty| {
                let applied = session.apply(&ty, substitutions);
                session.shallow_generalize(applied)
            },
            &mut |row| row,
        )
    }

    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedAST {
            decls: self.decls.into_iter().map(|d| d.mapping(m, r)).collect(),
            stmts: self.stmts.into_iter().map(|d| d.mapping(m, r)).collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub enum TypedRecordFieldPatternKind {
    Bind(#[drive(skip)] Symbol),
    Equals {
        #[drive(skip)]
        name: Symbol,
        value: TypedPattern,
    },
    Rest,
}

#[derive(Clone, Debug, PartialEq, Eq, Drive, DriveMut)]
pub struct TypedRecordFieldPattern {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: TypedRecordFieldPatternKind,
}

impl TypedRecordFieldPattern {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
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
pub enum TypedPatternKind {
    // Literals that must match exactly
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,

    // Variable binding (always succeeds, binds value)
    Bind(#[drive(skip)] Symbol),

    Tuple(Vec<TypedPattern>),

    Or(Vec<TypedPattern>),

    // Wildcard (always succeeds, ignores value)
    Wildcard,

    // Enum variant destructuring
    Variant {
        #[drive(skip)]
        enum_name: Option<Symbol>, // None for .some, Some for Option.some
        #[drive(skip)]
        variant_name: String,
        #[drive(skip)]
        variant_name_span: crate::span::Span,
        fields: Vec<TypedPattern>, // Recursive patterns for fields
    },

    Record {
        fields: Vec<TypedRecordFieldPattern>,
    },

    // Struct/Record destructuring
    Struct {
        #[drive(skip)]
        struct_name: Symbol, // The struct type name
        fields: Vec<TypedPattern>, // Field patterns (we'll store field names separately)
        #[drive(skip)]
        field_names: Vec<Symbol>, // Field names corresponding to patterns
        #[drive(skip)]
        rest: bool, // Whether there's a .. pattern to ignore remaining fields
    },
}

impl TypedPatternKind {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
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
                variant_name_span,
                fields,
            } => Variant {
                enum_name,
                variant_name,
                variant_name_span,
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
pub struct TypedPattern {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: Ty,
    pub kind: TypedPatternKind,
}

impl TypedPattern {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedPattern {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedDeclKind {
    Let {
        pattern: TypedPattern,
        ty: Ty,
        initializer: Option<TypedExpr>,
    },
    StructDef {
        symbol: Symbol,
        initializers: IndexMap<Label, TypedFunc>,
        properties: IndexMap<Label, Ty>,
        instance_methods: IndexMap<Label, TypedFunc>,
        typealiases: IndexMap<Label, Ty>,
    },
    Extend {
        symbol: Symbol,
        instance_methods: IndexMap<Label, TypedFunc>,
        typealiases: IndexMap<Label, Ty>,
    },
    EnumDef {
        symbol: Symbol,
        variants: IndexMap<Label, Vec<Ty>>,
        instance_methods: IndexMap<Label, TypedFunc>,
        typealiases: IndexMap<Label, Ty>,
    },
    ProtocolDef {
        symbol: Symbol,
        instance_methods: IndexMap<Label, TypedFunc>,
        instance_method_requirements: IndexMap<Label, Ty>,
        typealiases: IndexMap<Label, Ty>,
        associated_types: IndexMap<Label, Ty>,
    },
    /// Import declarations - no type info, just bring symbols into scope
    Import,
}

impl Drive for TypedDeclKind {
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
            TypedDeclKind::Import => {}
        }
    }
}

impl DriveMut for TypedDeclKind {
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
            TypedDeclKind::Import => {}
        }
    }
}

impl TypedDeclKind {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
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
            Import => Import,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub enum TypedNode {
    Decl(TypedDecl),
    Expr(TypedExpr),
    Stmt(TypedStmt),
}

impl TypedNode {
    pub fn ty(&self) -> Ty {
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

    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        match self {
            TypedNode::Decl(typed_decl) => TypedNode::Decl(typed_decl.mapping(m, r)),
            TypedNode::Expr(typed_expr) => TypedNode::Expr(typed_expr.mapping(m, r)),
            TypedNode::Stmt(typed_stmt) => TypedNode::Stmt(typed_stmt.mapping(m, r)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedStmt {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: Ty,
    pub kind: TypedStmtKind,
}

impl TypedStmt {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedStmt {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub enum TypedStmtKind {
    Expr(TypedExpr),
    Assignment(TypedExpr, TypedExpr),
    Return(Option<TypedExpr>),
    Continue(Option<TypedExpr>),
    Loop(TypedExpr, TypedBlock),
    Handler {
        #[drive(skip)]
        effect: Symbol,
        func: TypedFunc,
    },
    Break,
}

impl TypedStmtKind {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
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
pub struct TypedDecl {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: Ty,
    pub kind: TypedDeclKind,
}

impl TypedDecl {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedDecl {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedBlock {
    #[drive(skip)]
    pub id: NodeID,
    pub body: Vec<TypedNode>,
    pub ret: Ty,
}

impl TypedBlock {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedBlock {
            id: self.id,
            body: self.body.into_iter().map(|e| e.mapping(m, r)).collect(),
            ret: m(self.ret),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedParameter {
    #[drive(skip)]
    pub name: Symbol,
    pub ty: Ty,
}

impl TypedParameter {
    pub fn import(self, module_id: ModuleId) -> Self {
        TypedParameter {
            name: self.name.import(module_id),
            ty: self.ty.import(module_id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedEffect {
    #[drive(skip)]
    pub name: Symbol,
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedFunc {
    #[drive(skip)]
    pub name: Symbol,
    #[drive(skip)]
    pub foralls: IndexSet<ForAll>,
    pub params: Vec<TypedParameter>,
    pub effects: Vec<TypedEffect>,
    pub effects_row: Row,
    pub body: TypedBlock,
    pub ret: Ty,
}

impl TypedFunc {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
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
pub struct TypedMatchArm {
    pub pattern: TypedPattern,
    pub body: TypedBlock,
}

impl TypedMatchArm {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedMatchArm {
            pattern: self.pattern.mapping(m, r),
            body: self.body.mapping(m, r),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub struct TypedRecordField {
    #[drive(skip)]
    pub name: Label,
    pub value: TypedExpr,
}

#[derive(Debug, Clone, PartialEq, Drive, DriveMut)]
pub enum TypedExprKind {
    Hole,
    InlineIR(#[drive(skip)] Box<TypedInlineIRInstruction>),
    LiteralArray(Vec<TypedExpr>),
    LiteralInt(#[drive(skip)] String),
    LiteralFloat(#[drive(skip)] String),
    LiteralTrue,
    LiteralFalse,
    LiteralString(#[drive(skip)] String),
    Tuple(Vec<TypedExpr>),
    Block(TypedBlock),
    CallEffect {
        #[drive(skip)]
        effect: Symbol,
        type_args: Vec<Ty>,
        args: Vec<TypedExpr>,
    },
    Call {
        callee: Box<TypedExpr>,
        callee_ty: Ty,
        type_args: Vec<Ty>,
        args: Vec<TypedExpr>,
        #[drive(skip)]
        callee_sym: Option<Symbol>,
    },
    // A member access on a concrete type (property, instance method, etc.)
    Member {
        receiver: Box<TypedExpr>,
        #[drive(skip)]
        label: Label,
        #[drive(skip)]
        label_span: crate::span::Span,
    },
    // Function stuff
    Func(TypedFunc),
    Variable(#[drive(skip)] Symbol),
    Constructor(#[drive(skip)] Symbol, Vec<Ty>),

    If(
        Box<TypedExpr>, /* condition */
        TypedBlock,     /* condition block */
        TypedBlock,     /* else block */
    ),

    // Match expression
    Match(
        Box<TypedExpr>,     // scrutinee: the value being matched
        Vec<TypedMatchArm>, // arms: [MatchArm(pattern, body)]
    ),

    // Record literal: {x: 1, y: 2}
    RecordLiteral {
        fields: Vec<TypedRecordField>,
    },

    /// Variational choice: alternatives for overloaded calls.
    /// During constraint solving, we create Choice nodes when we can't
    /// immediately determine which implementation to use. After resolution,
    /// these are specialized to the selected alternative.
    Choice {
        #[drive(skip)]
        dimension: DimensionId,
        alternatives: Vec<TypedExpr>,
    },
}

impl TypedExprKind {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        use TypedExprKind::*;
        match self {
            Hole => Hole,
            CallEffect {
                effect,
                type_args,
                args,
            } => CallEffect {
                effect,
                type_args: type_args.into_iter().map(&mut *m).collect(),
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
            Member {
                receiver,
                label,
                label_span,
            } => Member {
                receiver: receiver.mapping(m, r).into(),
                label,
                label_span,
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
pub struct TypedExpr {
    #[drive(skip)]
    pub id: NodeID,
    pub ty: Ty,
    pub kind: TypedExprKind,
}

impl TypedExpr {
    pub fn mapping(self, m: &mut impl FnMut(Ty) -> Ty, r: &mut impl FnMut(Row) -> Row) -> Self {
        TypedExpr {
            id: self.id,
            ty: m(self.ty),
            kind: self.kind.mapping(m, r),
        }
    }
}
