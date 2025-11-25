use derive_visitor::VisitorMut;
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    id_generator::IDGenerator,
    name::Name,
    name_resolution::{
        name_resolver::{NameResolver, NameResolverError, Scope},
        symbol::{StructId, Symbol},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        body::Body,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    on,
    span::Span,
    types::type_session::TypeDefKind,
};

// Dummy values for symbol type discrimination - actual values created by declare()
#[macro_export]
macro_rules! some {
    (Struct) => {
        $crate::name_resolution::symbol::Symbol::Struct(
            $crate::name_resolution::symbol::StructId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Enum) => {
        $crate::name_resolution::symbol::Symbol::Enum($crate::name_resolution::symbol::EnumId::new(
            $crate::compiling::module::ModuleId::Current,
            0,
        ))
    };
    (TypeAlias) => {
        $crate::name_resolution::symbol::Symbol::TypeAlias(
            $crate::name_resolution::symbol::TypeAliasId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Global) => {
        $crate::name_resolution::symbol::Symbol::Global(
            $crate::name_resolution::symbol::GlobalId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Protocol) => {
        $crate::name_resolution::symbol::Symbol::Protocol(
            $crate::name_resolution::symbol::ProtocolId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Variant) => {
        $crate::name_resolution::symbol::Symbol::Variant(
            $crate::name_resolution::symbol::VariantId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Property) => {
        $crate::name_resolution::symbol::Symbol::Property(
            $crate::name_resolution::symbol::PropertyId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (InstanceMethod) => {
        $crate::name_resolution::symbol::Symbol::InstanceMethod(
            $crate::name_resolution::symbol::InstanceMethodId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Initializer) => {
        $crate::name_resolution::symbol::Symbol::Initializer(
            $crate::name_resolution::symbol::InitializerId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (MethodRequirement) => {
        $crate::name_resolution::symbol::Symbol::MethodRequirement(
            $crate::name_resolution::symbol::MethodRequirementId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (StaticMethod) => {
        $crate::name_resolution::symbol::Symbol::StaticMethod(
            $crate::name_resolution::symbol::StaticMethodId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (AssociatedType) => {
        $crate::name_resolution::symbol::Symbol::AssociatedType(
            $crate::name_resolution::symbol::AssociatedTypeId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
    (Builtin) => {
        $crate::name_resolution::symbol::Symbol::Builtin(
            $crate::name_resolution::symbol::BuiltinId::new(
                $crate::compiling::module::ModuleId::Builtin,
                0,
            ),
        )
    };
    // Local-only symbols (simple tuple structs)
    (TypeParameter) => {
        $crate::name_resolution::symbol::Symbol::TypeParameter(
            $crate::name_resolution::symbol::TypeParameterId(0),
        )
    };
    (DeclaredLocal) => {
        $crate::name_resolution::symbol::Symbol::DeclaredLocal(
            $crate::name_resolution::symbol::DeclaredLocalId(0),
        )
    };
    (ParamLocal) => {
        $crate::name_resolution::symbol::Symbol::ParamLocal(
            $crate::name_resolution::symbol::ParamLocalId(0),
        )
    };
    (PatternBindLocal) => {
        $crate::name_resolution::symbol::Symbol::PatternBindLocal(
            $crate::name_resolution::symbol::PatternBindLocalId(0),
        )
    };
    (Synthesized) => {
        $crate::name_resolution::symbol::Symbol::Synthesized(
            $crate::name_resolution::symbol::SynthesizedId::new(
                $crate::compiling::module::ModuleId::Current,
                0,
            ),
        )
    };
}

#[derive(VisitorMut)]
#[visitor(
    Stmt(enter, exit),
    FuncSignature,
    MatchArm(enter, exit),
    Func,
    Decl(enter, exit)
)]
pub struct DeclDeclarer<'a> {
    pub(super) resolver: &'a mut NameResolver,
    // For determining whether we need to synth an init
    type_members: FxHashMap<NodeID, TypeMembers>,
    // For synthesizing
    node_ids: &'a mut IDGenerator,
}

#[derive(Default)]
struct TypeMembers {
    initializers: Vec<DeclKind>,
    properties: Vec<DeclKind>,
}

#[allow(clippy::expect_used)]
impl<'a> DeclDeclarer<'a> {
    pub fn new(resolver: &'a mut NameResolver, node_ids: &'a mut IDGenerator) -> Self {
        Self {
            resolver,
            type_members: Default::default(),
            node_ids,
        }
    }

    pub fn at_module_scope(&self) -> bool {
        matches!(self.resolver.current_scope_id, Some(NodeID(_, 0)))
    }

    #[instrument(skip(self), fields(level = ?self.resolver.current_level))]
    pub fn start_scope(&mut self, binder: Option<Symbol>, id: NodeID, bump_level: bool) {
        let parent_id = self.resolver.current_scope_id;
        let scope = Scope::new(
            binder,
            if bump_level {
                self.resolver.current_level.next()
            } else {
                self.resolver.current_level
            },
            id,
            parent_id,
            self.resolver
                .current_scope()
                .map(|s| s.depth + 1)
                .unwrap_or(1),
        );
        tracing::trace!("start_scope: {:?}", scope);
        self.resolver.scopes.insert(id, scope);
        self.resolver.current_scope_id = Some(id);
    }

    pub fn end_scope(&mut self) {
        let current_id = self.resolver.current_scope_id.expect("no scope to end");
        let current = self
            .resolver
            .scopes
            .get(&current_id)
            .expect("did not find current scope");

        self.resolver.current_scope_id = current.parent_id;
    }

    ///////////////////////////////////////////////////////////////////////////
    // Local decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn declare_pattern(&mut self, pattern: &mut Pattern, bind_type: Symbol) {
        let Pattern { kind, .. } = pattern;

        match kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = if self.at_module_scope() {
                    self.resolver.declare(name, some!(Global), pattern.id)
                } else {
                    self.resolver.declare(name, bind_type, pattern.id)
                }
            }
            PatternKind::Bind(..) => {}
            PatternKind::Variant {
                enum_name, fields, ..
            } => {
                if let Some(enum_name) = enum_name {
                    *enum_name = self.resolver.declare(enum_name, some!(Variant), pattern.id);
                }

                for field in fields.iter_mut() {
                    self.declare_pattern(field, some!(PatternBindLocal));
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    match &mut field.kind {
                        RecordFieldPatternKind::Bind(name) => {
                            *name =
                                self.resolver
                                    .declare(name, some!(PatternBindLocal), pattern.id);
                        }
                        RecordFieldPatternKind::Equals { name, value, .. } => {
                            *name =
                                self.resolver
                                    .declare(name, some!(PatternBindLocal), pattern.id);
                            self.declare_pattern(value, some!(PatternBindLocal));
                        }
                        RecordFieldPatternKind::Rest => (),
                    }
                }
            }
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => {
                todo!()
            }
            PatternKind::Tuple(values) => {
                for value in values {
                    self.declare_pattern(value, bind_type);
                }
            }
            PatternKind::Wildcard => (),
            PatternKind::LiteralFalse
            | PatternKind::LiteralTrue
            | PatternKind::LiteralInt(..)
            | PatternKind::LiteralFloat(..) => (),
        }
    }

    fn enter_nominal(
        &mut self,
        id: NodeID,
        name: &mut Name,
        generics: &mut [GenericDecl],
        kind: TypeDefKind,
    ) {
        *name = match kind {
            TypeDefKind::Protocol => self.resolver.declare(name, some!(Protocol), id),
            TypeDefKind::Struct => self.resolver.declare(name, some!(Struct), id),
            TypeDefKind::Enum => self.resolver.declare(name, some!(Enum), id),
            TypeDefKind::Extension => self.resolver.lookup(name, Some(id)).unwrap_or(name.clone()),
        };

        let Ok(sym) = name.symbol() else {
            self.resolver
                .diagnostic(id, NameResolverError::Unresolved(name.clone()));
            return;
        };

        if let Some(parent) = self.resolver.nominal_stack.last() {
            self.resolver
                .phase
                .child_types
                .entry(*parent)
                .or_default()
                .insert(name.name_str().into(), sym);
        }

        self.resolver.nominal_stack.push(sym);
        self.type_members.insert(id, TypeMembers::default());

        self.start_scope(Some(sym), id, false);
        self.resolver
            .current_scope_mut()
            .expect("didn't get current scope")
            .types
            .insert("Self".into(), sym);

        for generic in generics {
            generic.name = self
                .resolver
                .declare(&generic.name, some!(TypeParameter), generic.id);
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(block),
            ..
        }) = &mut stmt.kind
        {
            self.start_scope(None, block.id, false);
        }
    }

    fn exit_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(..),
            ..
        }) = &mut stmt.kind
        {
            self.end_scope();
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block scoping
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn enter_match_arm(&mut self, arm: &mut MatchArm) {
        self.start_scope(None, arm.id, false);
        self.declare_pattern(&mut arm.pattern, some!(PatternBindLocal));
    }

    fn exit_match_arm(&mut self, _arm: &mut MatchArm) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Funcs
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn enter_func(&mut self, func: &mut Func) {
        let func_id = func.id;
        on!(
            func,
            Func {
                id,
                name,
                generics,
                params,
                body: _,
                ret: _,
                attributes: _,
                ..
            },
            {
                *name = self
                    .resolver
                    .lookup(name, Some(*id))
                    .unwrap_or_else(|| self.resolver.declare(name, some!(Global), func_id));

                if matches!(
                    name.symbol(),
                    Ok(Symbol::InstanceMethod(..)
                        | Symbol::StaticMethod(..)
                        | Symbol::Initializer(..))
                ) {
                    self.start_scope(
                        Some(func.name.symbol().unwrap_or_else(|_| unreachable!())),
                        *id,
                        false,
                    );
                }

                for generic in generics {
                    generic.name =
                        self.resolver
                            .declare(&generic.name, some!(TypeParameter), generic.id);
                }

                for param in params {
                    param.name = self
                        .resolver
                        .declare(&param.name, some!(ParamLocal), param.id);
                }
            }
        )
    }

    fn exit_func(&mut self, func: &mut Func) {
        if matches!(
            func.name.symbol(),
            Ok(Symbol::InstanceMethod(..) | Symbol::StaticMethod(..) | Symbol::Initializer(..))
        ) {
            self.end_scope();
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn enter_func_signature(&mut self, func: &mut FuncSignature) {
        on!(
            func,
            FuncSignature {
                name,
                params,
                generics,
                ..
            },
            {
                *name = self
                    .resolver
                    .declare(name, some!(MethodRequirement), func.id);

                self.start_scope(
                    Some(name.symbol().unwrap_or_else(|_| unreachable!())),
                    func.id,
                    false,
                );

                for generic in generics {
                    generic.name =
                        self.resolver
                            .declare(&generic.name, some!(TypeParameter), generic.id);
                }

                for param in params {
                    param.name = self
                        .resolver
                        .declare(&param.name, some!(ParamLocal), param.id);
                }
            }
        )
    }

    fn exit_func_signature(&mut self, _func: &mut FuncSignature) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Struct decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn enter_decl(&mut self, decl: &mut Decl) {
        on!(&mut decl.kind, DeclKind::Struct { name, generics, .. }, {
            self.enter_nominal(decl.id, name, generics, TypeDefKind::Struct);
        });

        on!(&mut decl.kind, DeclKind::Enum { name, generics, .. }, {
            self.enter_nominal(decl.id, name, generics, TypeDefKind::Enum);
        });

        on!(&mut decl.kind, DeclKind::Protocol { name, generics, .. }, {
            self.enter_nominal(decl.id, name, generics, TypeDefKind::Protocol);
        });

        on!(&mut decl.kind, DeclKind::TypeAlias(lhs_name, ..), {
            *lhs_name = self.resolver.declare(lhs_name, some!(TypeAlias), decl.id);

            if let Some(parent) = self.resolver.nominal_stack.last() {
                self.resolver
                    .phase
                    .child_types
                    .entry(*parent)
                    .or_default()
                    .insert(
                        lhs_name.name_str().into(),
                        lhs_name.symbol().unwrap_or_else(|_| unreachable!()),
                    );
            }
        });

        on!(&mut decl.kind, DeclKind::Extend { generics, .. }, {
            self.start_scope(None, decl.id, false);

            for generic in generics {
                generic.name =
                    self.resolver
                        .declare(&generic.name, some!(TypeParameter), generic.id);
            }
        });

        on!(&mut decl.kind, DeclKind::EnumVariant(name, ..), {
            *name = self.resolver.declare(name, some!(Variant), decl.id);
        });

        on!(
            &mut decl.kind,
            DeclKind::Method {
                func: box Func { name, generics, .. },
                is_static
            },
            {
                *name = if *is_static {
                    self.resolver.declare(name, some!(StaticMethod), decl.id)
                } else {
                    self.resolver.declare(name, some!(InstanceMethod), decl.id)
                };

                for generic in generics {
                    generic.name = self.resolver.declare(&generic.name, some!(TypeParameter), decl.id);
                }
            }
        );

        on!(&mut decl.kind, DeclKind::Associated { generic }, {
            generic.name = self
                .resolver
                .declare(&generic.name, some!(AssociatedType), decl.id);
            let parent = self
                .resolver
                .nominal_stack
                .last()
                .expect("did not get parent protocol for associated type");
            self.resolver
                .phase
                .child_types
                .entry(*parent)
                .or_default()
                .insert(
                    generic.name.name_str().into(),
                    generic.name.symbol().unwrap_or_else(|_| unreachable!()),
                );
        });

        on!(
            &mut decl.kind,
            DeclKind::FuncSignature(FuncSignature { name, generics, .. }),
            {
                *name = self.resolver.declare(name, some!(Global), decl.id);

                for generic in generics {
                    generic.name =
                        self.resolver
                            .declare(&generic.name, some!(TypeParameter), decl.id);
                }
            }
        );

        let decl_kind = decl.kind.clone();

        on!(&mut decl.kind, DeclKind::Property { name, .. }, {
            *name = self.resolver.declare(name, some!(Property), decl.id);
            let id = self
                .resolver
                .current_scope_id
                .expect("didn't get current scope id");
            self.type_members
                .entry(id)
                .or_default()
                .properties
                .push(decl_kind.clone());
        });

        on!(&mut decl.kind, DeclKind::Init { name, .. }, {
            let id = self
                .resolver
                .current_scope_id
                .expect("didn't get current scope id");
            self.type_members
                .entry(id)
                .or_default()
                .initializers
                .push(decl_kind);

            *name = self.resolver.declare(name, some!(Initializer), decl.id);

            self.start_scope(None, decl.id, false);
        });

        on!(&mut decl.kind, DeclKind::Let { lhs, .. }, {
            self.declare_pattern(lhs, some!(DeclaredLocal));
            for (id, binder) in lhs.collect_binders() {
                self.start_scope(Some(binder), id, true);
            }
        });
    }

    fn exit_decl(&mut self, decl: &mut Decl) {
        on!(
            &mut decl.kind,
            DeclKind::Struct {
                name: Name::Resolved(Symbol::Struct(type_id), _),
                body,
                ..
            },
            {
                let type_members = self
                    .type_members
                    .remove(&decl.id)
                    .expect("didn't get type members");

                if type_members.initializers.is_empty() {
                    self.synthesize_init(body, &type_members, *type_id);
                }

                self.end_scope();
            }
        );

        on!(
            &mut decl.kind,
            DeclKind::Protocol { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Extend { .. }
                | DeclKind::Init { .. },
            {
                self.end_scope();
            }
        );

        on!(&mut decl.kind, DeclKind::Let { lhs, .. }, {
            for _ in lhs.collect_binders() {
                self.end_scope();
            }
        });

        on!(
            &mut decl.kind,
            DeclKind::Protocol { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Extend { .. }
                | DeclKind::Struct { .. },
            {
                self.resolver.nominal_stack.pop();
            }
        );
    }

    fn synthesize_init(&mut self, body: &mut Body, type_members: &TypeMembers, type_id: StructId) {
        let init_id = NodeID(FileID::SYNTHESIZED, self.node_ids.next_id());
        tracing::debug!("synthesizing init for type {type_id:?} as: {init_id:?}");
        let init_name = self
            .resolver
            .declare(&"init".into(), some!(Synthesized), init_id);

        self.start_scope(None, init_id, false);

        // Need to synthesize an init
        let self_param_name = self.resolver.declare(
            &Name::Raw("self".into()),
            some!(ParamLocal),
            NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
        );
        let mut params: Vec<Parameter> = vec![Parameter {
            id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
            span: Span::SYNTHESIZED,
            name: self_param_name.clone(),
            name_span: Span::SYNTHESIZED,
            type_annotation: Some(TypeAnnotation {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: TypeAnnotationKind::SelfType(Name::SelfType(type_id.into())),
            }),
        }];

        let mut assignments: Vec<Node> = vec![];
        for property in type_members.properties.iter() {
            let DeclKind::Property {
                name,
                is_static,
                type_annotation,
                ..
            } = &property
            else {
                continue;
            };

            if *is_static {
                continue;
            }

            let name = self.resolver.declare(
                &Name::Raw(name.name_str()),
                some!(ParamLocal),
                NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
            );
            params.push(Parameter {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                name: name.clone(),
                name_span: Span::SYNTHESIZED,
                type_annotation: type_annotation.clone(),
                span: Span::SYNTHESIZED,
            });

            let assignment = Node::Stmt(Stmt {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: StmtKind::Assignment(
                    Expr {
                        id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                        kind: ExprKind::Member(
                            Some(
                                Expr {
                                    id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                                    span: Span::SYNTHESIZED,
                                    kind: ExprKind::Variable(self_param_name.clone()),
                                }
                                .into(),
                            ),
                            name.name_str().into(),
                            Span::SYNTHESIZED,
                        ),
                        span: Span::SYNTHESIZED,
                    },
                    Expr {
                        id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                        kind: ExprKind::Variable(name),
                        span: Span::SYNTHESIZED,
                    },
                ),
            });

            assignments.push(assignment);
        }

        assignments.push(Node::Stmt(Stmt {
            id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
            span: Span::SYNTHESIZED,
            kind: StmtKind::Expr(Expr {
                id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                span: Span::SYNTHESIZED,
                kind: ExprKind::Variable(self_param_name),
            }),
        }));

        let init = Decl {
            id: init_id,
            span: Span::SYNTHESIZED,
            kind: DeclKind::Init {
                name: init_name,
                params,
                body: Block {
                    id: NodeID(FileID::SYNTHESIZED, self.node_ids.next_id()),
                    span: Span::SYNTHESIZED,
                    args: vec![],
                    body: assignments,
                },
            },
        };

        self.end_scope();

        body.decls.insert(0, init);
    }
}
