use derive_visitor::VisitorMut;
use tracing::instrument;

use crate::{
    name::Name,
    name_resolution::{
        name_resolver::{NameResolver, NameResolverError, Scope},
        symbol::Symbol,
    },
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind, RecordFieldPatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    on,
};

#[derive(VisitorMut)]
#[visitor(
    Stmt(enter, exit),
    FuncSignature,
    Pattern(enter),
    MatchArm(enter, exit),
    Func,
    Decl(enter, exit)
)]
pub struct DeclDeclarer<'a> {
    pub(super) resolver: &'a mut NameResolver,
}

// Dummy values for symbol type discrimination - actual values created by declare()
#[macro_export]
macro_rules! some {
    (Type) => {
        $crate::name_resolution::symbol::Symbol::Type($crate::name_resolution::symbol::TypeId::new(
            $crate::compiling::module::ModuleId::Current,
            0,
        ))
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
                $crate::compiling::module::ModuleId::Prelude,
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
            $crate::name_resolution::symbol::SynthesizedId(0),
        )
    };
}

impl<'a> DeclDeclarer<'a> {
    pub fn new(resolver: &'a mut NameResolver) -> Self {
        Self { resolver }
    }

    pub fn at_module_scope(&self) -> bool {
        matches!(self.resolver.current_scope_id, Some(NodeID(_, 0)))
    }

    pub fn start_scope(&mut self, id: NodeID) {
        let parent_id = self.resolver.current_scope_id;
        let scope = Scope::new(
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

    fn enter_nominal(
        &mut self,
        id: NodeID,
        name: &mut Name,
        generics: &mut [GenericDecl],
        is_protocol: bool,
    ) {
        *name = if is_protocol {
            self.resolver.declare(name, some!(Protocol), id)
        } else {
            self.resolver.declare(name, some!(Type), id)
        };

        self.resolver
            .current_scope_mut()
            .unwrap()
            .types
            .insert("Self".into(), name.symbol().unwrap());

        self.start_scope(id);

        for generic in generics {
            generic.name = self
                .resolver
                .declare(&generic.name, some!(TypeParameter), generic.id);
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(skip(self))]
    fn enter_stmt(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(block),
            ..
        }) = &mut stmt.kind
        {
            self.start_scope(block.id);
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
    // Local decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(skip(self))]
    fn enter_pattern(&mut self, pattern: &mut Pattern) {
        let Pattern { kind, .. } = pattern;

        match kind {
            PatternKind::Bind(name @ Name::Raw(_)) => {
                *name = if self.at_module_scope() {
                    self.resolver.declare(name, some!(Global), pattern.id)
                } else {
                    self.resolver
                        .declare(name, some!(DeclaredLocal), pattern.id)
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    let RecordFieldPatternKind::Bind(name) = &mut field.kind else {
                        continue;
                    };

                    *name = if self.at_module_scope() {
                        self.resolver.declare(name, some!(Global), pattern.id)
                    } else {
                        self.resolver
                            .declare(name, some!(DeclaredLocal), pattern.id)
                    }
                }
            }
            PatternKind::Tuple(_) => (),
            PatternKind::Wildcard => (),
            _ => (),
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block scoping
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(skip(self))]
    fn enter_match_arm(&mut self, arm: &mut MatchArm) {
        self.start_scope(arm.id);
    }

    fn exit_match_arm(&mut self, _arm: &mut MatchArm) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Funcs
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(skip(self))]
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
            },
            {
                *name = self
                    .resolver
                    .lookup(name)
                    .unwrap_or_else(|| self.resolver.declare(name, some!(Global), func_id));

                self.start_scope(*id);

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

    fn exit_func(&mut self, _func: &mut Func) {
        self.end_scope();
    }

    #[instrument(skip(self))]
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
                *name = self.resolver.declare(name, some!(InstanceMethod), func.id);

                self.start_scope(func.id);

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
    #[instrument(skip(self))]
    fn enter_decl(&mut self, decl: &mut Decl) {
        on!(
            &mut decl.kind,
            DeclKind::Struct { name, generics, .. } | DeclKind::Enum { name, generics, .. },
            {
                self.enter_nominal(decl.id, name, generics, false);
            }
        );

        on!(&mut decl.kind, DeclKind::Protocol { name, generics, .. }, {
            self.enter_nominal(decl.id, name, generics, true);
        });

        on!(
            &mut decl.kind,
            DeclKind::TypeAlias(
                TypeAnnotation {
                    kind: TypeAnnotationKind::Nominal {
                        name: lhs_name,
                        generics: lhs_generics,
                    },
                    ..
                },
                ..
            ),
            {
                if !lhs_generics.is_empty() {
                    panic!("can't define a typealias with generics");
                }

                *lhs_name = self.resolver.declare(lhs_name, some!(Type), decl.id);
            }
        );

        on!(&mut decl.kind, DeclKind::Extend { name, generics, .. }, {
            let Some(type_name) = self.resolver.lookup(name) else {
                self.resolver
                    .diagnostic(decl.span, NameResolverError::UndefinedName(name.name_str()));
                return;
            };

            *name = type_name;

            self.start_scope(decl.id);

            self.resolver
                .current_scope_mut()
                .unwrap()
                .types
                .insert("Self".into(), name.symbol().unwrap());

            for generic in generics {
                generic.name = self
                    .resolver
                    .declare(&generic.name, some!(Type), generic.id);
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

        on!(&mut decl.kind, DeclKind::Property { name, .. }, {
            *name = self.resolver.declare(name, some!(Property), decl.id);
        });

        on!(&mut decl.kind, DeclKind::Init { name, .. }, {
            *name = self.resolver.declare(name, some!(Global), decl.id);

            let Name::Resolved(Symbol::Global(..), _) = &name else {
                unreachable!()
            };

            self.start_scope(decl.id);
        });
    }

    fn exit_decl(&mut self, decl: &mut Decl) {
        on!(
            &mut decl.kind,
            DeclKind::Struct { .. }
                | DeclKind::Protocol { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Extend { .. },
            {
                self.end_scope();
            }
        );

        on!(&mut decl.kind, DeclKind::Init { .. }, {
            self.end_scope();
        });
    }
}
