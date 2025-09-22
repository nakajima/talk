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
    },
    on,
};

#[derive(VisitorMut)]
#[visitor(
    Stmt(enter, exit),
    FuncSignature(enter),
    Pattern(enter),
    MatchArm(enter, exit),
    Func(enter, exit),
    Decl(enter, exit)
)]
pub struct DeclDeclarer<'a> {
    pub(super) resolver: &'a mut NameResolver,
}

impl<'a> DeclDeclarer<'a> {
    pub fn new(resolver: &'a mut NameResolver) -> Self {
        Self { resolver }
    }

    pub fn at_module_scope(&self) -> bool {
        self.resolver.current_scope_id == Some(NodeID(0))
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

    fn enter_nominal(&mut self, id: NodeID, name: &mut Name, generics: &mut [GenericDecl]) {
        *name = self.resolver.declare_type(name);

        let Name::Resolved(Symbol::Type(type_id), _) = name else {
            unreachable!()
        };

        self.resolver
            .current_scope_mut()
            .unwrap()
            .types
            .insert("Self".into(), Symbol::Type(*type_id));

        self.start_scope(id);

        for generic in generics {
            generic.name = self.resolver.declare_type(&generic.name);
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
                    self.resolver.declare_global(name)
                } else {
                    self.resolver.declare_local(name)
                }
            }
            PatternKind::Record { fields } => {
                for field in fields {
                    let RecordFieldPatternKind::Bind(name) = &mut field.kind else {
                        continue;
                    };

                    *name = if self.at_module_scope() {
                        self.resolver.declare_global(name)
                    } else {
                        self.resolver.declare_local(name)
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
                    .unwrap_or_else(|| self.resolver.declare_global(name));

                self.start_scope(*id);

                for generic in generics {
                    generic.name = self.resolver.declare_type(&generic.name);
                }

                for param in params {
                    param.name = self.resolver.declare_param(&param.name);
                }
            }
        )
    }

    fn exit_func(&mut self, _func: &mut Func) {
        self.end_scope();
    }

    #[instrument(skip(self))]
    fn enter_func_signature(&mut self, func: &mut FuncSignature) {
        on!(func, FuncSignature { name, .. }, {
            *name = self.resolver.declare_instance_method(name);
        })
    }

    ///////////////////////////////////////////////////////////////////////////
    // Struct decls
    ///////////////////////////////////////////////////////////////////////////
    #[instrument(skip(self))]
    fn enter_decl(&mut self, decl: &mut Decl) {
        on!(
            &mut decl.kind,
            DeclKind::Struct { name, generics, .. }
                | DeclKind::Protocol { name, generics, .. }
                | DeclKind::Enum { name, generics, .. },
            {
                self.enter_nominal(decl.id, name, generics);
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

            for generic in generics {
                generic.name = self.resolver.declare_type(&generic.name);
            }
        });

        on!(&mut decl.kind, DeclKind::EnumVariant(name, ..), {
            *name = self.resolver.declare_variant(name);
        });

        on!(
            &mut decl.kind,
            DeclKind::Method {
                func: box Func { name, .. },
                is_static
            },
            {
                *name = if *is_static {
                    self.resolver.declare_static_method(name)
                } else {
                    self.resolver.declare_instance_method(name)
                };
            }
        );

        on!(&mut decl.kind, DeclKind::Associated { generic }, {
            generic.name = self.resolver.declare_type(&generic.name);
        });

        on!(
            &mut decl.kind,
            DeclKind::FuncSignature(FuncSignature { name, .. }),
            {
                *name = self.resolver.declare_global(name);
            }
        );

        on!(&mut decl.kind, DeclKind::Property { name, .. }, {
            *name = self.resolver.declare_property(name);
        });

        on!(&mut decl.kind, DeclKind::Init { name, .. }, {
            *name = self.resolver.declare_global(name);

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
