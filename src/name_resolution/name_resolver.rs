use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt::Display,
};

use crate::{
    ast::{AST, ASTPhase, Parsed},
    diagnostic::Diagnostic,
    name::Name,
    name_resolution::symbol::{DeclId, LocalId, Symbol, Symbols},
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        pattern::{Pattern, PatternKind},
    },
    span::Span,
    traversal::fold_mut::FoldMut,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameResolverError {
    UndefinedName(String),
}
impl Error for NameResolverError {}
impl Display for NameResolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedName(name) => write!(f, "Undefined name: {name}"),
        }
    }
}

#[derive(Default, Debug)]
pub struct Scope {
    decls: BTreeMap<String, DeclId>,
    locals: BTreeMap<String, LocalId>,
    // fields: BTreeMap<String, FieldId>,
}

#[derive(Default, Debug)]
pub struct CurrentFunc {
    capturable_locals: BTreeSet<LocalId>,
    captures: BTreeSet<LocalId>,
}

#[derive(Default, Debug)]
pub struct NameResolver {
    path: String,
    scopes: Vec<Scope>,
    symbols: Symbols,
    diagnostics: Vec<Diagnostic<NameResolverError>>,
    phase: NameResolved,
    current_funcs: Vec<CurrentFunc>,
}

pub enum NameResolverPass {
    Decls,
    Bodies,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct NameResolved {
    pub captures: BTreeMap<Symbol, BTreeSet<LocalId>>,
    pub is_captured: BTreeSet<LocalId>,
}

impl ASTPhase for NameResolved {}

impl NameResolver {
    pub fn resolve(ast: AST<Parsed>) -> AST<NameResolved> {
        let AST {
            path,
            roots,
            mut diagnostics,
            meta,
            ..
        } = ast;

        let mut resolver = NameResolver::default();
        resolver.start_scope();
        let roots = roots
            .into_iter()
            .map(|mut root| {
                resolver.fold_node_mut(&mut root);
                root
            })
            .collect();

        for diagnostic in resolver.diagnostics {
            diagnostics.push(diagnostic.into());
        }

        AST {
            path,
            roots,
            diagnostics,
            meta,
            phase: resolver.phase,
        }
    }

    fn lookup(&mut self, name: &Name) -> Option<Symbol> {
        if let Some(sym) = self.lookup_decl(name) {
            return Some(Symbol::DeclId(sym));
        }

        if let Some(sym) = self.lookup_local(name) {
            return Some(Symbol::LocalId(sym));
        }

        None
    }

    fn declare_decl(&mut self, name: &Name) -> DeclId {
        let Some(scope) = self.scopes.last_mut() else {
            unreachable!("No scope specified");
        };

        tracing::debug!("declare decl {name:?}");

        let id = self.symbols.next_decl();
        scope.decls.insert(name.name_str(), id);

        id
    }
    fn lookup_decl(&mut self, name: &Name) -> Option<DeclId> {
        for scope in self.scopes.iter().rev() {
            if let Some(symbol_id) = scope.decls.get(&name.name_str()) {
                return Some(*symbol_id);
            }
        }

        None
    }

    fn declare_local(&mut self, name: &Name) -> LocalId {
        let Some(scope) = self.scopes.last_mut() else {
            unreachable!("No scope specified");
        };

        let id = self.symbols.next_local();
        scope.locals.insert(name.name_str(), id);

        tracing::debug!("declare decl {name:?} -> {id:?}");

        id
    }
    fn lookup_local(&mut self, name: &Name) -> Option<LocalId> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.locals.get(&name.name_str()) {
                if let Some(func) = self.current_funcs.last_mut()
                    && func.capturable_locals.contains(id)
                {
                    self.phase.is_captured.insert(*id);
                    func.captures.insert(*id);
                }

                return Some(*id);
            }
        }

        None
    }

    fn start_scope(&mut self) {
        self.scopes.push(Default::default());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn diagnostic(&mut self, span: Span, err: NameResolverError) {
        self.diagnostics.push(Diagnostic::<NameResolverError> {
            kind: err,
            path: self.path.clone(),
            span,
        });
    }
}

impl FoldMut for NameResolver {
    fn enter_decl_let_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind:
                DeclKind::Let {
                    lhs: Pattern { kind, .. },
                    ..
                },
            ..
        } = decl
        else {
            unreachable!()
        };

        let PatternKind::Bind(name) = kind else {
            unreachable!()
        };

        let id = self.declare_local(name);
        *name = Name::Resolved(Symbol::LocalId(id), name.name_str());
    }

    fn enter_expr_variable_mut(&mut self, expr: &mut Expr) {
        let Expr {
            kind: ExprKind::Variable(name),
            ..
        } = expr
        else {
            unreachable!()
        };

        let Some(sym) = self.lookup(name) else {
            self.diagnostic(expr.span, NameResolverError::UndefinedName(name.name_str()));
            return;
        };

        *name = Name::Resolved(sym, name.name_str());
    }

    ///////////////////////////////////////////////////////////////////////////
    // Scope handling
    ///////////////////////////////////////////////////////////////////////////
    fn enter_block_mut(&mut self, _block: &mut Block) {
        self.start_scope();
    }

    fn exit_block_mut(&mut self, _block: &mut Block) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Function handling
    ///////////////////////////////////////////////////////////////////////////
    fn enter_decl_func_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind:
                DeclKind::Func {
                    name,
                    generics: _,
                    params,
                    body: _,
                    ret: _,
                    attributes: _,
                },
            ..
        } = decl
        else {
            unreachable!()
        };

        let mut capturable_locals = BTreeSet::default();
        for scope in &self.scopes {
            capturable_locals.extend(scope.locals.values());
        }
        let current_func = CurrentFunc {
            capturable_locals,
            captures: Default::default(),
        };
        self.current_funcs.push(current_func);

        *name = Name::Resolved(self.declare_decl(name).into(), name.name_str());

        self.start_scope();

        for param in params {
            param.name = Name::Resolved(
                self.declare_local(&param.name).into(),
                param.name.name_str(),
            );
        }
    }

    fn exit_decl_func_mut(&mut self, decl: &mut Decl) {
        self.end_scope();

        let Decl {
            kind:
                DeclKind::Func {
                    name: Name::Resolved(sym, _),
                    ..
                },
            ..
        } = decl
        else {
            unreachable!()
        };

        let func = self.current_funcs.pop().unwrap();
        self.phase.captures.insert(*sym, func.captures);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Struct handling
    ///////////////////////////////////////////////////////////////////////////
    fn enter_decl_struct_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind: DeclKind::Struct { name, .. },
            ..
        } = decl
        else {
            unreachable!()
        };

        let id = self.declare_decl(name);
        *name = Name::Resolved(id.into(), name.name_str());
    }
}
