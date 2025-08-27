use std::{collections::BTreeMap, error::Error, fmt::Display};

use crate::{
    ast::AST,
    diagnostic::Diagnostic,
    fold::Fold,
    fold_mut::FoldMut,
    name::Name,
    node::Node,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        pattern::{Pattern, PatternKind},
        type_annotation::TypeAnnotation,
    },
    span::Span,
    types::{
        name_replacer::NameReplacer,
        symbol::{DeclId, FieldId, LocalId, Symbol, Symbols},
    },
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
    fields: BTreeMap<String, FieldId>,
}

#[derive(Default, Debug)]
pub struct NameResolver {
    path: String,
    scopes: Vec<Scope>,
    symbols: Symbols,
    diagnostics: Vec<Diagnostic<NameResolverError>>,
}

impl NameResolver {
    pub fn resolve(ast: AST) -> AST {
        let AST {
            path,
            roots,
            mut diagnostics,
            meta,
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
        }
    }

    fn lookup(&mut self, name: &Name) -> Option<(Symbol, usize)> {
        if let Some((sym, depth)) = self.lookup_decl(name) {
            return Some((Symbol::Decl(sym), depth));
        }

        if let Some((sym, depth)) = self.lookup_local(name) {
            return Some((Symbol::Local(sym), depth));
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
    fn lookup_decl(&mut self, name: &Name) -> Option<(DeclId, usize)> {
        for (i, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(symbol_id) = scope.decls.get(&name.name_str()) {
                // The depth of the scope where the variable was found
                let found_depth = self.scopes.len() - 1 - i;
                return Some((*symbol_id, found_depth));
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
    fn lookup_local(&mut self, name: &Name) -> Option<(LocalId, usize)> {
        for (i, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(symbol_id) = scope.locals.get(&name.name_str()) {
                // The depth of the scope where the variable was found
                let found_depth = self.scopes.len() - 1 - i;
                return Some((*symbol_id, found_depth));
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
        *name = Name::Resolved(Symbol::Local(id), name.name_str());
    }

    fn enter_expr_variable_mut(&mut self, expr: &mut Expr) {
        let Expr {
            kind: ExprKind::Variable(name),
            ..
        } = expr
        else {
            unreachable!()
        };

        let Some((sym, _)) = self.lookup(name) else {
            self.diagnostic(expr.span, NameResolverError::UndefinedName(name.name_str()));
            return;
        };

        *name = Name::Resolved(sym, name.name_str());
    }

    // Scope handling
    fn enter_block_mut(&mut self, _block: &mut crate::node_kinds::block::Block) {
        self.start_scope();
    }

    fn exit_block_mut(&mut self, _block: &mut crate::node_kinds::block::Block) {
        self.end_scope();
    }
}
