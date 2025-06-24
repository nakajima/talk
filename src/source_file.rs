use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use crate::{
    diagnostic::Diagnostic, environment::Environment, scope_tree::ScopeTree, span::Span,
    type_checker::Ty, typed_expr::TypedExpr,
};

use super::{
    expr::{Expr, ExprMeta},
    parser::ExprID,
};

pub trait Phase: Eq {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed;
impl Phase for Parsed {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameResolved;
impl Phase for NameResolved {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Typed {}
impl Phase for Typed {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lowered {}
impl Phase for Lowered {}

#[derive(Default, Debug, PartialEq, Clone)]
pub struct SourceFile<P: Phase = Parsed> {
    pub path: PathBuf,
    roots: Vec<ExprID>,
    pub(crate) nodes: HashMap<ExprID, Expr>,
    pub(crate) meta: HashMap<ExprID, ExprMeta>,
    pub diagnostics: HashSet<Diagnostic>,
    phase_data: P,
    pub scope_tree: ScopeTree,
}

impl SourceFile {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            roots: vec![],
            nodes: Default::default(),
            meta: Default::default(),
            phase_data: Parsed,
            diagnostics: Default::default(),
            scope_tree: Default::default(),
        }
    }
}

impl SourceFile<Parsed> {
    pub fn to_resolved(self) -> SourceFile<NameResolved> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: NameResolved,
            diagnostics: self.diagnostics,
            scope_tree: self.scope_tree,
        }
    }
}

impl SourceFile<NameResolved> {
    pub fn to_typed(self) -> SourceFile<Typed> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: Typed {},
            diagnostics: self.diagnostics,
            scope_tree: self.scope_tree,
        }
    }
}

impl SourceFile<Typed> {
    pub fn set_typed_expr(&mut self, id: ExprID, typed_expr: TypedExpr, env: &mut Environment) {
        env.typed_exprs.insert(id, typed_expr);
    }

    pub fn typed_roots(&self, env: &Environment) -> Vec<TypedExpr> {
        self.root_ids()
            .iter()
            .filter_map(|root| env.typed_exprs.get(root).cloned())
            .collect::<Vec<TypedExpr>>()
    }

    // pub fn types_mut(&mut self) -> &mut HashMap<(PathBuf, ExprID), TypedExpr> {
    //     &mut self.phase_data.env.typed_exprs
    // }

    // pub fn typed_exprs(&self) -> &HashMap<(PathBuf, ExprID), TypedExpr> {
    //     &self.phase_data.env.typed_exprs
    // }

    pub fn typed_expr(&self, expr_id: &ExprID, env: &Environment) -> Option<TypedExpr> {
        env.typed_exprs.get(expr_id).cloned()
    }

    // pub fn type_defs(&self) -> TypeDefs {
    //     self.phase_data.env.types.clone()
    // }

    // pub fn type_def(&self, id: &SymbolID) -> Option<&TypeDef> {
    //     self.phase_data.env.types.get(id)
    // }

    pub fn define(&mut self, id: ExprID, ty: Ty, env: &mut Environment) {
        if let Some(typed_expr) = env.typed_exprs.get_mut(&id) {
            typed_expr.ty = ty;
        }
    }

    // pub fn type_from_symbol(
    //     &self,
    //     symbol_id: &SymbolID,
    //     symbol_table: &SymbolTable,
    //     env: &Environment,
    // ) -> Option<Ty> {
    // }

    pub fn type_for(&self, id: ExprID, env: &Environment) -> Option<Ty> {
        env.typed_exprs
            .get(&id)
            .map(|typed_expr| typed_expr.ty.clone())
    }

    // pub fn constraints(&self) -> Vec<Constraint> {
    //     self.phase_data.env.constraints()
    // }

    pub fn to_parsed(&self) -> SourceFile<Parsed> {
        SourceFile {
            path: self.path.clone(),
            roots: self.roots.clone(),
            nodes: self.nodes.clone(),
            meta: self.meta.clone(),
            phase_data: Parsed,
            diagnostics: self.diagnostics.clone(),
            scope_tree: self.scope_tree.clone(),
        }
    }

    pub fn to_lowered(self) -> SourceFile<Lowered> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: Lowered {},
            diagnostics: self.diagnostics,
            scope_tree: self.scope_tree,
        }
    }
}

impl SourceFile<Lowered> {}

impl<P: Phase> SourceFile<P> {
    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, id: ExprID, expr: Expr, meta: ExprMeta) -> ExprID {
        self.nodes.insert(id, expr);
        self.meta.insert(id, meta);
        id
    }

    pub fn diagnostics(&self) -> Vec<&Diagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.is_unhandled())
            .collect()
    }

    pub fn push_root(&mut self, root: ExprID) {
        self.roots.push(root);
    }

    // Gets the root expr of the tree
    pub fn roots(&self) -> Vec<Option<&Expr>> {
        self.roots.iter().map(|r| self.get(r)).collect()
    }

    // Gets the root expr of the tree
    pub fn root_ids(&self) -> Vec<ExprID> {
        self.roots.clone()
    }

    pub fn find_expr_id(&self, expr: fn(expr: &Expr) -> bool) -> Option<ExprID> {
        for (id, node) in self.nodes.iter() {
            if expr(node) {
                return Some(*id);
            }
        }

        None
    }

    // Gets the expr at a given index
    pub fn get(&self, index: &ExprID) -> Option<&Expr> {
        self.nodes.get(index)
    }

    // Gets the expr at a given index
    pub fn get_mut(&mut self, index: &ExprID) -> Option<&mut Expr> {
        self.nodes.get_mut(index)
    }

    pub fn span(&self, expr_id: &ExprID) -> Span {
        let Some(meta) = self.meta.get(expr_id) else {
            panic!("didn't get a span for expr: {expr_id}");
        };

        // handle single token expressions
        if meta.start == meta.end {
            Span {
                path: self.path.clone(),
                start: meta.start.start,
                end: meta.end.end,
                start_line: meta.start.line,
                start_col: meta
                    .start
                    .col
                    .saturating_sub(meta.start.end - meta.start.start),
                end_line: meta.end.line,
                end_col: meta.end.col,
            }
        } else {
            Span {
                path: self.path.clone(),
                start: meta.start.start,
                end: meta.end.end,
                start_line: meta.start.line,
                start_col: meta.start.col,
                end_line: meta.end.line,
                end_col: meta.end.col,
            }
        }
    }
}
