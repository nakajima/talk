use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use crate::{
    SymbolID, SymbolTable,
    constraint_solver::Constraint,
    diagnostic::Diagnostic,
    environment::{Environment, Scope, TypeDef, TypedExprs},
    scope_tree::ScopeTree,
    span::Span,
    type_checker::{Ty, TypeDefs},
    typed_expr::TypedExpr,
};

use super::{
    expr::{Expr, ExprMeta},
    parser::ExprID,
};

pub trait Phase: Eq {
    type Data: Clone;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed;
impl Phase for Parsed {
    type Data = (); // No extra data for parsed
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameResolved;
impl Phase for NameResolved {
    type Data = (); // No extra data for name resolved (it just transforms the symbol table)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typed;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedInfo {
    pub roots: Vec<TypedExpr>,
    pub env: Environment,
}

impl Phase for Typed {
    type Data = TypedInfo;
}

#[derive(Debug, Clone)]
pub struct LoweredData {
    pub env: Environment,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lowered {}
impl Phase for Lowered {
    type Data = LoweredData;
}

#[derive(Default, Debug, PartialEq, Clone)]
pub struct SourceFile<P: Phase = Parsed> {
    pub path: PathBuf,
    roots: Vec<ExprID>,
    pub(crate) nodes: Vec<Expr>,
    pub(crate) meta: Vec<ExprMeta>,
    pub diagnostics: HashSet<Diagnostic>,
    phase_data: P::Data,
    pub scope_tree: ScopeTree,
}

impl SourceFile {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            roots: vec![],
            nodes: vec![],
            meta: vec![],
            phase_data: (),
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
            phase_data: (),
            diagnostics: self.diagnostics,
            scope_tree: self.scope_tree,
        }
    }
}

impl SourceFile<NameResolved> {
    pub fn to_typed(self, roots: Vec<TypedExpr>, env: Environment) -> SourceFile<Typed> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: TypedInfo { roots, env },
            diagnostics: self.diagnostics,
            scope_tree: self.scope_tree,
        }
    }
}

impl SourceFile<Typed> {
    pub fn set_typed_expr(&mut self, id: ExprID, typed_expr: TypedExpr) {
        self.phase_data.env.typed_exprs.insert(id, typed_expr);
    }

    pub fn typed_roots(&self) -> &[TypedExpr] {
        &self.phase_data.roots
    }

    pub fn replace_root_ids(&mut self, with: TypedExpr) {
        self.phase_data.roots = vec![with];
    }

    pub fn types_mut(&mut self) -> &mut HashMap<ExprID, TypedExpr> {
        &mut self.phase_data.env.typed_exprs
    }

    pub fn typed_exprs(&self) -> &HashMap<ExprID, TypedExpr> {
        &self.phase_data.env.typed_exprs
    }

    pub fn typed_expr(&self, expr_id: &ExprID) -> Option<TypedExpr> {
        self.phase_data.env.typed_exprs.get(expr_id).cloned()
    }

    pub fn type_defs(&self) -> TypeDefs {
        self.phase_data.env.types.clone()
    }

    pub fn type_def(&self, id: &SymbolID) -> Option<&TypeDef> {
        self.phase_data.env.types.get(id)
    }

    pub fn define(&mut self, id: ExprID, ty: Ty) {
        self.phase_data.env.typed_exprs.get_mut(&id).unwrap().ty = ty;
    }

    pub fn type_for(&self, id: ExprID) -> Option<Ty> {
        if let Some(typed_expr) = self.phase_data.env.typed_exprs.get(&id) {
            Some(typed_expr.ty.clone())
        } else {
            None
        }
    }

    pub fn type_from_symbol(&self, symbol_id: &SymbolID, symbol_table: &SymbolTable) -> Option<Ty> {
        if let Some(info) = symbol_table.get(symbol_id) {
            return self.type_for(info.expr_id);
        }

        None
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.phase_data.env.constraints()
    }

    pub fn export(self) -> (TypeDefs, Scope, TypedExprs) {
        let type_defs = self.phase_data.env.types;
        let typed_exprs = self.phase_data.env.typed_exprs;
        let scope = self.phase_data.env.scopes[0].clone();

        (type_defs, scope, typed_exprs)
    }

    pub fn register_direct_callable(&mut self, id: ExprID, symbol_id: SymbolID) {
        self.phase_data.env.direct_callables.insert(id, symbol_id);
    }

    pub fn get_direct_callable(&self, id: &ExprID) -> Option<SymbolID> {
        self.phase_data.env.direct_callables.get(id).copied()
    }

    pub fn to_lowered(self) -> SourceFile<Lowered> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: LoweredData {
                env: self.phase_data.env,
            },
            diagnostics: self.diagnostics,
            scope_tree: self.scope_tree,
        }
    }
}

impl SourceFile<Lowered> {
    pub fn type_def(&self, id: &SymbolID) -> Option<&TypeDef> {
        self.phase_data.env.types.get(id)
    }
}

impl<P: Phase> SourceFile<P> {
    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, expr: Expr, meta: ExprMeta) -> ExprID {
        let id = self.nodes.len() as ExprID;
        self.nodes.push(expr);
        self.meta.push(meta);
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

    // Gets the expr at a given index
    pub fn get(&self, index: &ExprID) -> Option<&Expr> {
        let index = *index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&self.nodes[index])
        }
    }

    // Gets the expr at a given index
    pub fn get_mut(&mut self, index: &ExprID) -> Option<&mut Expr> {
        let index = *index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&mut self.nodes[index])
        }
    }

    pub fn span(&self, expr_id: &ExprID) -> Span {
        let Some(meta) = self.meta.get(*expr_id as usize) else {
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
