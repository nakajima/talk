use std::collections::HashMap;

use crate::{
    FileID, SymbolID, SymbolTable,
    constraint_solver::Constraint,
    environment::{Environment, Scope, TypeDef, TypedExprs},
    lowering::lowerer::IRFunction,
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
    pub functions: Vec<IRFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lowered {}
impl Phase for Lowered {
    type Data = LoweredData;
}

#[derive(Default, Debug, PartialEq, Eq, Clone)]
pub struct SourceFile<P: Phase = Parsed> {
    pub file_id: FileID,
    roots: Vec<ExprID>,
    pub(crate) nodes: Vec<Expr>,
    pub(crate) meta: Vec<ExprMeta>,
    phase_data: P::Data,
}

impl SourceFile {
    pub fn new(file_id: FileID) -> Self {
        Self {
            file_id,
            roots: vec![],
            nodes: vec![],
            meta: vec![],
            phase_data: (),
        }
    }
}

impl SourceFile<Parsed> {
    pub fn to_resolved(self) -> SourceFile<NameResolved> {
        SourceFile {
            file_id: self.file_id,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: (),
        }
    }
}

impl SourceFile<NameResolved> {
    pub fn to_typed(self, roots: Vec<TypedExpr>, env: Environment) -> SourceFile<Typed> {
        SourceFile {
            file_id: self.file_id,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: TypedInfo { roots, env },
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

    pub fn type_for(&self, id: ExprID) -> Ty {
        self.phase_data.env.typed_exprs.get(&id).unwrap().ty.clone()
    }

    pub fn type_from_symbol(&self, symbol_id: &SymbolID, symbol_table: &SymbolTable) -> Option<Ty> {
        if let Some(info) = symbol_table.get(symbol_id) {
            return Some(self.type_for(info.expr_id));
        }

        None
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.phase_data.env.constraints.clone()
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

    pub fn to_lowered(self, functions: Vec<IRFunction>) -> SourceFile<Lowered> {
        SourceFile {
            file_id: self.file_id,
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: LoweredData { functions },
        }
    }
}

impl SourceFile<Lowered> {
    pub fn functions(&self) -> Vec<IRFunction> {
        self.phase_data.functions.clone()
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
}
