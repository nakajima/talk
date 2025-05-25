use std::collections::HashMap;

use crate::{symbol_table::SymbolTable, type_checker::Ty, typed_expr::TypedExpr};

use super::{
    expr::{Expr, ExprMeta},
    parser::ExprID,
};

pub trait Phase {
    type Data: Clone;
}

#[derive(Debug, Clone)]
pub struct Parsed;
impl Phase for Parsed {
    type Data = (); // No extra data for parsed
}

#[derive(Debug, Clone)]
pub struct NameResolved;
impl Phase for NameResolved {
    type Data = SymbolTable; // Symbol table only after name resolution
}

#[derive(Debug, Clone)]
pub struct Typed;

impl Phase for Typed {
    type Data = (SymbolTable, Vec<TypedExpr>, HashMap<ExprID, TypedExpr>); // Both symbol table and types
}

#[derive(Default, Debug, Clone)]
pub struct SourceFile<P: Phase = Parsed> {
    roots: Vec<ExprID>,
    pub(crate) nodes: Vec<Expr>,
    pub(crate) meta: Vec<ExprMeta>,
    phase_data: P::Data,
}

impl SourceFile {
    pub fn new() -> Self {
        Self {
            roots: vec![],
            nodes: vec![],
            meta: vec![],
            phase_data: (),
        }
    }
}

impl SourceFile<Parsed> {
    pub fn to_resolved(self, symbol_table: SymbolTable) -> SourceFile<NameResolved> {
        SourceFile {
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: symbol_table,
        }
    }
}

impl SourceFile<NameResolved> {
    pub fn to_typed(
        self,
        roots: Vec<TypedExpr>,
        types: HashMap<ExprID, TypedExpr>,
    ) -> SourceFile<Typed> {
        SourceFile {
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: (self.phase_data, roots, types),
        }
    }
}

impl SourceFile<Typed> {
    pub fn types(&mut self) -> &mut HashMap<ExprID, TypedExpr> {
        &mut self.phase_data.2
    }

    pub fn define(&mut self, id: ExprID, ty: Ty) {
        self.phase_data.2.get_mut(&id).unwrap().ty = ty;
    }

    pub fn type_for(&self, id: ExprID) -> Ty {
        self.phase_data.2.get(&id).unwrap().ty.clone()
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
        self.roots.iter().map(|r| self.get(*r)).collect()
    }

    // Gets the root expr of the tree
    pub fn root_ids(&self) -> Vec<ExprID> {
        self.roots.clone()
    }

    // Gets the expr at a given index
    pub fn get(&self, index: ExprID) -> Option<&Expr> {
        let index = index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&self.nodes[index])
        }
    }

    // Gets the expr at a given index
    pub fn get_mut(&mut self, index: ExprID) -> Option<&mut Expr> {
        let index = index as usize;

        if self.nodes.len() <= index {
            None
        } else {
            Some(&mut self.nodes[index])
        }
    }
}
