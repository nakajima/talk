use std::collections::HashMap;

use crate::{
    SymbolID, SymbolInfo, SymbolKind,
    constraint_solver::Constraint,
    environment::{Environment, Scope, TypeDef},
    lowering::ir::IRFunction,
    symbol_table::SymbolTable,
    type_checker::{Ty, TypeDefs},
    typed_expr::TypedExpr,
};

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

#[derive(Debug, Clone)]
pub struct TypedInfo {
    pub symbol_table: SymbolTable,
    pub roots: Vec<TypedExpr>,
    pub env: Environment,
}

impl Phase for Typed {
    type Data = TypedInfo;
}

#[derive(Debug, Clone)]
pub struct LoweredData {
    pub symbol_table: SymbolTable,
    pub functions: Vec<IRFunction>,
}

#[derive(Debug, Clone)]
pub struct Lowered;
impl Phase for Lowered {
    type Data = LoweredData;
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
    pub fn add_symbol(&mut self, name: String, kind: SymbolKind, expr_id: ExprID) -> SymbolID {
        self.phase_data.add(&name, kind, expr_id)
    }

    pub fn to_typed(self, roots: Vec<TypedExpr>, env: Environment) -> SourceFile<Typed> {
        SourceFile {
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: TypedInfo {
                symbol_table: self.phase_data,
                roots,
                env,
            },
        }
    }
}

impl SourceFile<Typed> {
    pub fn set(&mut self, symbol_id: SymbolID, info: SymbolInfo) {
        self.phase_data.symbol_table.import(&symbol_id, info);
    }

    pub fn typed_roots(&self) -> &[TypedExpr] {
        &self.phase_data.roots
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

    pub fn type_def(&mut self, id: &SymbolID) -> Option<&mut TypeDef> {
        self.phase_data.env.types.get_mut(id)
    }

    pub fn define(&mut self, id: ExprID, ty: Ty) {
        self.phase_data.env.typed_exprs.get_mut(&id).unwrap().ty = ty;
    }

    pub fn type_for(&self, id: ExprID) -> Ty {
        self.phase_data.env.typed_exprs.get(&id).unwrap().ty.clone()
    }

    pub fn type_from_symbol(&self, symbol_id: &SymbolID) -> Option<Ty> {
        if let Some(info) = self.phase_data.symbol_table.get(symbol_id) {
            return Some(self.type_for(info.expr_id));
        }

        None
    }

    pub fn constraints(&self) -> Vec<Constraint> {
        self.phase_data.env.constraints.clone()
    }

    pub fn symbol_table(&self) -> SymbolTable {
        self.phase_data.symbol_table.clone()
    }

    pub fn export(self) -> (SymbolTable, TypeDefs, Scope) {
        let symbols = self.phase_data.symbol_table;
        let type_defs = self.phase_data.env.types;
        let scope = self.phase_data.env.scopes[0].clone();
        (symbols, type_defs, scope)
    }

    pub fn register_direct_callable(&mut self, id: ExprID, symbol_id: SymbolID) {
        self.phase_data.env.direct_callables.insert(id, symbol_id);
    }

    pub fn get_direct_callable(&self, id: &ExprID) -> Option<SymbolID> {
        self.phase_data.env.direct_callables.get(id).copied()
    }

    pub fn to_lowered(self, functions: Vec<IRFunction>) -> SourceFile<Lowered> {
        SourceFile {
            roots: self.roots,
            nodes: self.nodes,
            meta: self.meta,
            phase_data: LoweredData {
                symbol_table: self.phase_data.symbol_table,
                functions,
            },
        }
    }

    pub fn symbol_info(&self, symbol_id: &SymbolID) -> &SymbolInfo {
        self.phase_data
            .symbol_table
            .get(symbol_id)
            .unwrap_or_else(|| panic!("Did not find symbol info for {:?}", symbol_id))
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
