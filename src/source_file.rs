use std::{cell::RefCell, collections::HashMap, path::PathBuf, rc::Rc};

use crate::{
    parsed_expr::ParsedExpr, scope_tree::ScopeTree, span::Span, typed_expr::TypedExpr,
};

use super::{expr::ExprMeta, parser::ExprID};

pub trait Phase: Eq {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed;
impl Phase for Parsed {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameResolved {
    pub scope_tree: ScopeTree,
}
impl Phase for NameResolved {}

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct Typed {
    pub roots: Vec<TypedExpr>,
    pub scope_tree: ScopeTree,
}
impl Phase for Typed {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lowered {}
impl Phase for Lowered {}

#[derive(Default, Debug, PartialEq, Clone)]
pub struct ExprMetaStorage {
    pub path: PathBuf,
    storage: HashMap<ExprID, ExprMeta>,
}

impl ExprMetaStorage {
    pub fn get(&self, id: &ExprID) -> Option<&ExprMeta> {
        self.storage.get(id)
    }

    pub fn insert(&mut self, id: ExprID, meta: ExprMeta) {
        self.storage.insert(id, meta);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ExprID, &ExprMeta)> {
        self.storage.iter()
    }

    pub fn span(&self, id: &ExprID) -> Option<Span> {
        let meta = self.storage.get(id)?;
        // handle single token expressions
        if meta.start == meta.end {
            Some(Span {
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
            })
        } else {
            Some(Span {
                path: self.path.clone(),
                start: meta.start.start,
                end: meta.end.end,
                start_line: meta.start.line,
                start_col: meta.start.col,
                end_line: meta.end.line,
                end_col: meta.end.col,
            })
        }
    }
}

#[derive(Default, Debug, PartialEq, Clone)]
pub struct SourceFile<P: Phase = Parsed> {
    pub path: PathBuf,
    roots: Vec<ParsedExpr>,
    pub(crate) meta: Rc<RefCell<ExprMetaStorage>>,
    pub(super) phase_data: P,
}

impl SourceFile {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path: path.clone(),
            roots: vec![],
            meta: Rc::new(RefCell::new(ExprMetaStorage {
                path,
                ..Default::default()
            })),
            phase_data: Parsed,
        }
    }
}

impl SourceFile<Parsed> {
    pub fn to_resolved(self, scope_tree: ScopeTree) -> SourceFile<NameResolved> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            meta: self.meta,
            phase_data: NameResolved { scope_tree },
        }
    }

    // Gets the root expr of the tree
    pub fn roots(&self) -> &Vec<ParsedExpr> {
        &self.roots
    }

    // Gets the root expr of the tree
    pub fn roots_mut(&mut self) -> &mut Vec<ParsedExpr> {
        &mut self.roots
    }
}

impl SourceFile<NameResolved> {
    // Gets the root expr of the tree
    pub fn roots(&self) -> &Vec<ParsedExpr> {
        &self.roots
    }

    // Gets the root expr of the tree
    pub fn roots_mut(&mut self) -> &mut Vec<ParsedExpr> {
        &mut self.roots
    }

    pub fn to_typed(&self, roots: Vec<TypedExpr>, scope_tree: ScopeTree) -> SourceFile<Typed> {
        SourceFile {
            path: self.path.clone(),
            roots: self.roots.clone(),
            meta: self.meta.clone(),
            phase_data: Typed { roots, scope_tree },
        }
    }

    pub fn as_parsed(&self) -> SourceFile<Parsed> {
        SourceFile {
            path: self.path.clone(),
            roots: self.roots.clone(),
            meta: self.meta.clone(),
            phase_data: Parsed,
        }
    }
}

impl SourceFile<Typed> {
    // pub fn typed_roots(&self, env: &Environment) -> Vec<TypedExpr> {
    //     self.root_ids()
    //         .iter()
    //         .filter_map(|root| env.typed_exprs.get(root).cloned())
    //         .collect::<Vec<TypedExpr>>()
    // }

    // pub fn types_mut(&mut self) -> &mut HashMap<(PathBuf, ExprID), TypedExpr> {
    //     &mut self.phase_data.env.typed_exprs
    // }

    // pub fn typed_exprs(&self) -> &HashMap<(PathBuf, ExprID), TypedExpr> {
    //     &self.phase_data.env.typed_exprs
    // }

    // pub fn type_defs(&self) -> TypeDefs {
    //     self.phase_data.env.types.clone()
    // }

    // pub fn type_def(&self, id: &SymbolID) -> Option<&TypeDef> {
    //     self.phase_data.env.types.get(id)
    // }

    // pub fn type_from_symbol(
    //     &self,
    //     symbol_id: &SymbolID,
    //     symbol_table: &SymbolTable,
    //     env: &Environment,
    // ) -> Option<Ty> {
    // }

    // pub fn constraints(&self) -> Vec<Constraint> {
    //     self.phase_data.env.constraints()
    // }

    pub fn typed_expr(&self, id: ExprID) -> Option<&TypedExpr> {
        TypedExpr::find_in(self.roots(), id)
    }

    pub fn roots(&self) -> &[TypedExpr] {
        &self.phase_data.roots
    }

    pub fn to_parsed(&self) -> SourceFile<Parsed> {
        SourceFile {
            path: self.path.clone(),
            roots: self.roots.clone(),
            meta: self.meta.clone(),
            phase_data: Parsed,
        }
    }

    pub fn to_lowered(self) -> SourceFile<Lowered> {
        SourceFile {
            path: self.path,
            roots: self.roots,
            meta: self.meta,
            phase_data: Lowered {},
        }
    }

    // Gets the root expr of the tree
    pub fn roots_mut(&mut self) -> &mut Vec<TypedExpr> {
        &mut self.phase_data.roots
    }
}

impl SourceFile<Lowered> {}

impl<P: Phase> SourceFile<P> {
    // Adds the expr to the parse tree and sets its ID
    pub fn add(&mut self, id: ExprID, meta: ExprMeta) {
        self.meta.borrow_mut().insert(id, meta);
    }

    pub fn push_root(&mut self, root: ParsedExpr) {
        self.roots.push(root);
    }

    pub fn span(&self, expr_id: &ExprID) -> Span {
        let meta = self.meta.borrow();
        let Some(meta) = meta.get(expr_id) else {
            return Span::default();
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
