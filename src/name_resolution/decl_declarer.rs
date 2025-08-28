use crate::{
    name_resolution::name_resolver::{NameResolver, Scope},
    node_id::NodeID,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    },
    traversal::fold_mut::FoldMut,
};

pub struct DeclDeclarer<'a> {
    resolver: &'a mut NameResolver,
}

impl<'a> DeclDeclarer<'a> {
    pub fn new(resolver: &'a mut NameResolver) -> Self {
        Self { resolver }
    }

    pub fn start_scope(&mut self, id: NodeID) {
        let scope = Scope::new(id, self.resolver.current_scope);
        let scope_id = self.resolver.scopes.insert(scope);
        self.resolver.scopes_by_node_id.insert(id, scope_id);
        self.resolver.node_ids_by_scope.insert(scope_id, id);
        self.resolver.current_scope = Some(scope_id);
    }

    pub fn end_scope(&mut self) {
        let current_id = self.resolver.current_scope.expect("no scope to end");
        let current = self
            .resolver
            .scopes
            .get(current_id)
            .expect("did not find current scope");

        self.resolver.current_scope = current.parent_id;
    }
}

impl<'a> FoldMut for DeclDeclarer<'a> {
    ///////////////////////////////////////////////////////////////////////////
    // Block expr decls
    ///////////////////////////////////////////////////////////////////////////
    fn enter_stmt_mut(&mut self, stmt: &mut Stmt) {
        if let StmtKind::Expr(Expr {
            kind: ExprKind::Block(block),
            ..
        }) = &mut stmt.kind
        {
            self.start_scope(block.id);
        }
    }

    fn exit_stmt_mut(&mut self, stmt: &mut Stmt) {
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

        match kind {
            PatternKind::Bind(name) => *name = self.resolver.declare_local(name),
            PatternKind::Wildcard => (),
            _ => todo!(),
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block scoping
    ///////////////////////////////////////////////////////////////////////////

    // fn enter_block_mut(&mut self, block: &mut Block) {
    //     self.start_scope(block.id, false);
    // }

    // fn exit_block_mut(&mut self, _block: &mut Block) {
    //     self.end_scope();
    // }

    ///////////////////////////////////////////////////////////////////////////
    // Func decls
    ///////////////////////////////////////////////////////////////////////////

    fn enter_decl_func_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind:
                DeclKind::Func {
                    name,
                    generics: _,
                    params: _,
                    body: _,
                    ret: _,
                    attributes: _,
                },
            ..
        } = decl
        else {
            unreachable!()
        };

        *name = self.resolver.declare_value(name);

        self.start_scope(decl.id);
    }

    fn exit_decl_func_mut(&mut self, _decl: &mut Decl) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Struct decls
    ///////////////////////////////////////////////////////////////////////////

    fn enter_decl_struct_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind: DeclKind::Struct { name, .. },
            ..
        } = decl
        else {
            unreachable!()
        };

        *name = self.resolver.declare_type(name);
    }
}
