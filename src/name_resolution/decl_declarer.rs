use crate::{
    name::Name,
    name_resolution::name_resolver::{NameResolver, Scope},
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        generic_decl::GenericDecl,
        match_arm::MatchArm,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    },
    traversal::fold_mut::FoldMut,
};

macro_rules! decl_pattern {
    ($pat:pat, $decl: expr) => {
        let Decl { kind: $pat, .. } = $decl else {
            unreachable!()
        };
    };
}

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

    fn enter_nominal(&mut self, id: NodeID, name: &mut Name, generics: &mut [GenericDecl]) {
        *name = self.resolver.declare_type(name);

        self.start_scope(id);

        for generic in generics {
            generic.name = self.resolver.declare_type(&generic.name);
        }
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
    fn enter_pattern_mut(&mut self, pattern: &mut Pattern) {
        let Pattern { kind, .. } = pattern;

        match kind {
            PatternKind::Bind(name) => *name = self.resolver.declare_local(name),
            PatternKind::Wildcard => (),
            _ => todo!(),
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Block scoping
    ///////////////////////////////////////////////////////////////////////////
    fn enter_match_arm_mut(&mut self, arm: &mut MatchArm) {
        self.start_scope(arm.id);
    }

    fn exit_match_arm_mut(&mut self, _arm: &mut MatchArm) {
        self.end_scope();
    }

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
        decl_pattern!(
            DeclKind::Func {
                name,
                generics,
                params: _,
                body: _,
                ret: _,
                attributes: _,
            },
            decl
        );

        *name = self.resolver.declare_value(name);

        self.start_scope(decl.id);

        for generic in generics {
            generic.name = self.resolver.declare_type(&generic.name);
        }
    }

    fn exit_decl_func_mut(&mut self, _decl: &mut Decl) {
        self.end_scope();
    }

    ///////////////////////////////////////////////////////////////////////////
    // Struct decls
    ///////////////////////////////////////////////////////////////////////////

    fn enter_decl_struct_mut(&mut self, decl: &mut Decl) {
        decl_pattern!(DeclKind::Struct { name, generics, .. }, decl);
        self.enter_nominal(decl.id, name, generics);
    }

    fn exit_decl_struct_mut(&mut self, _decl: &mut Decl) {
        self.end_scope();
    }

    fn enter_decl_property_mut(&mut self, decl: &mut Decl) {
        let Decl {
            kind: DeclKind::Property { name, .. },
            ..
        } = decl
        else {
            unreachable!()
        };

        *name = self.resolver.declare_value(name);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Enum decls
    ///////////////////////////////////////////////////////////////////////////
    fn enter_decl_enum_mut(&mut self, decl: &mut Decl) {
        decl_pattern!(DeclKind::Enum { name, generics, .. }, decl);
        self.enter_nominal(decl.id, name, generics);
    }

    fn exit_decl_enum_mut(&mut self, _decl: &mut Decl) {
        self.end_scope();
    }

    fn enter_decl_enum_variant_mut(&mut self, decl: &mut Decl) {
        decl_pattern!(DeclKind::EnumVariant(name, ..), decl);
        *name = self.resolver.declare_type(name);
    }

    ///////////////////////////////////////////////////////////////////////////
    // Protocol decls
    ///////////////////////////////////////////////////////////////////////////
    fn enter_decl_protocol_mut(&mut self, decl: &mut Decl) {
        decl_pattern!(DeclKind::Protocol { name, generics, .. }, decl);
        self.enter_nominal(decl.id, name, generics);
    }

    fn exit_decl_protocol_mut(&mut self, _decl: &mut Decl) {
        self.end_scope();
    }

    fn enter_decl_associated_mut(&mut self, decl: &mut Decl) {
        decl_pattern!(DeclKind::Associated { generic }, decl);
        generic.name = self.resolver.declare_type(&generic.name);
    }

    fn enter_decl_func_signature_mut(&mut self, decl: &mut Decl) {
        decl_pattern!(DeclKind::FuncSignature { name, .. }, decl);
        *name = self.resolver.declare_type(name);
    }
}
