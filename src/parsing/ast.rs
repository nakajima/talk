use derive_visitor::{Drive, Visitor};

use crate::{
    diagnostic::AnyDiagnostic,
    node::Node,
    node_id::NodeID,
    node_kinds::{
        attribute::Attribute, block::Block, call_arg::CallArg, decl::Decl, expr::Expr, func::Func,
        generic_decl::GenericDecl, incomplete_expr::IncompleteExpr, match_arm::MatchArm,
        parameter::Parameter, pattern::Pattern, record_field::RecordField, stmt::Stmt,
        type_annotation::TypeAnnotation,
    },
    node_meta_storage::NodeMetaStorage,
};

pub trait ASTPhase: Clone + std::fmt::Debug {}

pub type NewAST = ();
impl ASTPhase for NewAST {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parsed;
impl ASTPhase for Parsed {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AST<Phase: ASTPhase = NewAST> {
    pub path: String,
    pub roots: Vec<Node>,
    pub diagnostics: Vec<AnyDiagnostic>,
    pub meta: NodeMetaStorage,
    pub phase: Phase,
}

impl<Phase: ASTPhase> AST<Phase> {
    pub fn find(&self, node_id: NodeID) -> Option<Node> {
        for root in &self.roots {
            let mut visitor = ASTNodeFinder {
                node_id,
                result: None,
            };

            root.drive(&mut visitor);
            if let Some(result) = visitor.result {
                return Some(result);
            }
        }

        None
    }
}

#[derive(Visitor)]
#[visitor(
    Node(enter),
    Attribute(enter),
    Block(enter),
    CallArg(enter),
    Decl(enter),
    Expr(enter),
    Func(enter),
    GenericDecl(enter),
    IncompleteExpr(enter),
    MatchArm(enter),
    Parameter(enter),
    RecordField(enter),
    Stmt(enter),
    TypeAnnotation(enter),
    Pattern(enter)
)]
struct ASTNodeFinder {
    node_id: NodeID,
    pub result: Option<Node>,
}

impl ASTNodeFinder {
    fn check<N: Into<Node> + Clone>(&mut self, node: &N) {
        if self.result.is_some() {
            return;
        }

        let node: Node = node.clone().into();
        if node.node_id() == self.node_id {
            self.result = Some(node);
        }
    }
    fn enter_node(&mut self, node: &Node) {
        self.check(node);
    }
    fn enter_attribute(&mut self, node: &Attribute) {
        self.check(node);
    }
    fn enter_block(&mut self, node: &Block) {
        self.check(node);
    }
    fn enter_call_arg(&mut self, node: &CallArg) {
        self.check(node);
    }
    fn enter_decl(&mut self, node: &Decl) {
        self.check(node);
    }
    fn enter_expr(&mut self, node: &Expr) {
        self.check(node);
    }

    fn enter_func(&mut self, node: &Func) {
        self.check(node);
    }
    fn enter_generic_decl(&mut self, node: &GenericDecl) {
        self.check(node);
    }
    fn enter_incomplete_expr(&mut self, node: &IncompleteExpr) {
        self.check(node);
    }
    fn enter_match_arm(&mut self, node: &MatchArm) {
        self.check(node);
    }
    fn enter_parameter(&mut self, node: &Parameter) {
        self.check(node);
    }
    fn enter_pattern(&mut self, node: &Pattern) {
        self.check(node);
    }
    fn enter_record_field(&mut self, node: &RecordField) {
        self.check(node);
    }
    fn enter_stmt(&mut self, node: &Stmt) {
        self.check(node);
    }
    fn enter_type_annotation(&mut self, node: &TypeAnnotation) {
        self.check(node);
    }
}
