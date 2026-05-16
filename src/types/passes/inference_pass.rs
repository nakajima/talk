use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use crate::{
    ast::{AST, NameResolved},
    diagnostic::AnyDiagnostic,
    name_resolution::symbol::{ProtocolId, Symbol, set_symbol_names},
    node_id::NodeID,
    span::Span,
    types::{
        constraints::store::ConstraintStore,
        infer_row::Row,
        infer_ty::{Level, MetaVarId, Ty},
        predicate::Predicate,
        type_error::TypeError,
        type_operations::{InstantiationSubstitutions, UnificationSubstitutions},
        type_session::TypeSession,
        typed_ast::{TypedAST, TypedDecl, TypedStmt},
    },
};

mod auto_derived_body_synthesis;
mod blocks;
mod body_generation;
mod calls;
mod conformance_registration;
mod control_flow;
mod effect_handlers;
mod expressions;
mod finalize_types_pass;
mod functions;
mod let_declarations;
mod node_dispatch;
mod nominal_declarations;
mod patterns;
mod protocol_signature_discovery;
mod signature_discovery_pass;
mod solving;
mod type_annotations;

use finalize_types_pass::FinalizeTypesPass;
use signature_discovery_pass::SignatureDiscoveryPass;

type TypedRet<T> = Result<T, TypeError>;

#[derive(Clone, Debug)]
struct HandlerContext {
    ret: Ty,
}

// Protocol-level obligations derived from associated type declarations.
#[derive(Clone, Debug, Default)]
struct ProtocolAssociatedTypeRequirements {
    assoc_params: IndexSet<Symbol>,
    predicates: IndexSet<Predicate>,
}

impl ProtocolAssociatedTypeRequirements {
    fn is_empty(&self) -> bool {
        self.assoc_params.is_empty() && self.predicates.is_empty()
    }
}

pub type PendingTypeInstances =
    FxHashMap<MetaVarId, (NodeID, Span, Level, Symbol, Vec<(Ty, NodeID)>)>;

pub struct InferencePass<'a> {
    asts: &'a mut [&'a mut AST<NameResolved>],
    session: &'a mut TypeSession,
    constraints: ConstraintStore,
    instantiations: FxHashMap<NodeID, InstantiationSubstitutions>,
    substitutions: UnificationSubstitutions,
    tracked_returns: Vec<IndexSet<(NodeID, Ty)>>,
    tracked_effect_rows: Vec<Row>,
    handled_effects: IndexSet<Symbol>,
    handler_contexts: Vec<HandlerContext>,
    nominal_placeholders: FxHashMap<Symbol, (MetaVarId, Level)>,
    or_binders: Vec<FxHashMap<Symbol, Ty>>,
    diagnostics: IndexSet<AnyDiagnostic>,
    protocol_associated_type_requirements:
        FxHashMap<ProtocolId, ProtocolAssociatedTypeRequirements>,

    /// Tracks which function we're currently inside, for building the call tree.
    current_function: Option<Symbol>,

    /// Tracks the current nominal self type (for resolving SelfType annotations in extensions)
    current_self_ty: Option<Ty>,

    // These are what we eventually produce
    root_decls: Vec<TypedDecl>,
    root_stmts: Vec<TypedStmt>,
}

// Keep this phase wrapper local until there is enough body-inference structure
// to justify a real module extraction.
struct BodyInference<'pass, 'ast> {
    pass: &'pass mut InferencePass<'ast>,
}

impl<'pass, 'ast> BodyInference<'pass, 'ast> {
    fn new(pass: &'pass mut InferencePass<'ast>) -> Self {
        Self { pass }
    }

    fn run(&mut self) {
        self.pass.generate();
        self.pass.session.apply_all(&mut self.pass.substitutions);
    }
}

impl<'a> InferencePass<'a> {
    pub fn drive(
        asts: &'a mut [&'a mut AST<NameResolved>],
        session: &'a mut TypeSession,
    ) -> (TypedAST, Vec<AnyDiagnostic>) {
        let substitutions = UnificationSubstitutions::new(session.meta_levels.clone());
        let pass = InferencePass {
            asts,
            session,
            instantiations: Default::default(),
            constraints: Default::default(),
            substitutions,
            tracked_returns: Default::default(),
            diagnostics: Default::default(),
            nominal_placeholders: Default::default(),
            tracked_effect_rows: Default::default(),
            handled_effects: Default::default(),
            handler_contexts: Default::default(),
            or_binders: Default::default(),
            protocol_associated_type_requirements: Default::default(),
            current_function: None,
            current_self_ty: None,
            root_decls: Default::default(),
            root_stmts: Default::default(),
        };

        pass.drive_all()
    }

    fn drive_all(mut self) -> (TypedAST, Vec<AnyDiagnostic>) {
        let _s = set_symbol_names(self.session.resolved_names.symbol_names.clone());

        self.discover_signatures();
        self.infer_bodies();
        self.finalize_inference()
    }

    fn discover_signatures(&mut self) {
        SignatureDiscoveryPass::new(self).run();
    }

    fn infer_bodies(&mut self) {
        BodyInference::new(self).run();
    }

    fn finalize_inference(mut self) -> (TypedAST, Vec<AnyDiagnostic>) {
        {
            FinalizeTypesPass::new(&mut self).run();
        }

        let typed_ast = TypedAST {
            decls: self.root_decls,
            stmts: self.root_stmts,
        };

        let ast = typed_ast.apply(&mut self.substitutions, self.session);

        (ast, self.diagnostics.into_iter().collect())
    }
}
