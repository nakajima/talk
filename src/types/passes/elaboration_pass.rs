use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use petgraph::{
    algo::kosaraju_scc,
    graph::{DiGraph, NodeIndex},
};
use rustc_hash::FxHashMap;
use tracing::instrument;

use crate::{
    ast::AST,
    compiling::module::ModuleId,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{AssociatedTypeId, ProtocolId, StructId, Symbol},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        generic_decl::GenericDecl,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    types::{
        infer_row::{RowMetaId, RowParamId},
        infer_ty::{Level, SkolemId, TypeParamId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        ty::SomeType,
        type_catalog::ConformanceStub,
        type_session::{TypeDefKind, TypeSession},
    },
};

// TODO: Add Level to Var once we support open rows
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum ElaborationRow {
    Empty(TypeDefKind),
    Extend {
        row: Box<ElaborationRow>,
        label: Label,
        ty: ElaborationTy,
    },
    Param(RowParamId),
    Pending,
}

impl ElaborationRow {
    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            Self::Empty(..) => (),
            Self::Param(id) => {
                result.push(ForAll::Row(*id));
            }
            Self::Extend { row, ty, .. } => {
                result.extend(ty.collect_foralls());
                result.extend(row.collect_foralls());
            }
            _ => (),
        }
        result
    }
}

#[derive(PartialEq, Debug, Eq, Clone, Hash)]
pub enum ElaborationTy {
    Hole(NodeID),
    Primitive(Symbol),

    Param(TypeParamId),
    Rigid(SkolemId),

    Projection {
        base: Box<ElaborationTy>,
        associated: Label,
    },

    Constructor {
        name: Name,
        params: Vec<ElaborationTy>,
        ret: Box<ElaborationTy>,
    },

    Func(Box<ElaborationTy>, Box<ElaborationTy>),
    Tuple(Vec<ElaborationTy>),
    Record(Box<ElaborationRow>),

    // Nominal types (we look up their information from the TypeCatalog)
    Nominal {
        symbol: Symbol,
    },
}

impl SomeType for ElaborationTy {
    type RowType = ElaborationRow;

    fn contains_var(&self) -> bool {
        false
    }
}

#[allow(non_snake_case)]
#[allow(non_upper_case_globals)]
impl ElaborationTy {
    pub const Int: ElaborationTy = ElaborationTy::Primitive(Symbol::Int);
    pub const Float: ElaborationTy = ElaborationTy::Primitive(Symbol::Float);
    pub const Bool: ElaborationTy = ElaborationTy::Primitive(Symbol::Bool);
    pub const Void: ElaborationTy = ElaborationTy::Primitive(Symbol::Void);
    pub fn String() -> ElaborationTy {
        ElaborationTy::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 2,
            }),
        }
    }
    pub fn Array(_t: ElaborationTy) -> ElaborationTy {
        ElaborationTy::Nominal {
            symbol: Symbol::Struct(StructId {
                module_id: ModuleId::Core,
                local_id: 3,
            }),
        }
    }

    pub fn collect_foralls(&self) -> Vec<ForAll> {
        let mut result = vec![];
        match self {
            ElaborationTy::Param(id) => result.push(ForAll::Ty(*id)),
            ElaborationTy::Rigid(..) => (),
            ElaborationTy::Primitive(..) => (),
            ElaborationTy::Projection { base, .. } => {
                result.extend(base.collect_foralls());
            }
            ElaborationTy::Constructor { params, .. } => {
                for item in params {
                    result.extend(item.collect_foralls());
                }
            }
            ElaborationTy::Func(ty, ty1) => {
                result.extend(ty.collect_foralls());
                result.extend(ty1.collect_foralls());
            }
            ElaborationTy::Tuple(items) => {
                for item in items {
                    result.extend(item.collect_foralls());
                }
            }
            ElaborationTy::Record(box row) => {
                result.extend(row.collect_foralls());
            }
            _ => (),
        }
        result
    }
}

impl EnvEntry<ElaborationTy> {
    pub(super) fn inner_ty(&self) -> ElaborationTy {
        match self {
            Self::Mono(ty) => ty.clone(),
            Self::Scheme(scheme) => scheme.ty.clone(),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum MemberKind {
    Initializer,
    Variant,
    Property,
    InstanceMethod,
    StaticMethod,
    MethodRequirement,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Members<T> {
    pub initializers: IndexMap<Label, T>,
    pub variants: IndexMap<Label, T>,
    pub properties: IndexMap<Label, T>,
    pub methods: IndexMap<Label, T>,
    pub static_methods: IndexMap<Label, T>,
}

impl<T> Members<T> {
    fn extend(&mut self, other: Members<T>) {
        self.initializers.extend(other.initializers);
        self.variants.extend(other.variants);
        self.properties.extend(other.properties);
        self.methods.extend(other.methods);
        self.static_methods.extend(other.static_methods);
    }

    fn map<U>(self, mut map: impl FnMut(MemberKind, T) -> U) -> Members<U> {
        Members {
            initializers: self
                .initializers
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::Initializer, v)))
                .collect(),
            variants: self
                .variants
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::Variant, v)))
                .collect(),
            properties: self
                .properties
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::Property, v)))
                .collect(),
            methods: self
                .methods
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::InstanceMethod, v)))
                .collect(),
            static_methods: self
                .static_methods
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::StaticMethod, v)))
                .collect(),
        }
    }
}

impl<T> Default for Members<T> {
    fn default() -> Self {
        Members {
            initializers: Default::default(),
            variants: Default::default(),
            properties: Default::default(),
            methods: Default::default(),
            static_methods: Default::default(),
        }
    }
}

pub trait ElaborationPhase: PartialEq + Clone + std::fmt::Debug {
    type T;
}

#[derive(PartialEq, Clone, Debug)]
pub struct RegisteredNames {}
impl ElaborationPhase for RegisteredNames {
    type T = ();
}

#[derive(PartialEq, Clone, Debug)]
pub struct ElaboratedToElaborationTys {}
impl ElaborationPhase for ElaboratedToElaborationTys {
    type T = (
        Symbol,
        ElaborationTy,
        IndexSet<ForAll>,
        IndexSet<Predicate<ElaborationTy>>,
    );
}

#[derive(PartialEq, Clone, Debug)]
pub struct ElaboratedToSchemes {}
impl ElaborationPhase for ElaboratedToSchemes {
    type T = (Symbol, EnvEntry<ElaborationTy>);
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Binder {
    Symbol(Symbol),
    Member(Symbol, Label),
}

impl Binder {
    pub fn symbol(&self) -> Symbol {
        match self {
            Binder::Symbol(symbol) => *symbol,
            Binder::Member(..) => todo!(),
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct SCCGraph {
    idx_map: FxHashMap<Binder, NodeIndex>,
    graph: DiGraph<Binder, NodeID>,
    rhs_ids: FxHashMap<Binder, NodeID>,
}

impl SCCGraph {
    pub fn rhs_id_for(&self, binder: &Binder) -> &NodeID {
        self.rhs_ids.get(binder).unwrap()
    }

    pub fn groups(&self) -> Vec<Vec<Binder>> {
        kosaraju_scc(&self.graph)
            .iter()
            .map(|ids| ids.iter().map(|id| self.graph[*id].clone()).collect())
            .collect()
    }

    pub fn add_node(&mut self, node: Binder, rhs_id: NodeID) -> NodeIndex {
        if let Some(idx) = self.idx_map.get(&node) {
            return *idx;
        }

        let idx = self.graph.add_node(node.clone());
        self.idx_map.insert(node.clone(), idx);
        self.rhs_ids.insert(node, rhs_id);
        idx
    }

    #[instrument(skip(self))]
    pub fn add_edge(&mut self, from: (Binder, NodeID), to: (Binder, NodeID), node_id: NodeID) {
        if from.0 == to.0 {
            return;
        }
        let from = self.add_node(from.0, from.1);
        let to = self.add_node(to.0, to.1);
        self.graph.update_edge(from, to, node_id);
    }
}

#[derive(Clone, Debug)]
pub struct ElaboratedTypes<Phase: ElaborationPhase = RegisteredNames> {
    pub nominals: FxHashMap<Symbol, Nominal<Phase::T>>,
    pub protocols: FxHashMap<Symbol, Protocol<Phase>>,
    pub globals: FxHashMap<Symbol, Phase::T>,
    pub canonical_row_vars: FxHashMap<Symbol, RowMetaId>,
    pub canonical_type_params: FxHashMap<Symbol, TypeParamId>,
    pub type_param_conformances: IndexMap<TypeParamId, IndexSet<(ProtocolId, Span)>>,
    // We need to track references between binders in the same scope so
    // we can handle things like mutual recursion.
    pub scc_graph: SCCGraph,
}

impl ElaboratedTypes<ElaboratedToSchemes> {}

impl<T: ElaborationPhase> Default for ElaboratedTypes<T> {
    fn default() -> Self {
        ElaboratedTypes {
            nominals: Default::default(),
            protocols: Default::default(),
            globals: Default::default(),
            scc_graph: Default::default(),
            canonical_row_vars: Default::default(),
            canonical_type_params: Default::default(),
            type_param_conformances: Default::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NominalKind {
    Struct,
    Enum,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Nominal<T> {
    pub name: Name,
    pub ty: T,
    pub node_id: NodeID,
    pub span: Span,
    pub kind: NominalKind,
    pub conformances: Vec<ConformanceStub>,
    pub child_types: IndexMap<Label, Symbol>,
    pub members: Members<T>,
}

#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::type_complexity)]
pub struct Protocol<Phase: ElaborationPhase> {
    pub name: Name,
    pub node_id: NodeID,
    pub self_id: TypeParamId,
    pub associated_types: IndexMap<
        Label,
        (
            Symbol,
            AssociatedTypeId,
            TypeParamId,
            IndexSet<Predicate<ElaborationTy>>,
        ),
    >,
    pub method_requirements: IndexMap<Label, Phase::T>,
    pub conformances: Vec<ConformanceStub>,
    pub child_types: IndexMap<Label, Symbol>,
    pub members: Members<Phase::T>,
}

impl Protocol<ElaboratedToElaborationTys> {
    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut foralls = IndexSet::default();

        foralls.insert(ForAll::Ty(self.self_id));
        foralls.extend(
            self.associated_types
                .values()
                .map(|(_, _, id, _)| ForAll::Ty(*id)),
        );

        foralls
    }
}

impl Protocol<ElaboratedToSchemes> {
    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut foralls = IndexSet::default();

        foralls.insert(ForAll::Ty(self.self_id));
        foralls.extend(
            self.associated_types
                .values()
                .map(|(_, _, id, _)| ForAll::Ty(*id)),
        );

        foralls
    }
}

// Walk the AST finding global funcs, lets, nominals and protocols. Extract
// what we can from their type annotations to make inference easier.
// TODO: Maybe we can just stash more info in ElaboratedTypes and not have
// to traverse the AST as many times? But also since we're not entering bodies
// maybe this is fine? I dunno we'll figure it out.
pub struct ElaborationPass<'a> {
    pub session: &'a mut TypeSession,
    pub canonical_row_vars: FxHashMap<Symbol, RowMetaId>,
    pub canonical_type_params: FxHashMap<Symbol, TypeParamId>,
    pub type_param_conformances: IndexMap<TypeParamId, IndexSet<(ProtocolId, Span)>>,
}

impl<'a> ElaborationPass<'a> {
    pub fn drive(
        asts: &'a [AST<NameResolved>],
        session: &'a mut TypeSession,
    ) -> ElaboratedTypes<ElaboratedToSchemes> {
        let mut pass = Self {
            session,
            canonical_row_vars: Default::default(),
            canonical_type_params: Default::default(),
            type_param_conformances: Default::default(),
        };

        let root_decls = asts
            .iter()
            .flat_map(|a| {
                a.roots
                    .clone()
                    .into_iter()
                    .filter_map(|n| {
                        if let Node::Decl(decl) = n {
                            Some(decl)
                        } else {
                            None
                        }
                    })
                    .collect_vec()
            })
            .collect_vec();

        let registered_names = pass.register_type_names(
            ElaboratedTypes::<RegisteredNames>::default(),
            root_decls.iter(),
            &mut Default::default(),
        );

        let infer_tys = pass.elaborate_to_infer_tys(registered_names, root_decls.iter());
        let mut scheme_tys = pass.elaborate_to_schemes(infer_tys, root_decls.iter());

        scheme_tys.canonical_row_vars = std::mem::take(&mut pass.canonical_row_vars);
        scheme_tys.canonical_type_params = std::mem::take(&mut pass.canonical_type_params);
        scheme_tys.type_param_conformances = std::mem::take(&mut pass.type_param_conformances);
        scheme_tys
    }

    #[instrument(skip(self, types, nodes, child_types))]
    pub fn register_type_names(
        &mut self,
        mut types: ElaboratedTypes<RegisteredNames>,
        nodes: impl Iterator<Item = &'a Decl>,
        child_types: &mut IndexMap<Label, Symbol>,
    ) -> ElaboratedTypes<RegisteredNames> {
        for node in nodes {
            let Decl { kind, .. } = &node;

            match kind {
                DeclKind::Let {
                    lhs: _,
                    type_annotation,
                    rhs:
                        Some(Expr {
                            id: expr_id,
                            kind: ExprKind::Func(func),
                            ..
                        }),
                } => {
                    types
                        .scc_graph
                        .add_node(Binder::Symbol(func.name.symbol()), *expr_id);

                    for generic in func.generics.iter() {
                        self.register_generic(generic);
                    }

                    if let Some(anno) = &type_annotation {
                        self.elaborate_type_annotation(anno.id, &types, &anno.kind);
                    }

                    types.globals.insert(func.name.symbol(), ());
                    self.collect_references(
                        &mut types,
                        (Binder::Symbol(func.name.symbol()), func.id),
                        func.body.body.iter(),
                    );
                }
                DeclKind::Let {
                    lhs:
                        Pattern {
                            kind: PatternKind::Bind(name),
                            ..
                        },
                    rhs: Some(rhs),
                    ..
                } => {
                    // Add the binding to the graph
                    types
                        .scc_graph
                        .add_node(Binder::Symbol(name.symbol()), rhs.id);
                    types.globals.insert(name.symbol(), ());

                    // Collect references from RHS (only adds edges for globals)
                    self.collect_references(
                        &mut types,
                        (Binder::Symbol(name.symbol()), rhs.id),
                        std::iter::once(rhs.clone()),
                    );
                }
                DeclKind::Associated { generic } => {
                    child_types.insert(generic.name.name_str().into(), generic.name.symbol());
                    self.register_generic(generic);
                }
                DeclKind::FuncSignature(signature) => {
                    for generic in &signature.generics {
                        self.register_generic(generic);
                    }
                }
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
                    body,
                    ..
                }
                | DeclKind::Extend {
                    name,
                    conformances,
                    generics,
                    body,
                    ..
                }
                | DeclKind::Enum {
                    name,
                    generics,
                    conformances,
                    body,
                    ..
                } => {
                    let kind = match name.symbol() {
                        Symbol::Struct(..) => NominalKind::Struct,
                        Symbol::Enum(..) => NominalKind::Enum,
                        _ => unreachable!(),
                    };

                    // Create TypeParamIds for explicit generic type parameters
                    for generic in generics {
                        self.register_generic(generic);
                    }

                    // Create the initial nominal that we'll pass through to future phases.
                    let mut nominal =
                        types
                            .nominals
                            .get(&name.symbol())
                            .cloned()
                            .unwrap_or_else(|| {
                                let id = self.session.new_row_meta_var_id(Level::default());
                                self.canonical_row_vars.insert(name.symbol(), id);
                                Nominal {
                                    ty: (),
                                    members: Default::default(),
                                    name: name.clone(),
                                    node_id: node.id,
                                    span: node.span,
                                    kind,
                                    conformances: Default::default(),
                                    child_types: Default::default(),
                                }
                            });

                    let conformance_stubs =
                        Self::collect_conformance_stubs(name.symbol(), conformances);

                    nominal.conformances.extend(conformance_stubs);

                    // Add this type to parent's children
                    child_types.insert(name.name_str().into(), name.symbol());

                    // Visit child types
                    types = self.register_type_names(
                        types,
                        body.decls.iter(),
                        &mut nominal.child_types,
                    );

                    // Add it to the list
                    types.nominals.insert(name.symbol(), nominal);
                }
                DeclKind::Protocol {
                    name,
                    conformances,
                    body,
                    ..
                } => {
                    tracing::trace!("registering {name}");
                    let id = self.session.new_type_param_id(None);
                    self.canonical_type_params.insert(name.symbol(), id);
                    let mut protocol = Protocol {
                        name: name.clone(),
                        node_id: node.id,
                        conformances: Self::collect_conformance_stubs(name.symbol(), conformances),
                        method_requirements: Default::default(),
                        child_types: Default::default(),
                        members: Default::default(),
                        self_id: id,
                        associated_types: Default::default(),
                    };

                    // Add this type to parent's children
                    child_types.insert(name.name_str().into(), name.symbol());

                    // Visit child types
                    types = self.register_type_names(
                        types,
                        body.decls.iter(),
                        &mut protocol.child_types,
                    );

                    // Add it to the list
                    types.protocols.insert(name.symbol(), protocol);
                }
                _ => (),
            }
        }

        types
    }

    // Now that we've got Nominals and Protocols known, we can start gathering their members
    #[instrument(skip(self, types, nodes))]
    pub fn elaborate_to_infer_tys(
        &mut self,
        mut types: ElaboratedTypes<RegisteredNames>,
        nodes: impl Iterator<Item = &'a Decl>,
    ) -> ElaboratedTypes<ElaboratedToElaborationTys> {
        let mut new_types = ElaboratedTypes::<ElaboratedToElaborationTys> {
            scc_graph: std::mem::take(&mut types.scc_graph),
            canonical_row_vars: std::mem::take(&mut types.canonical_row_vars),
            canonical_type_params: std::mem::take(&mut types.canonical_type_params),
            type_param_conformances: std::mem::take(&mut types.type_param_conformances),
            ..Default::default()
        };
        for node in nodes {
            let Decl { kind, .. } = &node;

            match &kind {
                DeclKind::Let {
                    lhs: _,
                    type_annotation,
                    rhs:
                        Some(Expr {
                            kind: ExprKind::Func(func),
                            ..
                        }),
                } => {
                    for generic in func.generics.iter() {
                        self.register_generic(generic);
                    }

                    if let Some(anno) = &type_annotation {
                        self.elaborate_type_annotation(anno.id, &types, &anno.kind);
                    }

                    let func_type = self.elaborate_func(&types, func);
                    new_types.globals.insert(func.name.symbol(), func_type);
                }
                DeclKind::Let {
                    lhs:
                        Pattern {
                            kind: PatternKind::Bind(name),
                            ..
                        },
                    type_annotation,
                    rhs,
                    ..
                } => {
                    let ty = match (&type_annotation, &rhs) {
                        (None, None) => ElaborationTy::Hole(node.id),
                        (Some(anno), None) => {
                            self.elaborate_type_annotation(anno.id, &types, &anno.kind)
                        }
                        (
                            None,
                            Some(
                                val @ Expr {
                                    kind:
                                        ExprKind::LiteralInt(..)
                                        | ExprKind::LiteralFloat(..)
                                        | ExprKind::LiteralTrue
                                        | ExprKind::LiteralFalse,
                                    ..
                                },
                            ),
                        ) => self.elaborate_literal(val),
                        (Some(anno), Some(_val)) => {
                            self.elaborate_type_annotation(anno.id, &types, &anno.kind)
                        }
                        _ => continue,
                    };

                    new_types.globals.insert(
                        name.symbol(),
                        (name.symbol(), ty, Default::default(), Default::default()),
                    );
                }

                DeclKind::Struct {
                    name,
                    body,
                    generics,
                    ..
                }
                | DeclKind::Enum {
                    name,
                    body,
                    generics,
                    ..
                }
                | DeclKind::Extend {
                    name,
                    body,
                    generics,
                    ..
                } => {
                    let nominal = types.nominals.get(&name.symbol()).cloned().unwrap();
                    let members = self.collect_members(name.symbol(), &mut new_types, &body.decls);
                    let symbol = name.symbol();
                    let mut foralls = IndexSet::default();
                    let mut predicates = IndexSet::default();
                    for generic in generics.iter() {
                        let id = self.register_generic(generic);
                        foralls.insert(ForAll::Ty(id));
                        for conformance in generic.conformances.iter() {
                            let protocol_id = ProtocolId::from(conformance.symbol());
                            predicates.insert(Predicate::Conforms {
                                param: id,
                                protocol_id,
                                span: conformance.span,
                            });
                        }
                    }

                    let nominal = new_types.nominals.entry(symbol).or_insert_with(|| Nominal {
                        members: Default::default(),
                        name: nominal.name,
                        node_id: nominal.node_id,
                        span: nominal.span,
                        kind: nominal.kind,
                        conformances: nominal.conformances,
                        child_types: nominal.child_types,
                        ty: (symbol, self.symbol_to_infer_ty(symbol), foralls, predicates),
                    });

                    nominal.members.extend(members);
                }
                DeclKind::Protocol { name, body, .. } => {
                    let protocol = types.protocols.get(&name.symbol()).cloned().unwrap();
                    let members = self.collect_members(name.symbol(), &mut new_types, &body.decls);
                    let (associated_types, method_requirements) =
                        self.collect_protocol_members(&types, &body.decls);
                    new_types.protocols.insert(
                        name.symbol(),
                        Protocol {
                            name: protocol.name,
                            node_id: protocol.node_id,
                            conformances: protocol.conformances,
                            child_types: protocol.child_types,
                            members,
                            self_id: protocol.self_id,
                            method_requirements,
                            associated_types,
                        },
                    );
                }
                _ => (),
            }
        }
        new_types
    }

    #[instrument(skip(self, types, nodes))]
    pub fn elaborate_to_schemes(
        &mut self,
        mut types: ElaboratedTypes<ElaboratedToElaborationTys>,
        nodes: impl Iterator<Item = &'a Decl>,
    ) -> ElaboratedTypes<ElaboratedToSchemes> {
        let mut new_types = ElaboratedTypes::<ElaboratedToSchemes> {
            scc_graph: std::mem::take(&mut types.scc_graph),
            canonical_row_vars: std::mem::take(&mut types.canonical_row_vars),
            canonical_type_params: std::mem::take(&mut types.canonical_type_params),
            type_param_conformances: std::mem::take(&mut types.type_param_conformances),
            ..Default::default()
        };

        for (sym, global) in types.globals {
            let (_, ty, foralls, predicates) = global;
            let entry = if foralls.is_empty() && predicates.is_empty() {
                EnvEntry::Mono(ty)
            } else {
                EnvEntry::Scheme(Scheme {
                    ty,
                    foralls,
                    predicates: predicates.into_iter().collect(),
                })
            };

            new_types.globals.insert(sym, (sym, entry));
        }

        for node in nodes {
            let Decl { kind, .. } = &node;

            match &kind {
                DeclKind::Struct { name, generics, .. }
                | DeclKind::Enum { name, generics, .. }
                | DeclKind::Extend { name, generics, .. } => {
                    let nominal = types.nominals.get(&name.symbol()).cloned().unwrap();
                    let mut foralls = IndexSet::default();
                    let mut predicates = vec![];
                    let mut generic_ids = vec![];
                    for generic in generics.iter() {
                        let (id, protocol_ids) = self.lookup_generic(generic.clone());
                        generic_ids.push(EnvEntry::Mono(ElaborationTy::Param(id)));
                        foralls.insert(ForAll::Ty(id));
                        for (protocol_id, span) in protocol_ids {
                            predicates.push(Predicate::Conforms {
                                param: id,
                                protocol_id,
                                span,
                            })
                        }
                    }

                    let ty = self.symbol_to_infer_ty(name.symbol());
                    let ty = if foralls.is_empty() && predicates.is_empty() {
                        EnvEntry::Mono(ty)
                    } else {
                        EnvEntry::Scheme(Scheme {
                            foralls: foralls.clone(),
                            predicates,
                            ty,
                        })
                    };

                    let members = nominal
                        .members
                        .map(|kind, m| self.upgrade_members_to_entries(kind, m, &foralls));

                    let nominal =
                        new_types
                            .nominals
                            .entry(name.symbol())
                            .or_insert_with(|| Nominal {
                                ty: (name.symbol(), ty),
                                members: Default::default(),
                                name: nominal.name,
                                node_id: nominal.node_id,
                                span: nominal.span,
                                kind: nominal.kind,
                                conformances: nominal.conformances,
                                child_types: nominal.child_types,
                            });

                    nominal.members.extend(members);
                }
                DeclKind::Protocol { name, .. } => {
                    let protocol = types.protocols.get(&name.symbol()).cloned().unwrap();
                    let foralls = protocol.collect_foralls();
                    let members = protocol
                        .members
                        .map(|k, m| self.upgrade_members_to_entries(k, m, &foralls));
                    let method_requirements = protocol
                        .method_requirements
                        .into_iter()
                        .map(|(label, m)| {
                            (
                                label,
                                self.upgrade_members_to_entries(
                                    MemberKind::MethodRequirement,
                                    m,
                                    &foralls,
                                ),
                            )
                        })
                        .collect();
                    new_types.protocols.insert(
                        name.symbol(),
                        Protocol {
                            name: protocol.name,
                            node_id: protocol.node_id,
                            conformances: protocol.conformances,
                            child_types: protocol.child_types,
                            members,
                            method_requirements,
                            self_id: protocol.self_id,
                            associated_types: protocol.associated_types,
                        },
                    );
                }
                _ => (),
            }
        }

        new_types
    }

    // Helpers
    #[instrument(skip(self, generic), fields(generic.name = %generic.name))]
    fn register_generic(&mut self, generic: &GenericDecl) -> TypeParamId {
        let id = self
            .canonical_type_params
            .get(&generic.name.symbol())
            .copied()
            .unwrap_or_else(|| self.session.new_type_param_id(None));

        self.canonical_type_params.insert(generic.name.symbol(), id);
        let mut conformances = IndexSet::default();
        for conformance in generic.conformances.iter() {
            conformances.insert((ProtocolId::from(conformance.symbol()), conformance.span));
        }
        self.type_param_conformances.insert(id, conformances);
        id
    }

    #[instrument(skip(self, generic), fields(generic.name = %generic.name))]
    fn lookup_generic(&mut self, generic: GenericDecl) -> (TypeParamId, Vec<(ProtocolId, Span)>) {
        let id = self
            .canonical_type_params
            .get(&generic.name.symbol())
            .unwrap_or_else(|| panic!("did not find canonical type param for {:?}", generic.name));

        (
            *id,
            generic
                .conformances
                .into_iter()
                .map(|c| match &c.kind {
                    TypeAnnotationKind::Nominal { name, .. } => {
                        (ProtocolId::try_from(name.symbol()), c.span)
                    }
                    _ => unreachable!(),
                })
                .collect(),
        )
    }

    #[instrument(skip(self))]
    fn upgrade_members_to_entries(
        &mut self,
        kind: MemberKind,
        ty: (
            Symbol,
            ElaborationTy,
            IndexSet<ForAll>,
            IndexSet<Predicate<ElaborationTy>>,
        ),
        type_foralls: &IndexSet<ForAll>,
    ) -> (Symbol, EnvEntry<ElaborationTy>) {
        let (sym, ty, mut foralls, predicates) = ty;
        foralls.extend(ty.collect_foralls());

        if kind != MemberKind::Property && kind != MemberKind::Variant {
            foralls.extend(type_foralls);
        }

        let entry = if foralls.is_empty() && predicates.is_empty() {
            EnvEntry::Mono(ty)
        } else {
            EnvEntry::Scheme(Scheme {
                ty,
                foralls,
                predicates: predicates.into_iter().collect(),
            })
        };

        (sym, entry)
    }

    #[instrument(skip(self, types, nodes))]
    #[allow(clippy::type_complexity)]
    fn collect_protocol_members<T: ElaborationPhase>(
        &mut self,
        types: &ElaboratedTypes<T>,
        nodes: &[Decl],
    ) -> (
        IndexMap<
            Label,
            (
                Symbol,
                AssociatedTypeId,
                TypeParamId,
                IndexSet<Predicate<ElaborationTy>>,
            ),
        >,
        IndexMap<
            Label,
            (
                Symbol,
                ElaborationTy,
                IndexSet<ForAll>,
                IndexSet<Predicate<ElaborationTy>>,
            ),
        >,
    ) {
        let mut associated_types = IndexMap::<
            Label,
            (
                Symbol,
                AssociatedTypeId,
                TypeParamId,
                IndexSet<Predicate<ElaborationTy>>,
            ),
        >::default();
        let mut method_requirements = IndexMap::<
            Label,
            (
                Symbol,
                ElaborationTy,
                IndexSet<ForAll>,
                IndexSet<Predicate<ElaborationTy>>,
            ),
        >::default();

        for node in nodes {
            let Decl { kind, .. } = &node;

            match kind {
                DeclKind::Associated { generic } => {
                    let Symbol::AssociatedType(associated_type_id) = generic.name.symbol() else {
                        unreachable!()
                    };

                    let (id, protocol_ids) = self.lookup_generic(generic.clone());
                    let predicates = protocol_ids
                        .into_iter()
                        .map(|(protocol_id, span)| Predicate::<ElaborationTy>::Conforms {
                            param: id,
                            protocol_id,
                            span,
                        })
                        .collect();
                    associated_types.insert(
                        generic.name.name_str().into(),
                        (generic.name.symbol(), associated_type_id, id, predicates),
                    );
                }
                DeclKind::MethodRequirement(req) | DeclKind::FuncSignature(req) => {
                    let mut foralls = IndexSet::default();
                    let mut predicates = IndexSet::default();
                    for generic in req.generics.iter() {
                        let id = self.register_generic(generic);
                        foralls.insert(ForAll::Ty(id));
                        for conformance in generic.conformances.iter() {
                            let protocol_id = ProtocolId::from(conformance.symbol());
                            predicates.insert(Predicate::Conforms {
                                param: id,
                                protocol_id,
                                span: conformance.span,
                            });
                        }
                    }

                    let ret = if let Some(box ret) = req.ret.clone() {
                        self.elaborate_type_annotation(ret.id, types, &ret.kind.clone())
                    } else {
                        ElaborationTy::Void
                    };
                    let ty = curry_stub(
                        req.params.iter().map(|param| {
                            param
                                .type_annotation
                                .as_ref()
                                .map(|anno| {
                                    self.elaborate_type_annotation(
                                        anno.id,
                                        types,
                                        &anno.kind.clone(),
                                    )
                                })
                                .unwrap_or_else(|| ElaborationTy::Hole(param.id))
                        }),
                        ret,
                    );

                    method_requirements.insert(
                        req.name.name_str().into(),
                        (req.name.symbol(), ty, foralls, predicates),
                    );
                }
                _ => continue,
            }
        }

        (associated_types, method_requirements)
    }

    #[instrument(skip(self, types, nodes))]
    #[allow(clippy::type_complexity)]
    fn collect_members<T: ElaborationPhase>(
        &mut self,
        self_symbol: Symbol,
        types: &mut ElaboratedTypes<T>,
        nodes: &[Decl],
    ) -> Members<(
        Symbol,
        ElaborationTy,
        IndexSet<ForAll>,
        IndexSet<Predicate<ElaborationTy>>,
    )> {
        let mut members = Members::default();

        for node in nodes {
            let Decl { kind, .. } = &node;

            match kind {
                DeclKind::Init { name, params, body } => {
                    let self_ty = self.symbol_to_infer_ty(self_symbol);
                    self.collect_references(
                        types,
                        (Binder::Symbol(name.symbol()), node.id),
                        body.body.iter(),
                    );

                    let params = params
                        .iter()
                        .map(|param| {
                            param
                                .type_annotation
                                .as_ref()
                                .map(|anno| {
                                    self.elaborate_type_annotation(
                                        anno.id,
                                        types,
                                        &anno.kind.clone(),
                                    )
                                })
                                .unwrap_or_else(|| ElaborationTy::Hole(param.id))
                        })
                        .collect_vec();

                    self.session
                        .type_catalog
                        .initializers
                        .entry(self_symbol)
                        .or_default()
                        .insert("init".into(), name.symbol());

                    members.initializers.insert(
                        Label::Named("init".into()),
                        (
                            name.symbol(),
                            curry_stub(params, self_ty),
                            Default::default(),
                            Default::default(),
                        ),
                    );
                }
                DeclKind::Method { func, is_static } => {
                    let result = self.elaborate_func(types, func);

                    if *is_static {
                        self.session
                            .type_catalog
                            .static_methods
                            .entry(self_symbol)
                            .or_default()
                            .insert(func.name.name_str().into(), func.name.symbol());

                        members
                            .static_methods
                            .insert(func.name.name_str().into(), result);
                    } else {
                        self.session
                            .type_catalog
                            .instance_methods
                            .entry(self_symbol)
                            .or_default()
                            .insert(func.name.name_str().into(), func.name.symbol());

                        members.methods.insert(func.name.name_str().into(), result);
                    }

                    self.collect_references(
                        types,
                        (Binder::Symbol(func.name.symbol()), func.id),
                        func.body.body.iter(),
                    );
                }
                DeclKind::FuncSignature(req) => {
                    for generic in req.generics.iter() {
                        self.register_generic(generic);
                    }
                }
                DeclKind::MethodRequirement(req) => {
                    for generic in req.generics.iter() {
                        self.register_generic(generic);
                    }
                }
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                    ..
                } => {
                    self.session
                        .type_catalog
                        .properties
                        .entry(self_symbol)
                        .or_default()
                        .insert(name.name_str().into(), name.symbol());

                    if *is_static {
                        todo!();
                    } else {
                        let ty = match (&type_annotation, &default_value) {
                            (None, None) => ElaborationTy::Hole(node.id),
                            (Some(anno), None) => {
                                self.elaborate_type_annotation(anno.id, types, &anno.kind)
                            }
                            (None, Some(_val)) => todo!(),
                            (Some(anno), Some(_val)) => {
                                self.elaborate_type_annotation(anno.id, types, &anno.kind)
                            }
                        };

                        members.properties.insert(
                            name.name_str().into(),
                            (name.symbol(), ty, Default::default(), Default::default()),
                        );
                    }
                }
                DeclKind::EnumVariant(name, _, annos) => {
                    self.session
                        .type_catalog
                        .properties
                        .entry(self_symbol)
                        .or_default()
                        .insert(name.name_str().into(), name.symbol());

                    let ty = match annos.len() {
                        0 => ElaborationTy::Void,
                        1 => self.elaborate_type_annotation(annos[0].id, types, &annos[0].kind),
                        _ => ElaborationTy::Tuple(
                            annos
                                .iter()
                                .map(|a| self.elaborate_type_annotation(a.id, types, &a.kind))
                                .collect(),
                        ),
                    };

                    members.variants.insert(
                        name.name_str().into(),
                        (name.symbol(), ty, Default::default(), Default::default()),
                    );
                }
                _ => (),
            }
        }

        members
    }

    #[instrument(skip(self))]
    fn symbol_to_infer_ty(&self, symbol: Symbol) -> ElaborationTy {
        match symbol {
            Symbol::Int => ElaborationTy::Int,
            Symbol::Float => ElaborationTy::Float,
            Symbol::Bool => ElaborationTy::Bool,
            Symbol::Void => ElaborationTy::Void,
            Symbol::TypeParameter(..) | Symbol::AssociatedType(..) => {
                let id = self.canonical_type_params.get(&symbol).unwrap_or_else(|| {
                    panic!(
                        "did not get canonical type param for symbol: {symbol:?} in {:?}",
                        self.canonical_type_params
                    )
                });

                ElaborationTy::Param(*id)
            }
            _ => ElaborationTy::Nominal { symbol },
        }
    }

    fn elaborate_func<T: ElaborationPhase>(
        &mut self,
        types: &ElaboratedTypes<T>,
        func: &Func,
    ) -> (
        Symbol,
        ElaborationTy,
        IndexSet<ForAll>,
        IndexSet<Predicate<ElaborationTy>>,
    ) {
        let mut foralls = IndexSet::default();
        let mut predicates = IndexSet::default();
        for generic in func.generics.iter() {
            let id = self.register_generic(generic);
            foralls.insert(ForAll::Ty(id));
            for conformance in generic.conformances.iter() {
                let protocol_id = ProtocolId::from(conformance.symbol());
                predicates.insert(Predicate::Conforms {
                    param: id,
                    protocol_id,
                    span: conformance.span,
                });
            }
        }

        let mut params = func
            .params
            .iter()
            .map(|param| {
                param
                    .type_annotation
                    .as_ref()
                    .map(|anno| self.elaborate_type_annotation(anno.id, types, &anno.kind.clone()))
                    .unwrap_or_else(|| ElaborationTy::Hole(param.id))
            })
            .collect::<Vec<_>>();

        // If it's a static method, it won't have a self param so we need to prepend a Void so that curry works properly
        if params.is_empty() {
            params.insert(0, ElaborationTy::Void);
        }

        let ty = curry_stub(
            params,
            func.ret
                .as_ref()
                .map(|t| self.elaborate_type_annotation(t.id, types, &t.kind))
                .unwrap_or_else(|| ElaborationTy::Hole(func.id)),
        );

        (func.name.symbol(), ty, foralls, predicates)
    }

    fn elaborate_literal(&self, literal: &Expr) -> ElaborationTy {
        match &literal.kind {
            ExprKind::LiteralInt(..) => ElaborationTy::Int,
            ExprKind::LiteralFloat(..) => ElaborationTy::Float,
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => ElaborationTy::Bool,
            _ => panic!("unhandled literal ty: {literal:?}"),
        }
    }

    #[instrument(skip(self, types))]
    fn elaborate_type_annotation<T: ElaborationPhase>(
        &self,
        id: NodeID,
        types: &ElaboratedTypes<T>,
        kind: &TypeAnnotationKind,
    ) -> ElaborationTy {
        match kind {
            TypeAnnotationKind::SelfType(name) => {
                let symbol = name.symbol();
                if matches!(symbol, Symbol::Protocol(..) | Symbol::AssociatedType(..)) {
                    ElaborationTy::Param(
                        *self
                            .canonical_type_params
                            .get(&symbol)
                            .unwrap_or_else(|| panic!("didn't get param for {symbol:?}")),
                    )
                } else {
                    self.symbol_to_infer_ty(symbol)
                }
            }
            TypeAnnotationKind::Nominal { name, .. } => self.symbol_to_infer_ty(name.symbol()),
            TypeAnnotationKind::NominalPath { base, member, .. } => {
                let base_sym = base.symbol();
                let base = self.elaborate_type_annotation(id, types, &base.kind);
                match base_sym {
                    Symbol::AssociatedType(..) => ElaborationTy::Projection {
                        base: Box::new(base),
                        associated: member.clone(),
                    },
                    Symbol::Protocol(..) => {
                        let child_sym = types
                            .protocols
                            .get(&base_sym)
                            .unwrap()
                            .child_types
                            .get(member)
                            .unwrap();
                        self.symbol_to_infer_ty(*child_sym)
                    }
                    Symbol::Enum(..) | Symbol::Struct(..) => {
                        let child_sym = types
                            .nominals
                            .get(&base_sym)
                            .unwrap_or_else(|| panic!("did not get nominal {base_sym:?} {base:?}"))
                            .child_types
                            .get(member)
                            .unwrap();
                        self.symbol_to_infer_ty(*child_sym)
                    }
                    Symbol::TypeParameter(..) => ElaborationTy::Projection {
                        base: Box::new(base),
                        associated: member.clone(),
                    },
                    _ => {
                        unimplemented!("base: {base:?}, member: {member:?}");
                    }
                }
            }
            _ => todo!(),
        }
    }

    #[instrument(skip(conformances))]
    fn collect_conformance_stubs(
        conforming_id: Symbol,
        conformances: &[TypeAnnotation],
    ) -> Vec<ConformanceStub> {
        conformances
            .iter()
            .map(|c| {
                let TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Protocol(protocol_id), _),
                    ..
                } = &c.kind
                else {
                    unreachable!();
                };

                ConformanceStub {
                    conforming_id,
                    protocol_id: *protocol_id,
                    span: c.span,
                }
            })
            .collect()
    }

    #[instrument(skip(self, types, nodes))]
    #[allow(clippy::only_used_in_recursion)]
    fn collect_references<T: ElaborationPhase>(
        &mut self,
        types: &mut ElaboratedTypes<T>,
        from: (Binder, NodeID),
        nodes: impl Iterator<Item = impl Into<Node>>,
    ) {
        for node in nodes {
            let node: Node = node.into();
            let (Node::Stmt(Stmt {
                kind: StmtKind::Expr(expr),
                ..
            })
            | Node::Expr(expr)) = node
            else {
                continue;
            };

            match &expr.kind {
                ExprKind::LiteralArray(exprs) => {
                    self.collect_references(types, from.clone(), exprs.iter())
                }
                ExprKind::Unary(.., box expr) => {
                    self.collect_references(types, from.clone(), [expr.clone()].iter())
                }
                ExprKind::Binary(box expr, .., box expr1) => self.collect_references(
                    types,
                    from.clone(),
                    [expr.clone(), expr1.clone()].iter(),
                ),
                ExprKind::Tuple(exprs) => {
                    self.collect_references(types, from.clone(), exprs.iter())
                }
                ExprKind::Call { callee, args, .. } => {
                    if let ExprKind::Variable(Name::Resolved(sym, _)) = &callee.kind {
                        // Only track references to global-scope symbols
                        if matches!(
                            sym,
                            Symbol::Global(_) | Symbol::StaticMethod(_) | Symbol::InstanceMethod(_)
                        ) {
                            types.scc_graph.add_edge(
                                from.clone(),
                                (Binder::Symbol(*sym), expr.id),
                                expr.id,
                            );
                        }
                        continue;
                    }

                    self.collect_references(types, from.clone(), args.iter());

                    if let ExprKind::Variable(Name::Resolved(sym, _)) = &callee.kind {
                        if matches!(sym, Symbol::Global(_)) {
                            // Only globals!
                            types.scc_graph.add_edge(
                                from.clone(),
                                (Binder::Symbol(*sym), expr.id),
                                expr.id,
                            );
                        }

                        continue;
                    }

                    if let ExprKind::Member(
                        Some(box Expr {
                            kind:
                                ExprKind::Variable(Name::SelfType(sym))
                                | ExprKind::Constructor(Name::Resolved(sym, ..)),
                            ..
                        }),
                        label,
                        ..,
                    ) = &callee.kind
                    {
                        types.scc_graph.add_edge(
                            from.clone(),
                            (Binder::Member(*sym, label.clone()), expr.id),
                            expr.id,
                        );
                        continue;
                    }

                    if let ExprKind::Member(
                        Some(box Expr {
                            kind: ExprKind::Variable(Name::Resolved(Symbol::ParamLocal(..), named)),
                            ..
                        }),
                        label,
                        ..,
                    ) = &callee.kind
                        && named == "self"
                        && let Binder::Symbol(parent) = from.0
                    {
                        types.scc_graph.add_edge(
                            from.clone(),
                            (Binder::Member(parent, label.clone()), expr.id),
                            expr.id,
                        );
                        continue;
                    }
                }
                ExprKind::Func(..) => { /* we don't do this recursively */ }
                ExprKind::If(box expr, conseq, alt) => {
                    self.collect_references(types, from.clone(), [expr.clone()].iter());
                    self.collect_references(types, from.clone(), conseq.body.iter());
                    self.collect_references(types, from.clone(), alt.body.iter());
                }
                ExprKind::Match(box expr, match_arms) => {
                    self.collect_references(types, from.clone(), [expr.clone()].iter());
                    for arm in match_arms {
                        self.collect_references(types, from.clone(), arm.body.body.iter());
                    }
                }
                ExprKind::RecordLiteral { fields, .. } => {
                    let fields = fields.iter().map(|f| f.value.clone()).collect_vec();
                    self.collect_references(types, from.clone(), fields.iter());
                }
                _ => (),
            }
        }
    }
}

fn curry_stub<I: IntoIterator<Item = ElaborationTy>>(
    params: I,
    ret: ElaborationTy,
) -> ElaborationTy {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| {
            ElaborationTy::Func(Box::new(p), Box::new(acc))
        })
}

#[cfg(test)]
pub mod tests {
    use indexmap::{indexmap, indexset};

    use super::*;
    use crate::{
        assert_eq_diff,
        compiling::{
            driver::{Driver, Source},
            module::ModuleId,
        },
        name_resolution::symbol::{AssociatedTypeId, EnumId, GlobalId, ProtocolId, StructId},
        node_id::FileID,
        span::Span,
    };

    pub fn curry<I: IntoIterator<Item = ElaborationTy>>(
        params: I,
        ret: ElaborationTy,
    ) -> ElaborationTy {
        params
            .into_iter()
            .collect::<Vec<_>>()
            .into_iter()
            .rfold(ret, |acc, p| {
                ElaborationTy::Func(Box::new(p), Box::new(acc))
            })
    }

    impl SCCGraph {
        fn neighbors_for(&self, node: &Binder) -> Vec<Binder> {
            self.graph
                .neighbors(self.idx_map[node])
                .map(|idx| self.graph[idx].clone())
                .collect()
        }
    }

    fn elaborate(code: &'static str) -> ElaboratedTypes<ElaboratedToSchemes> {
        let driver = Driver::new_bare(vec![Source::from(code)], Default::default());
        let resolved = driver.parse().unwrap().resolve_names().unwrap();
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let asts: Vec<_> = resolved.phase.asts.into_values().collect();
        ElaborationPass::drive(asts.as_slice(), &mut session)
    }

    #[test]
    fn registers_globals() {
        assert_eq_diff!(
            *elaborate("let fizz = 123; fizz")
                .globals
                .get(&GlobalId::from(1).into())
                .unwrap(),
            (Symbol::Global(1.into()), EnvEntry::Mono(ElaborationTy::Int))
        );
        assert_eq_diff!(
            *elaborate("let fizz = true; fizz")
                .globals
                .get(&GlobalId::from(1).into())
                .unwrap(),
            (
                Symbol::Global(1.into()),
                EnvEntry::Mono(ElaborationTy::Bool)
            )
        );
    }

    #[test]
    fn registers_func_items() {
        assert_eq_diff!(
            *elaborate("func fizz() {}",)
                .globals
                .get(&GlobalId::from(1).into())
                .unwrap(),
            (
                Symbol::Global(1.into()),
                EnvEntry::Mono(ElaborationTy::Func(
                    ElaborationTy::Void.into(),
                    ElaborationTy::Hole(NodeID::ANY).into()
                ))
            )
        );
    }

    #[test]
    fn registers_generic_func_items() {
        assert_eq_diff!(
            *elaborate("func fizz<T>(t: T) -> T { t }",)
                .globals
                .get(&GlobalId::from(1).into())
                .unwrap(),
            (
                Symbol::Global(1.into()),
                EnvEntry::Scheme(Scheme {
                    ty: ElaborationTy::Func(
                        ElaborationTy::Param(1.into()).into(),
                        ElaborationTy::Param(1.into()).into()
                    ),
                    foralls: indexset! {ForAll::Ty(1.into())},
                    predicates: Default::default()
                })
            )
        );
    }

    #[test]
    fn registers_struct() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };

        assert_eq_diff!(
            *elaborate("struct A {}",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal::<(Symbol, EnvEntry<ElaborationTy>)> {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        (Symbol::Synthesized(1.into()), EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone())))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: Default::default(),
                ty: (Symbol::Struct(1.into()), EnvEntry::Mono(struct_ty.clone())),
            }
        );
    }

    #[test]
    fn registers_generics() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };
        assert_eq_diff!(
            *elaborate("struct A<B> { let b: B }",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                      Label::Named("init".into()) => (Symbol::Synthesized(1.into()), EnvEntry::Scheme(
                        Scheme {
                          foralls: indexset! { ForAll::Ty(1.into()) },
                          predicates: Default::default(),
                          ty: curry(vec![struct_ty.clone(), ElaborationTy::Param(1.into())], struct_ty.clone())
                        }
                      ))
                    },
                    variants: Default::default(),
                    properties: indexmap::indexmap! {
                      Label::Named("b".into()) =>
                          (Symbol::Property(1.into()), EnvEntry::Scheme(Scheme { foralls: indexset! { ForAll::Ty(1.into()) }, predicates: vec![], ty: ElaborationTy::Param(1.into()) }))
                    },
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: Default::default(),
                ty: (
                    Symbol::Struct(1.into()),
                    EnvEntry::Scheme(Scheme {
                        foralls: [ForAll::Ty(1.into())].into(),
                        predicates: vec![],
                        ty: ElaborationTy::Nominal {
                            symbol: StructId::from(1).into(),
                        }
                    })
                ),
            }
        );
    }

    #[test]
    fn registers_generic_conformances() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };
        assert_eq_diff!(
            *elaborate("protocol P {}; struct A<B: P> { let b: B }",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                      (Symbol::Synthesized(1.into()), EnvEntry::Scheme(
                        Scheme {
                          foralls: indexset! { ForAll::Ty(2.into()) },
                          predicates: Default::default(),
                          ty: curry(vec![struct_ty.clone(), ElaborationTy::Param(2.into())], struct_ty.clone())
                        }
                      ))
                    },
                    variants: Default::default(),
                    properties: indexmap::indexmap! {
                    Label::Named("b".into()) =>
                        (Symbol::Property(1.into()), EnvEntry::Scheme(Scheme { foralls: indexset! { ForAll::Ty(2.into()) }, predicates: vec![], ty: ElaborationTy::Param(2.into()) }))
                    },
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: Default::default(),
                ty: (
                    Symbol::Struct(1.into()),
                    EnvEntry::Scheme(Scheme {
                        foralls: [ForAll::Ty(2.into())].into(),
                        predicates: vec![Predicate::Conforms {
                            param: 2.into(),
                            protocol_id: ProtocolId::from(1),
                            span: Span::ANY
                        }],
                        ty: ElaborationTy::Nominal {
                            symbol: StructId::from(1).into(),
                        }
                    })
                ),
            }
        );
    }

    #[test]
    fn registers_struct_conformances() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };
        assert_eq!(
            *elaborate("protocol A {} ; protocol B {} ; struct C: A, B {}",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "C".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        (Symbol::Synthesized(1.into()), EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone())))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![
                    ConformanceStub {
                        protocol_id: ProtocolId::from(1),
                        conforming_id: StructId::from(1).into(),
                        span: Span::ANY,
                    },
                    ConformanceStub {
                        protocol_id: ProtocolId::from(2),
                        conforming_id: StructId::from(1).into(),
                        span: Span::ANY,
                    }
                ],
                child_types: Default::default(),
                ty: (Symbol::Struct(1.into()), EnvEntry::Mono(struct_ty.clone())),
            }
        );
    }

    #[test]
    fn registers_struct_extend_conformances() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };
        assert_eq_diff!(
            *elaborate(
                "protocol A {} ; protocol B {} ; struct C {}; extend C: A {} ; extend C: B {}",
            )
            .nominals
            .get(&StructId::from(1).into())
            .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "C".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                       (Symbol::Synthesized(1.into()),  EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone())))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![
                    ConformanceStub {
                        protocol_id: ProtocolId::from(1),
                        conforming_id: StructId::from(1).into(),
                        span: Span::ANY,
                    },
                    ConformanceStub {
                        protocol_id: ProtocolId::from(2),
                        conforming_id: StructId::from(1).into(),
                        span: Span::ANY,
                    }
                ],
                child_types: Default::default(),
                ty: (Symbol::Struct(1.into()), EnvEntry::Mono(struct_ty.clone())),
            }
        );
    }

    #[test]
    fn child_types() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };
        assert_eq_diff!(
            *elaborate(
                "struct A {
                  struct B {}
                  enum C {}
                  protocol D {}
                }",
            )
            .nominals
            .get(&StructId::from(1).into())
            .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                       (Symbol::Synthesized(2.into()),  EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone())))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: indexmap![
                    "B".into() => StructId::from(2).into(),
                    "C".into() => EnumId::from(3).into(),
                    "D".into() => ProtocolId::from(1).into(),
                ],
                ty: (Symbol::Struct(1.into()), EnvEntry::Mono(struct_ty.clone())),
            }
        );
    }

    #[test]
    fn registers_enum() {
        assert_eq_diff!(
            *elaborate("enum A {}",)
                .nominals
                .get(&EnumId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(EnumId::from(1).into(), "A".into()),
                node_id: NodeID(FileID(0), 2),
                span: Span::ANY,
                kind: NominalKind::Enum,
                members: Members {
                    initializers: Default::default(),
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: Default::default(),
                ty: (
                    Symbol::Enum(1.into()),
                    EnvEntry::Mono(ElaborationTy::Nominal {
                        symbol: EnumId::from(1).into(),
                    })
                ),
            }
        );
    }

    #[test]
    fn registers_protocol() {
        assert_eq_diff!(
            *elaborate("protocol A { func fizz() -> Int }",)
                .protocols
                .get(&ProtocolId::from(1).into())
                .unwrap(),
            Protocol::<ElaboratedToSchemes> {
                name: Name::Resolved(ProtocolId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                conformances: vec![],
                child_types: Default::default(),
                method_requirements: indexmap!("fizz".into() => (Symbol::MethodRequirement(1.into()), EnvEntry::Scheme(
                  Scheme {
                    foralls: indexset! { ForAll::Ty(1.into()) },
                    predicates: Default::default(),
                    ty: ElaborationTy::Func(
                      ElaborationTy::Param(1.into()).into(),
                      ElaborationTy::Int.into(),
                    )
                  }
                ))),
                members: Default::default(),
                self_id: 1.into(),
                associated_types: Default::default(),
            }
        );
    }

    #[test]
    fn registers_associated_types() {
        assert_eq_diff!(
            *elaborate(
                "
                protocol A { associated F }
                protocol B {
                  associated C
                  associated D: A

                  func fizz<T: A>() -> T.F
                }
              ",
            )
            .protocols
            .get(&ProtocolId::from(2).into())
            .unwrap(),
            Protocol::<ElaboratedToSchemes> {
                self_id: 3.into(),
                name: Name::Resolved(ProtocolId::from(2).into(), "B".into()),
                node_id: NodeID::ANY,
                conformances: vec![],
                child_types: indexmap! {
                  "C".into() => AssociatedTypeId::from(2).into(),
                  "D".into() => AssociatedTypeId::from(3).into(),
                },
                method_requirements: indexmap::indexmap! {
                  Label::Named("fizz".into()) =>
                      (Symbol::MethodRequirement(1.into()), EnvEntry::Scheme(Scheme {
                          ty:ElaborationTy::Func(
                              Box::new(ElaborationTy::Param(3.into())), // Self
                              Box::new(
                                ElaborationTy::Projection {
                                    base: Box::new(ElaborationTy::Param(6.into())),
                                    associated: Label::Named("F".into()),
                                }
                              )
                          ),
                          foralls: [ForAll::Ty(3.into()),ForAll::Ty(4.into()),ForAll::Ty(5.into()),ForAll::Ty(6.into()),].into(),
                          predicates: [
                              Predicate::Conforms {
                                  param: 6.into(),
                                  protocol_id: 1.into(),
                                  span: Span::ANY
                              }
                          ].into()
                      }))
                },
                associated_types: indexmap::indexmap! {
                    "C".into() => (Symbol::AssociatedType(2.into()), 2.into(), 4.into(), indexset!{}),
                    "D".into() => (Symbol::AssociatedType(3.into()), 3.into(), 5.into(), indexset!{
                        Predicate::Conforms {
                            param: 5.into(),
                            protocol_id: ProtocolId::from(1),
                            span: Span::ANY
                        }
                    }),
                },
                members: Members {
                    initializers: Default::default(),
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
            }
        );
    }

    #[test]
    fn registers_struct_members() {
        let struct_ty = ElaborationTy::Nominal {
            symbol: StructId::from(1).into(),
        };
        assert_eq_diff!(
            *elaborate(
                "
                protocol P {}
                struct A {
                  let prop: Int
                  static func getPropStatic() -> Int {
                    123
                  }
                  func getProp() {
                    self.prop
                  }
                  func getGeneric<T: P>(t: T) {
                    t
                  }
                }",
            )
            .nominals
            .get(&StructId::from(1).into())
            .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                span: Span::ANY,
                kind: NominalKind::Struct,
                conformances: vec![],
                child_types: Default::default(),
                members: Members {
                    initializers: indexmap::indexmap! {
                      Label::Named("init".into()) =>
                        (Symbol::Synthesized(1.into()), EnvEntry::Mono(
                            curry(vec![struct_ty.clone(), ElaborationTy::Int], struct_ty.clone())
                        ))
                    },
                    variants: Default::default(),
                    properties: indexmap::indexmap! {
                      Label::Named("prop".into()) =>
                        (Symbol::Property(1.into()), EnvEntry::Mono(
                            ElaborationTy::Int
                        ))
                    },
                    methods: indexmap::indexmap! {
                      Label::Named("getProp".into()) =>
                          (Symbol::InstanceMethod(1.into()), EnvEntry::Mono(
                              curry(vec![struct_ty.clone()], ElaborationTy::Hole(NodeID::ANY))
                          )),
                      Label::Named("getGeneric".into()) =>
                          (Symbol::InstanceMethod(2.into()), EnvEntry::Scheme(
                            Scheme {
                                ty: curry(vec![struct_ty.clone(), ElaborationTy::Param(2.into())], ElaborationTy::Hole(NodeID::ANY)),
                                foralls: indexset! { ForAll::Ty(2.into()) },
                                predicates: vec![Predicate::Conforms { param: 2.into(), protocol_id: 1.into(), span: Span::ANY }]
                            }
                          ))
                    },
                    static_methods: indexmap::indexmap! {
                      Label::Named("getPropStatic".into()) =>
                        (Symbol::StaticMethod(1.into()), EnvEntry::Mono(
                          ElaborationTy::Func(ElaborationTy::Void.into(), ElaborationTy::Int.into())
                        ))
                    },
                },
                ty: (Symbol::Struct(1.into()), EnvEntry::Mono(struct_ty.clone())),
            }
        );
    }

    #[test]
    fn registers_edges_for_global_func_calls() {
        let types = elaborate(
            "
            func a() { 123 }
            func b() { a() ; a() } // Twice to make sure we don't have dups
          ",
        );

        // b references a...
        assert_eq!(
            vec![Binder::Symbol(Symbol::Global(1.into()))],
            types
                .scc_graph
                .neighbors_for(&Binder::Symbol(Symbol::Global(2.into())))
        );

        // but a does not reference b
        assert!(
            types
                .scc_graph
                .neighbors_for(&Binder::Symbol(Symbol::Global(1.into())))
                .is_empty()
        );
    }

    #[test]
    fn registers_mutual_recursion_edges_for_global_func_calls() {
        let types = elaborate(
            "
            func a() { b() }
            func b() { a() }
          ",
        );

        assert_eq!(
            vec![Binder::Symbol(Symbol::Global(2.into()))],
            types
                .scc_graph
                .neighbors_for(&Binder::Symbol(Symbol::Global(1.into())))
        );

        assert_eq!(
            vec![Binder::Symbol(Symbol::Global(1.into()))],
            types
                .scc_graph
                .neighbors_for(&Binder::Symbol(Symbol::Global(2.into())))
        );
    }

    #[test]
    #[ignore = "we dont have builtin funcs yet"]
    fn graph_ignores_builtins() {
        // Calls to builtins (no DeclId) must not create edges.
        let types = elaborate(
            "
            func f(){ print(1) }
          ",
        );

        assert_eq!(types.scc_graph.graph.edge_count(), 0);
    }

    #[test]
    #[ignore = "for this to work we either need to make the `self` param's symbol track its parent type or track type context in the elaboration pass"]
    fn instance_methods_are_graphed() {
        let types = elaborate(
            r#"
        struct Person {
            func first()  { self.second() }
            func second() { self.first() }
        }
        "#,
        );

        assert_eq!(
            vec![Binder::Symbol(Symbol::InstanceMethod(1.into()))],
            types
                .scc_graph
                .neighbors_for(&Binder::Member(Symbol::Struct(1.into()), "second".into()))
        );

        assert_eq!(
            vec![Binder::Symbol(Symbol::InstanceMethod(2.into()))],
            types
                .scc_graph
                .neighbors_for(&Binder::Member(Symbol::Struct(1.into()), "first".into()))
        );
    }

    #[test]
    fn static_methods_are_graphed() {
        let types = elaborate(
            r#"
        struct Person {
            static func first()  { Person.second() }
            static func second() { Person.first() }
        }
        "#,
        );

        assert_eq!(
            vec![Binder::Member(Symbol::Struct(1.into()), "first".into())],
            types
                .scc_graph
                .neighbors_for(&Binder::Symbol(Symbol::StaticMethod(2.into())))
        );

        assert_eq!(
            vec![Binder::Member(Symbol::Struct(1.into()), "second".into())],
            types
                .scc_graph
                .neighbors_for(&Binder::Symbol(Symbol::StaticMethod(1.into())))
        );
    }
}
