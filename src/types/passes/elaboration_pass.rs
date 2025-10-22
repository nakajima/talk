use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{ProtocolId, Symbol},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        decl::{Decl, DeclKind},
        generic_decl::GenericDecl,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    types::{
        infer_row::{InferRow, RowMetaId},
        infer_ty::{InferTy, Level, TypeParamId},
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        type_catalog::ConformanceStub,
        type_session::TypeSession,
    },
};

#[derive(Clone, PartialEq, Debug)]
struct Members<T> {
    pub initializers: IndexMap<Label, T>,
    pub variants: IndexMap<Label, T>,
    pub properties: IndexMap<Label, T>,
    pub methods: IndexMap<Label, T>,
    pub static_methods: IndexMap<Label, T>,
}

impl<T> Members<T> {
    fn map<U>(self, mut map: impl FnMut(T) -> U) -> Members<U> {
        Members {
            initializers: self
                .initializers
                .into_iter()
                .map(|(l, v)| (l, map(v)))
                .collect(),
            variants: self
                .variants
                .into_iter()
                .map(|(l, v)| (l, map(v)))
                .collect(),
            properties: self
                .properties
                .into_iter()
                .map(|(l, v)| (l, map(v)))
                .collect(),
            methods: self.methods.into_iter().map(|(l, v)| (l, map(v))).collect(),
            static_methods: self
                .static_methods
                .into_iter()
                .map(|(l, v)| (l, map(v)))
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
    type Associated;
}

#[derive(PartialEq, Clone, Debug)]
pub struct RegisteredNames {}
impl ElaborationPhase for RegisteredNames {
    type T = ();
    type Associated = ();
}

#[derive(PartialEq, Clone, Debug)]
pub struct RegisteredMembers {}
impl ElaborationPhase for RegisteredMembers {
    type T = (InferTy, IndexSet<ForAll>, IndexSet<Predicate<InferTy>>);
    type Associated = (TypeParamId, IndexSet<Predicate<InferTy>>);
}

#[derive(PartialEq, Clone, Debug)]
pub struct RegisteredBodies {}
impl ElaborationPhase for RegisteredBodies {
    type T = EnvEntry;
    type Associated = (TypeParamId, IndexSet<Predicate<InferTy>>);
}

pub struct ElaboratedTypes<Phase: ElaborationPhase = RegisteredNames> {
    pub nominals: FxHashMap<Symbol, Nominal<Phase::T>>,
    pub protocols: FxHashMap<Symbol, Protocol<Phase>>,
}

impl<T: ElaborationPhase> Default for ElaboratedTypes<T> {
    fn default() -> Self {
        ElaboratedTypes {
            nominals: Default::default(),
            protocols: Default::default(),
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
    name: Name,
    ty: T,
    node_id: NodeID,
    kind: NominalKind,
    conformances: Vec<ConformanceStub>,
    child_types: Vec<Symbol>,
    members: Members<T>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Protocol<Phase: ElaborationPhase> {
    name: Name,
    node_id: NodeID,
    self_id: TypeParamId,
    associated_types: IndexMap<Name, Phase::Associated>,
    method_requirements: IndexMap<Label, Phase::T>,
    conformances: Vec<ConformanceStub>,
    child_types: Vec<Symbol>,
    members: Members<Phase::T>,
}

impl Protocol<RegisteredMembers> {
    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut foralls = IndexSet::default();

        foralls.insert(ForAll::Ty(self.self_id));
        foralls.extend(
            self.associated_types
                .values()
                .map(|(id, _)| ForAll::Ty(*id)),
        );

        foralls
    }
}

impl Protocol<RegisteredBodies> {
    pub fn collect_foralls(&self) -> IndexSet<ForAll> {
        let mut foralls = IndexSet::default();

        foralls.insert(ForAll::Ty(self.self_id));
        foralls.extend(
            self.associated_types
                .values()
                .map(|(id, _)| ForAll::Ty(*id)),
        );

        foralls
    }
}

pub struct ElaborationPass<'a> {
    session: &'a mut TypeSession,
    canonical_row_vars: FxHashMap<Symbol, RowMetaId>,
    canonical_type_params: FxHashMap<Symbol, TypeParamId>,
    type_param_conformances: IndexMap<TypeParamId, IndexSet<(ProtocolId, Span)>>,
}

impl<'a> ElaborationPass<'a> {
    pub fn drive(
        asts: &'a [AST<NameResolved>],
        session: &'a mut TypeSession,
    ) -> ElaboratedTypes<RegisteredBodies> {
        let mut pass = Self {
            session,
            canonical_row_vars: Default::default(),
            canonical_type_params: Default::default(),
            type_param_conformances: Default::default(),
        };

        let registered_names = pass.register_type_names(
            ElaboratedTypes::<RegisteredNames>::default(),
            asts.iter().flat_map(|a| &a.roots),
            &mut Default::default(),
        );

        let registered_members =
            pass.elaborate_members(registered_names, asts.iter().flat_map(|a| &a.roots));

        pass.elaborate_bodies(registered_members, asts.iter().flat_map(|a| &a.roots))
    }

    fn register_type_names(
        &mut self,
        mut types: ElaboratedTypes<RegisteredNames>,
        nodes: impl Iterator<Item = &'a Node>,
        child_types: &mut Vec<Symbol>,
    ) -> ElaboratedTypes<RegisteredNames> {
        for node in nodes {
            let Node::Decl(Decl { kind, .. }) = &node else {
                continue;
            };

            match kind {
                DeclKind::Associated { generic } => {
                    self.register_generic(generic);
                }
                DeclKind::Struct {
                    name,
                    generics,
                    conformances,
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
                    let kind = match kind {
                        DeclKind::Struct { .. } => NominalKind::Struct,
                        DeclKind::Enum { .. } => NominalKind::Enum,
                        _ => unreachable!(),
                    };

                    // Create TypeParamIds for explicit generic type parameters
                    for generic in generics {
                        self.register_generic(generic);
                    }

                    // Create the initial nominal that we'll pass through to future phases.
                    let mut nominal = Nominal {
                        ty: (),
                        members: Default::default(),
                        name: name.clone(),
                        node_id: node.node_id(),
                        kind,
                        conformances: Self::collect_conformance_stubs(name.symbol(), conformances),
                        child_types: vec![],
                    };

                    // Create a canonical row var since we don't know the properties/variants for this
                    // nominal yet
                    let id = self.session.new_row_meta_var_id(Level(1));
                    self.canonical_row_vars.insert(name.symbol(), id);

                    // Add this type to parent's children
                    child_types.push(name.symbol());

                    // Visit child types
                    types =
                        self.register_type_names(types, body.body.iter(), &mut nominal.child_types);

                    // Add it to the list
                    types.nominals.insert(name.symbol(), nominal);
                }
                DeclKind::Protocol {
                    name,
                    conformances,
                    body,
                    ..
                } => {
                    let id = self.session.new_type_param_id(None);
                    self.canonical_type_params.insert(name.symbol(), id);
                    let mut protocol = Protocol {
                        name: name.clone(),
                        node_id: node.node_id(),
                        conformances: Self::collect_conformance_stubs(name.symbol(), conformances),
                        method_requirements: Default::default(),
                        child_types: vec![],
                        members: Default::default(),
                        self_id: id,
                        associated_types: Default::default(),
                    };

                    // Add this type to parent's children
                    child_types.push(name.symbol());

                    // Visit child types
                    types = self.register_type_names(
                        types,
                        body.body.iter(),
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
    fn elaborate_members(
        &mut self,
        types: ElaboratedTypes<RegisteredNames>,
        nodes: impl Iterator<Item = &'a Node>,
    ) -> ElaboratedTypes<RegisteredMembers> {
        let mut new_types = ElaboratedTypes::<RegisteredMembers>::default();
        for node in nodes {
            let Node::Decl(Decl { kind, .. }) = &node else {
                continue;
            };

            match &kind {
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
                } => {
                    let nominal = types.nominals.get(&name.symbol()).cloned().unwrap();
                    let members = self.collect_members(name.symbol(), &body.body);
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
                                protocol_id: protocol_id,
                                span: conformance.span,
                            });
                        }
                    }

                    new_types.nominals.insert(
                        symbol,
                        Nominal {
                            members,
                            name: nominal.name,
                            node_id: nominal.node_id,
                            kind: nominal.kind,
                            conformances: nominal.conformances,
                            child_types: nominal.child_types,
                            ty: (self.symbol_to_infer_ty(symbol), foralls, predicates),
                        },
                    );
                }
                DeclKind::Protocol { name, body, .. } => {
                    let protocol = types.protocols.get(&name.symbol()).cloned().unwrap();
                    let members = self.collect_members(name.symbol(), &body.body);
                    let (associated_types, method_requirements) =
                        self.collect_protocol_members(&body.body);
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

    fn elaborate_bodies(
        &mut self,
        types: ElaboratedTypes<RegisteredMembers>,
        nodes: impl Iterator<Item = &'a Node>,
    ) -> ElaboratedTypes<RegisteredBodies> {
        let mut new_types = ElaboratedTypes::<RegisteredBodies>::default();
        for node in nodes {
            let Node::Decl(Decl { kind, .. }) = &node else {
                continue;
            };

            match &kind {
                DeclKind::Struct { name, generics, .. } | DeclKind::Enum { name, generics, .. } => {
                    let nominal = types.nominals.get(&name.symbol()).cloned().unwrap();
                    let mut foralls = IndexSet::default();
                    let mut predicates = vec![];
                    let mut generic_ids = vec![];
                    for generic in generics.iter() {
                        let (id, protocol_ids) = self.lookup_generic(generic.clone());
                        generic_ids.push(EnvEntry::Mono(InferTy::Param(id)));
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
                        .map(|m| self.upgrade_members_to_entries(m, &foralls));

                    new_types.nominals.insert(
                        name.symbol(),
                        Nominal {
                            ty,
                            members,
                            name: nominal.name,
                            node_id: nominal.node_id,
                            kind: nominal.kind,
                            conformances: nominal.conformances,
                            child_types: nominal.child_types,
                        },
                    );
                }
                DeclKind::Protocol { name, .. } => {
                    let protocol = types.protocols.get(&name.symbol()).cloned().unwrap();
                    let foralls = protocol.collect_foralls();
                    let members = protocol
                        .members
                        .map(|m| self.upgrade_members_to_entries(m, &foralls));
                    let method_requirements = protocol
                        .method_requirements
                        .into_iter()
                        .map(|(label, m)| (label, self.upgrade_members_to_entries(m, &foralls)))
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
    fn register_generic(&mut self, generic: &GenericDecl) -> TypeParamId {
        let id = self.session.new_type_param_id(None);
        self.canonical_type_params.insert(generic.name.symbol(), id);
        let mut conformances = IndexSet::default();
        for conformance in generic.conformances.iter() {
            conformances.insert((ProtocolId::from(conformance.symbol()), conformance.span));
        }
        self.type_param_conformances.insert(id, conformances);
        id
    }

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

    fn upgrade_members_to_entries(
        &mut self,
        ty: (InferTy, IndexSet<ForAll>, IndexSet<Predicate<InferTy>>),
        type_foralls: &IndexSet<ForAll>,
    ) -> EnvEntry {
        let (ty, foralls, predicates) = ty;
        let foralls: IndexSet<_> = foralls
            .into_iter()
            .filter(|p| !type_foralls.contains(p))
            .collect();

        if foralls.is_empty() && predicates.is_empty() {
            EnvEntry::Mono(ty)
        } else {
            EnvEntry::Scheme(Scheme {
                ty,
                foralls,
                predicates: predicates.into_iter().collect(),
            })
        }
    }

    fn collect_protocol_members(
        &mut self,
        nodes: &[Node],
    ) -> (
        IndexMap<Name, (TypeParamId, IndexSet<Predicate<InferTy>>)>,
        IndexMap<Label, (InferTy, IndexSet<ForAll>, IndexSet<Predicate<InferTy>>)>,
    ) {
        let mut associated_types =
            IndexMap::<Name, (TypeParamId, IndexSet<Predicate<InferTy>>)>::default();
        let mut method_requirements =
            IndexMap::<Label, (InferTy, IndexSet<ForAll>, IndexSet<Predicate<InferTy>>)>::default();

        for node in nodes {
            let Node::Decl(Decl { kind, .. }) = &node else {
                continue;
            };

            match kind {
                DeclKind::Associated { generic } => {
                    let (id, protocol_ids) = self.lookup_generic(generic.clone());
                    let predicates = protocol_ids
                        .into_iter()
                        .map(|(protocol_id, span)| Predicate::<InferTy>::Conforms {
                            param: id,
                            protocol_id: protocol_id,
                            span,
                        })
                        .collect();
                    associated_types.insert(generic.name.clone(), (id, predicates));
                }
                DeclKind::MethodRequirement(req) => {
                    let ret = if let Some(box ret) = req.ret.clone() {
                        self.infer_type_annotation(&ret.kind.clone())
                    } else {
                        InferTy::Void
                    };
                    let ty = curry_stub(
                        req.params.iter().map(|param| {
                            param
                                .type_annotation
                                .as_ref()
                                .map(|anno| self.infer_type_annotation(&anno.kind.clone()))
                                .unwrap_or_else(|| self.session.new_ty_meta_var(Level(1)))
                        }),
                        ret,
                    );

                    method_requirements.insert(
                        req.name.name_str().into(),
                        (ty, Default::default(), Default::default()),
                    );
                }
                _ => continue,
            }
        }

        (associated_types, method_requirements)
    }

    fn collect_members(
        &mut self,
        self_symbol: Symbol,
        nodes: &[Node],
    ) -> Members<(InferTy, IndexSet<ForAll>, IndexSet<Predicate<InferTy>>)> {
        let mut members = Members::default();

        for node in nodes {
            let Node::Decl(Decl { kind, .. }) = &node else {
                continue;
            };

            match kind {
                DeclKind::Init { params, .. } => {
                    let self_ty = self.symbol_to_infer_ty(self_symbol);
                    members.initializers.insert(
                        Label::Named("init".into()),
                        (
                            curry_stub(
                                params.iter().map(|param| {
                                    param
                                        .type_annotation
                                        .as_ref()
                                        .map(|anno| self.infer_type_annotation(&anno.kind.clone()))
                                        .unwrap_or_else(|| self.session.new_ty_meta_var(Level(1)))
                                }),
                                self_ty,
                            ),
                            Default::default(),
                            Default::default(),
                        ),
                    );
                }
                DeclKind::Method { func, is_static } => {
                    let mut foralls = IndexSet::default();
                    let mut predicates = IndexSet::default();
                    for generic in func.generics.iter() {
                        let id = self.register_generic(generic);
                        foralls.insert(ForAll::Ty(id));
                        for conformance in generic.conformances.iter() {
                            let protocol_id = ProtocolId::from(conformance.symbol());
                            predicates.insert(Predicate::Conforms {
                                param: id,
                                protocol_id: protocol_id,
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
                                .map(|anno| self.infer_type_annotation(&anno.kind.clone()))
                                .unwrap_or_else(|| self.session.new_ty_meta_var(Level(1)))
                        })
                        .collect::<Vec<_>>();

                    // If it's a static method, it won't have a self param so we need to prepend a Void so that curry works properly
                    if *is_static {
                        params.insert(0, InferTy::Void);
                    }

                    let ty = curry_stub(
                        params,
                        func.ret
                            .as_ref()
                            .map(|t| self.infer_type_annotation(&t.kind))
                            .unwrap_or_else(|| self.session.new_ty_meta_var(Level(1))),
                    );

                    let result = (ty, foralls, predicates);

                    if *is_static {
                        members
                            .static_methods
                            .insert(func.name.name_str().into(), result);
                    } else {
                        members.methods.insert(func.name.name_str().into(), result);
                    }
                }
                DeclKind::MethodRequirement(_req) => {}
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    default_value,
                    ..
                } => {
                    if *is_static {
                        todo!();
                    } else {
                        let ty = match (&type_annotation, &default_value) {
                            (None, None) => self.session.new_ty_meta_var(Level(1)),
                            (Some(anno), None) => self.infer_type_annotation(&anno.kind),
                            (None, Some(_val)) => todo!(),
                            (Some(anno), Some(_val)) => self.infer_type_annotation(&anno.kind),
                        };

                        members.properties.insert(
                            name.name_str().into(),
                            (ty, Default::default(), Default::default()),
                        );
                    }
                }
                _ => (),
            }
        }

        members
    }

    fn symbol_to_infer_ty(&self, symbol: Symbol) -> InferTy {
        match symbol {
            Symbol::Int => InferTy::Int,
            Symbol::Float => InferTy::Float,
            Symbol::Bool => InferTy::Bool,
            Symbol::Void => InferTy::Void,
            Symbol::TypeParameter(..) | Symbol::AssociatedType(..) => {
                let id = self.canonical_type_params.get(&symbol).unwrap_or_else(|| {
                    panic!(
                        "did not get canonical type param for symbol: {symbol:?} in {:?}",
                        self.canonical_type_params
                    )
                });

                InferTy::Param(*id)
            }
            _ => InferTy::Nominal {
                symbol,
                row: Box::new(InferRow::Var(
                    *self.canonical_row_vars.get(&symbol).unwrap_or_else(|| {
                        panic!("did not get canonical row var for symbol: {symbol:?}")
                    }),
                )),
            },
        }
    }

    fn infer_type_annotation(&self, kind: &TypeAnnotationKind) -> InferTy {
        match kind {
            TypeAnnotationKind::SelfType(name) => {
                let symbol = name.symbol();
                if matches!(symbol, Symbol::Protocol(..) | Symbol::AssociatedType(..)) {
                    InferTy::Param(
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
            TypeAnnotationKind::NominalPath { .. } => todo!(),
            _ => todo!(),
        }
    }

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
}

fn curry_stub<I: IntoIterator<Item = InferTy>>(params: I, ret: InferTy) -> InferTy {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| InferTy::Func(Box::new(p), Box::new(acc)))
}

#[cfg(test)]
pub mod tests {
    use indexmap::indexset;

    use super::*;
    use crate::{
        assert_eq_diff,
        compiling::{
            driver::{Driver, Source},
            module::ModuleId,
        },
        indexmap,
        name_resolution::symbol::{AssociatedTypeId, EnumId, ProtocolId, StructId},
        node_id::FileID,
        span::Span,
        types::{
            infer_row::{InferRow, RowMetaId},
            passes::inference_pass::curry,
        },
    };

    fn elaborate(code: &'static str) -> ElaboratedTypes<RegisteredBodies> {
        let driver = Driver::new_bare(vec![Source::from(code)], Default::default());
        let resolved = driver.parse().unwrap().resolve_names().unwrap();
        let mut session = TypeSession::new(ModuleId::Current, Default::default());
        let asts: Vec<_> = resolved.phase.asts.into_values().collect();
        ElaborationPass::drive(asts.as_slice(), &mut session)
    }

    #[test]
    fn registers_struct() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
        };

        assert_eq_diff!(
            *elaborate("struct A {}",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal::<EnvEntry> {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone()))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: vec![],
                ty: EnvEntry::Mono(struct_ty.clone()),
            }
        );
    }

    #[test]
    fn registers_generics() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
        };
        assert_eq_diff!(
            *elaborate("struct A<B> { let b: B }",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                      Label::Named("init".into()) => EnvEntry::Mono(curry(vec![struct_ty.clone(), InferTy::Param(1.into())], struct_ty.clone()))
                    },
                    variants: Default::default(),
                    properties: indexmap::indexmap! {
                      Label::Named("b".into()) =>
                          EnvEntry::Mono(InferTy::Param(1.into()))
                    },
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: vec![],
                ty: EnvEntry::Scheme(Scheme {
                    foralls: [ForAll::Ty(2.into())].into(),
                    predicates: vec![],
                    ty: InferTy::Nominal {
                        symbol: StructId::from(1).into(),
                        row: Box::new(InferRow::Var(1.into())),
                    }
                }),
            }
        );
    }

    #[test]
    fn registers_generic_conformances() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
        };
        assert_eq_diff!(
            *elaborate("protocol P {}; struct A<B: P> { let b: B }",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        EnvEntry::Mono(curry(vec![struct_ty.clone(), InferTy::Param(2.into())], struct_ty.clone()))
                    },
                    variants: Default::default(),
                    properties: indexmap::indexmap! {
                    Label::Named("b".into()) =>
                        EnvEntry::Mono(InferTy::Param(2.into()))
                    },
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: vec![],
                ty: EnvEntry::Scheme(Scheme {
                    foralls: [ForAll::Ty(3.into())].into(),
                    predicates: vec![Predicate::Conforms {
                        param: 3.into(),
                        protocol_id: ProtocolId::from(1),
                        span: Span::ANY
                    }],
                    ty: InferTy::Nominal {
                        symbol: StructId::from(1).into(),
                        row: Box::new(InferRow::Var(1.into())),
                    }
                }),
            }
        );
    }

    #[test]
    fn registers_struct_conformances() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
        };
        assert_eq!(
            *elaborate("protocol A {} ; protocol B {} ; struct C: A, B {}",)
                .nominals
                .get(&StructId::from(1).into())
                .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "C".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone()))
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
                child_types: vec![],
                ty: EnvEntry::Mono(struct_ty.clone()),
            }
        );
    }

    #[test]
    fn child_types() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
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
            Nominal::<EnvEntry> {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone()))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: vec![
                    StructId::from(2).into(),
                    EnumId::from(3).into(),
                    ProtocolId::from(1).into(),
                ],
                ty: EnvEntry::Mono(struct_ty.clone()),
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
            Nominal::<EnvEntry> {
                name: Name::Resolved(EnumId::from(1).into(), "A".into()),
                node_id: NodeID(FileID(0), 2),
                kind: NominalKind::Enum,
                members: Members {
                    initializers: Default::default(),
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                },
                conformances: vec![],
                child_types: vec![],
                ty: EnvEntry::Mono(InferTy::Nominal {
                    symbol: EnumId::from(1).into(),
                    row: Box::new(InferRow::Var(RowMetaId(1))),
                }),
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
            Protocol::<RegisteredBodies> {
                name: Name::Resolved(ProtocolId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                conformances: vec![],
                child_types: vec![],
                method_requirements: indexmap!("fizz".into() => EnvEntry::Mono(
                  InferTy::Func(
                    InferTy::Param(1.into()).into(),
                    InferTy::Int.into(),
                  )
                )),
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
              protocol A {}
              protocol B {
                associated C
                associated D: A

                func fizz() -> C
              }",
            )
            .protocols
            .get(&ProtocolId::from(2).into())
            .unwrap(),
            Protocol::<RegisteredBodies> {
                self_id: 2.into(),
                name: Name::Resolved(ProtocolId::from(2).into(), "B".into()),
                node_id: NodeID::ANY,
                conformances: vec![],
                method_requirements: indexmap!(
                  "fizz".into() => EnvEntry::Mono(
                    InferTy::Func(
                      InferTy::Param(2.into()).into(),
                      InferTy::Param(3.into()).into(),
                    )
                  )
                ),
                child_types: vec![],
                associated_types: indexmap::indexmap! {
                Name::Resolved(
                  Symbol::AssociatedType(AssociatedTypeId::from(1)), "C".into()) =>
                    (3.into(), indexset! {}),
                Name::Resolved(
                  Symbol::AssociatedType(AssociatedTypeId::from(2)), "D".into()) =>
                    (4.into(), indexset! {
                      Predicate::Conforms { param: 4.into(), protocol_id: ProtocolId::from(1), span: Span::ANY }
                    }),
                },
                members: Default::default(),
            }
        );
    }

    #[test]
    fn registers_struct_members() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
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
            Nominal::<EnvEntry> {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                conformances: vec![],
                child_types: vec![],
                members: Members {
                    initializers: indexmap::indexmap! {
                      Label::Named("init".into()) =>
                        EnvEntry::Mono(
                            curry(vec![struct_ty.clone(), InferTy::Int], struct_ty.clone())
                        )
                    },
                    variants: Default::default(),
                    properties: indexmap::indexmap! {
                      Label::Named("prop".into()) =>
                        EnvEntry::Mono(
                            InferTy::Int
                        )
                    },
                    methods: indexmap::indexmap! {
                      Label::Named("getProp".into()) =>
                          EnvEntry::Mono(
                              curry(vec![struct_ty.clone()], InferTy::UnificationVar { id: 1.into(), level: Level(1) })
                          ),
                      Label::Named("getGeneric".into()) =>
                          EnvEntry::Scheme(
                            Scheme {
                                ty: curry(vec![struct_ty.clone(), InferTy::Param(2.into())], InferTy::UnificationVar { id: 2.into(), level: Level(1) }),
                                foralls: indexset! { ForAll::Ty(2.into()) },
                                predicates: vec![Predicate::Conforms { param: 2.into(), protocol_id: 1.into(), span: Span::ANY }]
                            }
                          )
                    },
                    static_methods: indexmap::indexmap! {
                      Label::Named("getPropStatic".into()) =>
                        EnvEntry::Mono(
                          InferTy::Func(InferTy::Void.into(), InferTy::Int.into())
                        )
                    },
                },
                ty: EnvEntry::Mono(struct_ty.clone()),
            }
        );
    }
}
