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

pub trait ElaborationPhase {
    type T;
    type Generic;
}

pub struct RegisteredNames {}
impl ElaborationPhase for RegisteredNames {
    type T = ();
    type Generic = GenericDecl;
}

pub struct RegisteredMembers {}
impl ElaborationPhase for RegisteredMembers {
    type T = InferTy;
    type Generic = (TypeParamId, Vec<(ProtocolId, Span)>);
}

pub struct RegisteredBodies {}
impl ElaborationPhase for RegisteredBodies {
    type T = EnvEntry;
    type Generic = EnvEntry;
}

pub struct ElaboratedTypes<Phase: ElaborationPhase = RegisteredNames> {
    pub nominals: FxHashMap<Symbol, Nominal<Phase::Generic, Phase::T>>,
    pub protocols: FxHashMap<Symbol, Protocol>,
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
pub struct Nominal<Generic, T> {
    name: Name,
    ty: T,
    node_id: NodeID,
    kind: NominalKind,
    generics: Vec<Generic>,
    conformances: Vec<ConformanceStub>,
    child_types: Vec<Symbol>,
    members: Members<T>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Protocol {
    name: Name,
    node_id: NodeID,
    conformances: Vec<ConformanceStub>,
    child_types: Vec<Symbol>,
}

pub struct ElaborationPass<'a> {
    session: &'a mut TypeSession,
    canonical_row_vars: FxHashMap<Symbol, RowMetaId>,
    canonical_type_params: FxHashMap<Symbol, TypeParamId>,
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
            match node {
                Node::Decl(Decl {
                    id,
                    kind:
                        kind @ (DeclKind::Struct {
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
                        }),
                    ..
                }) => {
                    let kind = match kind {
                        DeclKind::Struct { .. } => NominalKind::Struct,
                        DeclKind::Enum { .. } => NominalKind::Enum,
                        _ => unreachable!(),
                    };

                    for generic in generics {
                        let InferTy::Param(id) = self.session.new_type_param(None) else {
                            unreachable!();
                        };

                        self.canonical_type_params.insert(generic.name.symbol(), id);
                    }

                    let mut nominal = Nominal {
                        ty: (),
                        members: Default::default(),
                        name: name.clone(),
                        node_id: *id,
                        kind,
                        generics: generics.clone(),
                        conformances: Self::collect_conformance_stubs(name.symbol(), conformances),
                        child_types: vec![],
                    };

                    let InferRow::Var(id) = self.session.new_row_meta_var(Level(1)) else {
                        unreachable!();
                    };
                    self.canonical_row_vars.insert(name.symbol(), id);

                    child_types.push(name.symbol());
                    types =
                        self.register_type_names(types, body.body.iter(), &mut nominal.child_types);
                    types.nominals.insert(name.symbol(), nominal);
                }
                Node::Decl(Decl {
                    id,
                    kind:
                        DeclKind::Protocol {
                            name,
                            conformances,
                            body,
                            ..
                        },
                    ..
                }) => {
                    let mut protocol = Protocol {
                        name: name.clone(),
                        node_id: *id,
                        conformances: Self::collect_conformance_stubs(name.symbol(), conformances),
                        child_types: vec![],
                    };

                    child_types.push(name.symbol());
                    types = self.register_type_names(
                        types,
                        body.body.iter(),
                        &mut protocol.child_types,
                    );
                    types.protocols.insert(name.symbol(), protocol);
                }
                _ => (),
            }
        }

        types
    }

    fn elaborate_members(
        &mut self,
        types: ElaboratedTypes<RegisteredNames>,
        nodes: impl Iterator<Item = &'a Node>,
    ) -> ElaboratedTypes<RegisteredMembers> {
        let mut new_types = ElaboratedTypes::<RegisteredMembers>::default();
        for node in nodes {
            match &node {
                Node::Decl(Decl {
                    kind: DeclKind::Struct { name, body, .. } | DeclKind::Enum { name, body, .. },
                    ..
                }) => {
                    let Nominal {
                        name,
                        node_id,
                        kind,
                        generics,
                        conformances,
                        child_types,
                        ty: _,
                        members: _,
                    } = types.nominals.get(&name.symbol()).cloned().unwrap();

                    let members = self.collect_members(name.symbol(), &body.body);
                    let symbol = name.symbol();
                    new_types.nominals.insert(
                        symbol,
                        Nominal {
                            members,
                            generics: generics
                                .into_iter()
                                .map(|generic| {
                                    let id = self
                                        .canonical_type_params
                                        .get(&generic.name.symbol())
                                        .unwrap();

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
                                })
                                .collect(),
                            name,
                            node_id,
                            kind,
                            conformances,
                            child_types,
                            ty: self.symbol_to_infer_ty(symbol),
                        },
                    );
                }
                Node::Decl(Decl {
                    kind: DeclKind::Protocol { name, .. },
                    ..
                }) => {
                    let Protocol {
                        name,
                        node_id,
                        conformances,
                        child_types,
                    } = types.protocols.get(&name.symbol()).cloned().unwrap();
                    new_types.protocols.insert(
                        name.symbol(),
                        Protocol {
                            name,
                            node_id,
                            conformances,
                            child_types,
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
            match &node {
                Node::Decl(Decl {
                    kind: DeclKind::Struct { name, .. } | DeclKind::Enum { name, .. },
                    ..
                }) => {
                    let Nominal {
                        name,
                        node_id,
                        kind,
                        generics,
                        conformances,
                        child_types,
                        members: member_stubs,
                        ty: _,
                    } = types.nominals.get(&name.symbol()).cloned().unwrap();

                    let mut foralls = IndexSet::default();
                    let mut predicates = vec![];
                    let mut generic_ids = vec![];
                    for (generic_id, bounds) in generics {
                        generic_ids.push(EnvEntry::Mono(InferTy::Param(generic_id)));
                        foralls.insert(ForAll::Ty(generic_id));
                        for (protocol_id, span) in bounds {
                            predicates.push(Predicate::Conforms {
                                param: generic_id,
                                protocol_id,
                                span: span,
                            })
                        }
                    }

                    let ty = self.symbol_to_infer_ty(name.symbol());
                    let ty = if foralls.is_empty() && predicates.is_empty() {
                        EnvEntry::Mono(ty)
                    } else {
                        EnvEntry::Scheme(Scheme {
                            foralls,
                            predicates,
                            ty,
                        })
                    };

                    let members = Members {
                        initializers: self.upgrade_members_to_entries(member_stubs.initializers),
                        variants: self.upgrade_members_to_entries(member_stubs.variants),
                        properties: self.upgrade_members_to_entries(member_stubs.properties),
                        methods: self.upgrade_members_to_entries(member_stubs.methods),
                        static_methods: self
                            .upgrade_members_to_entries(member_stubs.static_methods),
                    };

                    new_types.nominals.insert(
                        name.symbol(),
                        Nominal {
                            ty,
                            members,
                            generics: generic_ids,
                            name,
                            node_id,
                            kind,
                            conformances,
                            child_types,
                        },
                    );
                }
                Node::Decl(Decl {
                    kind: DeclKind::Protocol { name, .. },
                    ..
                }) => {
                    let Protocol {
                        name,
                        node_id,
                        conformances,
                        child_types,
                    } = types.protocols.get(&name.symbol()).cloned().unwrap();
                    new_types.protocols.insert(
                        name.symbol(),
                        Protocol {
                            name,
                            node_id,
                            conformances,
                            child_types,
                        },
                    );
                }
                _ => (),
            }
        }

        new_types
    }

    // Helpers

    fn upgrade_members_to_entries(
        &mut self,
        infer_members: IndexMap<Label, InferTy>,
    ) -> IndexMap<Label, EnvEntry> {
        infer_members
            .into_iter()
            .map(|(label, ty)| {
                let foralls = ty.collect_foralls();
                if foralls.is_empty() {
                    (label, EnvEntry::Mono(ty))
                } else {
                    (
                        label,
                        EnvEntry::Scheme(Scheme {
                            ty,
                            foralls: foralls.into_iter().collect(),
                            predicates: vec![],
                        }),
                    )
                }
            })
            .collect()
    }

    fn collect_members(&mut self, self_symbol: Symbol, nodes: &[Node]) -> Members<InferTy> {
        let mut members = Members::default();

        for node in nodes {
            match node {
                Node::Decl(Decl {
                    kind: DeclKind::Init { params, .. },
                    ..
                }) => {
                    let self_ty = self.symbol_to_infer_ty(self_symbol);
                    members.initializers.insert(
                        Label::Named("init".into()),
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
                    );
                }
                Node::Decl(Decl {
                    kind: DeclKind::Method { func, is_static },
                    ..
                }) => {}
                Node::Decl(Decl {
                    kind: DeclKind::MethodRequirement(req),
                    ..
                }) => {}
                Node::Decl(Decl {
                    kind:
                        DeclKind::Property {
                            name,
                            name_span,
                            is_static,
                            type_annotation,
                            default_value,
                        },
                    ..
                }) => {}
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
            Symbol::TypeParameter(..) => {
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
            TypeAnnotationKind::SelfType(name) => self.symbol_to_infer_ty(name.symbol()),
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
    use super::*;
    use crate::{
        assert_eq_diff,
        compiling::{
            driver::{Driver, Source},
            module::ModuleId,
        },
        make_infer_row,
        name_resolution::symbol::{EnumId, ProtocolId, StructId},
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
            Nominal::<EnvEntry, EnvEntry> {
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
                    static_methods: Default::default()
                },
                generics: vec![],
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
        assert_eq!(
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
                    Label::Named("init".into()) =>
                        EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default()
                },
                generics: vec![EnvEntry::Mono(InferTy::Param(1.into()))],
                conformances: vec![],
                child_types: vec![],
                ty: EnvEntry::Mono(InferTy::Nominal {
                    symbol: StructId::from(1).into(),
                    row: Box::new(make_infer_row!(Struct, "b" => InferTy::Param(1.into()))),
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
                        EnvEntry::Scheme(Scheme {
                            ty: curry(
                                vec![
                                    struct_ty.clone(),
                                    InferTy::Param(1.into())
                                ],
                                struct_ty.clone()
                            ),
                            foralls: [ForAll::Ty(1.into())].into(),
                            predicates: vec![]
                        }
                    )},
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default()
                },
                generics: vec![EnvEntry::Mono(InferTy::Param(1.into()))],
                conformances: vec![],
                child_types: vec![],
                ty: EnvEntry::Scheme(Scheme {
                    foralls: [ForAll::Ty(1.into())].into(),
                    predicates: vec![Predicate::Conforms {
                        param: 1.into(),
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
                generics: vec![],
                members: Members {
                    initializers: indexmap::indexmap! {
                    Label::Named("init".into()) =>
                        EnvEntry::Mono(curry(vec![struct_ty.clone()], struct_ty.clone()))
                    },
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default()
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
            Nominal::<EnvEntry, EnvEntry> {
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
                    static_methods: Default::default()
                },
                generics: vec![],
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
            Nominal::<EnvEntry, EnvEntry> {
                name: Name::Resolved(EnumId::from(1).into(), "A".into()),
                node_id: NodeID(FileID(0), 2),
                kind: NominalKind::Enum,
                generics: vec![],
                members: Members {
                    initializers: Default::default(),
                    variants: Default::default(),
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default()
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
        assert_eq!(
            *elaborate("protocol A {}",)
                .protocols
                .get(&ProtocolId::from(1).into())
                .unwrap(),
            Protocol {
                name: Name::Resolved(ProtocolId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                conformances: vec![],
                child_types: vec![]
            }
        );
    }

    #[test]
    fn registers_struct_members() {
        let struct_ty = InferTy::Nominal {
            symbol: StructId::from(1).into(),
            row: InferRow::Var(RowMetaId(1)).into(),
        };
        assert_eq!(
            *elaborate(
                "struct A {
                let prop: Int
                func getProp() {
                    self.prop
                }
            }",
            )
            .nominals
            .get(&StructId::from(1).into())
            .unwrap(),
            Nominal {
                name: Name::Resolved(StructId::from(1).into(), "A".into()),
                node_id: NodeID::ANY,
                kind: NominalKind::Struct,
                generics: vec![],
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
                    properties: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default()
                },
                ty: EnvEntry::Mono(struct_ty),
            }
        );
    }
}
