use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, SynthesizedId, TypeId},
    },
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        func::Func,
        func_signature::FuncSignature,
        type_annotation::TypeAnnotationKind,
    },
    span::Span,
    types::{
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        kind::Kind,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeExtension, TypeSession},
    },
};
use derive_visitor::{Drive, Visitor};
use indexmap::IndexMap;
use rustc_hash::FxHashMap;

// Helper for n-ary arrows when all args are the same:
pub fn arrow_n(arg: Kind, n: usize, ret: Kind) -> Kind {
    (0..n).fold(ret, |acc, _| Kind::Arrow {
        in_kind: Box::new(arg.clone()),
        out_kind: Box::new(acc),
    })
}

#[derive(Debug, Visitor)]
#[visitor(Decl(enter))]
pub struct TypeHeaderPass<'a> {
    session: &'a mut TypeSession<Raw>,
    extensions: FxHashMap<TypeId, Vec<TypeExtension<ASTTyRepr>>>,
}

impl<'a> TypeHeaderPass<'a> {
    pub fn drive(session: &'a mut TypeSession<Raw>, ast: &AST<NameResolved>) {
        let mut instance = TypeHeaderPass {
            session,
            extensions: Default::default(),
        };

        for root in ast.roots.iter() {
            root.drive(&mut instance);
        }

        let mut extensions = std::mem::take(&mut instance.extensions);
        for (id, type_constructor) in instance.session.phase.type_constructors.iter_mut() {
            if let Some(extensions) = extensions.remove(id) {
                type_constructor.extensions = extensions
            }
        }
    }

    fn enter_decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Struct {
                name: name @ Name::Resolved(Symbol::Type(decl_id), _),
                generics,
                body: Block { body, .. },
                ..
            } => {
                let fields =
                    self.collect_fields(name, decl.id, decl.span, TypeDefKind::Struct, body);
                self.session.phase.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        extensions: Default::default(),
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Struct,
                        generics: generics
                            .iter()
                            .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                            .collect(),
                        fields,
                    },
                );
            }
            DeclKind::Extend {
                name: name @ Name::Resolved(Symbol::Type(type_id), _),
                body: Block { body, .. },
                conformances,
                ..
            } => {
                let TypeFields::Extension {
                    static_methods,
                    instance_methods: methods,
                } = self.collect_fields(name, decl.id, decl.span, TypeDefKind::Extension, body)
                else {
                    unreachable!()
                };

                let protocol_ids = conformances.iter().filter_map(|c| {
                    if let TypeAnnotationKind::Nominal {
                        name: Name::Resolved(Symbol::Type(type_id), _),
                        ..
                    } = &c.kind
                    {
                        Some(*type_id)
                    } else {
                        None
                    }
                });
                self.extensions
                    .entry(*type_id)
                    .or_default()
                    .push(TypeExtension {
                        node_id: decl.id,
                        conformances: protocol_ids.collect(),
                        methods,
                        static_methods,
                    });
            }
            DeclKind::Protocol {
                name: name @ Name::Resolved(Symbol::Type(decl_id), _),
                generics,
                body: Block { body, .. },
                ..
            } => {
                let fields =
                    self.collect_fields(name, decl.id, decl.span, TypeDefKind::Protocol, body);
                self.session.phase.protocols.insert(
                    *decl_id,
                    TypeDef {
                        extensions: Default::default(),
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Protocol,
                        generics: generics
                            .iter()
                            .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                            .collect(),
                        fields,
                    },
                );
            }
            DeclKind::Enum {
                name: name @ Name::Resolved(Symbol::Type(decl_id), _),
                body: Block { body, .. },
                generics,
                ..
            } => {
                let fields = self.collect_fields(name, decl.id, decl.span, TypeDefKind::Enum, body);

                self.session.phase.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        extensions: Default::default(),
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Enum,
                        generics: generics
                            .iter()
                            .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                            .collect(),
                        fields,
                    },
                );
            }
            _ => (),
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Helpers
    ///////////////////////////////////////////////////////////////////////////

    fn collect_fields(
        &mut self,
        type_name: &Name,
        id: NodeID,
        span: Span,
        type_kind: TypeDefKind,
        body: &[Node],
    ) -> TypeFields<ASTTyRepr> {
        // Collect properties
        let mut properties: IndexMap<Label, Property<ASTTyRepr>> = Default::default();
        let mut instance_methods: IndexMap<Label, Method<ASTTyRepr>> = Default::default();
        let mut static_methods: IndexMap<Label, Method<ASTTyRepr>> = Default::default();
        let mut initializers: IndexMap<Label, Initializer<ASTTyRepr>> = Default::default();
        let mut variants: IndexMap<Label, Variant<ASTTyRepr>> = Default::default();
        let mut associated_types: IndexMap<Name, Associated> = Default::default();
        let mut method_requirements: IndexMap<Label, MethodRequirement<ASTTyRepr>> =
            Default::default();

        let Name::Resolved(Symbol::Type(type_id), _) = &type_name else {
            unreachable!("didn't resolve type");
        };

        for node in body {
            let Node::Decl(Decl {
                id: decl_id,
                kind,
                span,
                ..
            }) = node
            else {
                continue;
            };

            match &kind {
                DeclKind::Property {
                    name: Name::Resolved(sym, name),
                    is_static,
                    type_annotation,
                    ..
                } => {
                    let ty_repr = if let Some(type_annotation) = type_annotation {
                        ASTTyRepr::Annotated(type_annotation.clone())
                    } else {
                        ASTTyRepr::Hole(*decl_id, *span)
                    };

                    properties.insert(
                        name.into(),
                        Property {
                            symbol: *sym,
                            is_static: *is_static,
                            ty_repr,
                        },
                    );
                }
                DeclKind::EnumVariant(variant_name, values) => {
                    variants.insert(
                        variant_name.name_str().into(),
                        Variant {
                            tag: variant_name.name_str().into(),
                            symbol: variant_name.symbol().expect("did not resolve variant name"),
                            fields: values
                                .iter()
                                .map(|type_annotation| {
                                    ASTTyRepr::Annotated(type_annotation.clone())
                                })
                                .collect(),
                        },
                    );
                }
                DeclKind::Associated { generic } => {
                    associated_types.insert(generic.name.clone(), Associated {});
                }
                DeclKind::Method {
                    func:
                        box Func {
                            name, params, ret, ..
                        },
                    is_static,
                    ..
                } => {
                    if *is_static {
                        static_methods.insert(
                            Label::Named(name.name_str()),
                            Method {
                                id,
                                span: *span,
                                symbol: name.symbol().unwrap(),
                                is_static: *is_static,
                                params: params
                                    .iter()
                                    .enumerate()
                                    .map(|(i, p)| {
                                        if i == 0 {
                                            ASTTyRepr::SelfType(type_name.clone(), p.id, *span)
                                        } else if let Some(type_annotation) = &p.type_annotation {
                                            ASTTyRepr::Annotated(type_annotation.clone())
                                        } else {
                                            ASTTyRepr::Hole(p.id, *span)
                                        }
                                    })
                                    .collect(),
                                ret: ret
                                    .as_ref()
                                    .map(|m| ASTTyRepr::Annotated(m.clone()))
                                    .unwrap_or(ASTTyRepr::Hole(*decl_id, *span)),
                            },
                        );
                    } else {
                        instance_methods.insert(
                            Label::Named(name.name_str()),
                            Method {
                                id,
                                span: *span,
                                symbol: name.symbol().unwrap(),
                                is_static: *is_static,
                                params: params
                                    .iter()
                                    .enumerate()
                                    .map(|(i, p)| {
                                        if i == 0 {
                                            ASTTyRepr::SelfType(type_name.clone(), p.id, *span)
                                        } else if let Some(type_annotation) = &p.type_annotation {
                                            ASTTyRepr::Annotated(type_annotation.clone())
                                        } else {
                                            ASTTyRepr::Hole(p.id, *span)
                                        }
                                    })
                                    .collect(),
                                ret: ret
                                    .as_ref()
                                    .map(|m| ASTTyRepr::Annotated(m.clone()))
                                    .unwrap_or(ASTTyRepr::Hole(*decl_id, *span)),
                            },
                        );
                    }
                }
                DeclKind::MethodRequirement(FuncSignature {
                    name: Name::Resolved(symbol, name),
                    params,
                    ret,
                    ..
                }) => {
                    method_requirements.insert(
                        name.into(),
                        MethodRequirement {
                            id,
                            symbol: *symbol,
                            params: params
                                .iter()
                                .map(|p| {
                                    if let Some(type_annotation) = &p.type_annotation {
                                        ASTTyRepr::Annotated(type_annotation.clone())
                                    } else {
                                        ASTTyRepr::Hole(p.id, *span)
                                    }
                                })
                                .collect(),
                            ret: ASTTyRepr::Annotated(*ret.clone()),
                        },
                    );
                }
                DeclKind::Init { name, params, .. } => {
                    initializers.insert(
                        name.name_str().into(),
                        Initializer {
                            symbol: name.symbol().unwrap(),
                            initializes_type_id: *type_id,
                            params: params
                                .iter()
                                .enumerate()
                                .map(|(i, p)| {
                                    if i == 0 {
                                        ASTTyRepr::SelfType(type_name.clone(), p.id, *span)
                                    } else if let Some(type_annotation) = &p.type_annotation {
                                        ASTTyRepr::Annotated(type_annotation.clone())
                                    } else {
                                        ASTTyRepr::Hole(p.id, *span)
                                    }
                                })
                                .collect(),
                        },
                    );
                }
                _ => continue,
            };
        }

        if type_kind == TypeDefKind::Struct && initializers.is_empty() {
            // If we don't have an initializer, synthesize one.
            let mut params: Vec<ASTTyRepr> = properties
                .values()
                .filter_map(|p| {
                    if p.is_static {
                        None
                    } else {
                        Some(p.ty_repr.clone())
                    }
                })
                .collect();

            // At this point, we've already prepend `self` to param lists so we need to do so here as well
            params.insert(0, ASTTyRepr::SelfType(type_name.clone(), id, span));

            let sym = Symbol::Synthesized(SynthesizedId(self.session.synthsized_ids.next_id()));

            initializers.insert(
                "init".into(),
                Initializer {
                    initializes_type_id: *type_id,
                    symbol: sym,
                    params,
                },
            );
        }

        match type_kind {
            TypeDefKind::Extension => TypeFields::Extension {
                instance_methods,
                static_methods,
            },
            TypeDefKind::Struct => TypeFields::Struct {
                initializers,
                instance_methods,
                static_methods,
                properties,
            },
            TypeDefKind::Enum => TypeFields::Enum {
                variants,
                instance_methods,
                static_methods,
            },
            TypeDefKind::Protocol => TypeFields::Protocol {
                instance_methods,
                static_methods,
                associated_types,
                method_requirements,
            },
        }
    }
}

#[cfg(test)]
pub mod tests {
    use indexmap::indexmap;

    use crate::{
        annotation, assert_eq_diff,
        ast::AST,
        label::Label,
        name::Name,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{
                BuiltinId, GlobalId, InstanceMethodId, PropertyId, Symbol, SynthesizedId, TypeId,
                VariantId,
            },
        },
        node_id::NodeID,
        node_kinds::{generic_decl::GenericDecl, type_annotation::*},
        span::Span,
        types::{
            fields::{Associated, Initializer, MethodRequirement, Property, TypeFields, Variant},
            kind::Kind,
            passes::type_headers_pass::TypeHeaderPass,
            type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeExtension, TypeSession},
        },
    };

    pub fn type_header_decl_pass(code: &'static str) -> (AST<NameResolved>, TypeSession<Raw>) {
        let resolved = resolve(code);
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderPass::drive(&mut session, &resolved);
        (resolved, session)
    }

    #[test]
    fn basic_struct() {
        let session = type_header_decl_pass(
            "
        struct Person {
            let age: Int
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: indexmap! {
                        Label::Named("init".into()) => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                                ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                                ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::Int, "Int".into()), generics: vec!{} }))
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    properties: crate::indexmap!(
                        "age".into() => Property {
                            symbol: Symbol::Property(PropertyId(1)),
                            is_static: false,
                            ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::Builtin(BuiltinId(1)), "Int".into()),
                                generics: vec![]
                            })),
                        }
                    )
                }
            }
        );
    }

    #[test]
    fn struct_extension() {
        let session = type_header_decl_pass(
            "
        struct Person {}
        extend Person {}
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                extensions: vec![TypeExtension::<ASTTyRepr> {
                    node_id: NodeID::ANY,
                    conformances: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                }],
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: indexmap! {
                        "init".into() => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                                ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    properties: Default::default()
                }
            }
        );
    }

    #[test]
    fn generic_struct() {
        let session = type_header_decl_pass(
            "
        struct Wrapper<T> {
            let wrapped: T

            init(wrapped) {
                self.wrapped = wrapped
            }
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Box::new(Kind::Type)
                },
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(2)), "T".into()) => ASTTyRepr::Generic(GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Type(TypeId(2)), "T".into()),
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY,
                })),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: crate::indexmap!("init".into() => Initializer {
                        symbol: Symbol::Global(GlobalId(1)),
                        initializes_type_id: TypeId(1),
                        params: vec![
                            ASTTyRepr::SelfType(Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()), NodeID::ANY, Span::ANY),
                            ASTTyRepr::Hole(NodeID(4), Span::ANY)
                        ]
                    }),
                    instance_methods: Default::default(),
                    properties: crate::indexmap!("wrapped".into() => Property {
                        symbol: Symbol::Property(PropertyId(1)),
                        is_static: false,
                        ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Type(TypeId(2)), "T".into()),
                            generics: vec![]
                        }))
                    })
                }
            }
        );
    }

    #[test]
    fn nested_generic_struct() {
        let session = type_header_decl_pass(
            "
        struct Wrapper<T, U> {
            let wrapped: T<U>
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Kind::Arrow {
                        in_kind: Kind::Type.into(),
                        out_kind: Kind::Type.into(),
                    }
                    .into()
                },
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: crate::indexmap!(
                  Name::Resolved(Symbol::Type(TypeId(2)), "T".into()) =>  ASTTyRepr::Generic(GenericDecl {
                        id: NodeID::ANY,
                        name: Name::Resolved(Symbol::Type(TypeId(2)), "T".into()),
                        generics: vec![],
                        conformances: vec![],
                        span: Span::ANY,
                    }),
                   Name::Resolved(Symbol::Type(TypeId(3)), "U".into()) => ASTTyRepr::Generic(GenericDecl {
                        id: NodeID::ANY,
                        name: Name::Resolved(Symbol::Type(TypeId(3)), "U".into()),
                        generics: vec![],
                        conformances: vec![],
                        span: Span::ANY,
                    })
                ),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: indexmap! {
                        "init".into() => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                            ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Wrapper".into()), NodeID::ANY, Span::ANY),
                            ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::Type(TypeId(2)), "T".into()), generics: vec![
                                annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(TypeId(3).into(), "U".into()), generics: vec![] })
                            ] }))
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    properties: crate::indexmap!("wrapped".into() => Property {
                        symbol: Symbol::Property(PropertyId(1)),
                        is_static: false,
                        ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Type(TypeId(2)), "T".into()),
                            generics: vec![annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::Type(TypeId(3)), "U".into()),
                                generics: vec![]
                            })]
                        }))
                    })
                }
            }
        );
    }

    #[test]
    fn basic_enum() {
        let session = type_header_decl_pass(
            "
        enum Fizz {
            case foo(Int), bar
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Fizz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Enum,
                generics: Default::default(),
                fields: TypeFields::Enum {
                    static_methods: Default::default(),
                    variants: crate::indexmap!(
                        "foo".into() => Variant {
                            symbol: Symbol::Variant(VariantId(1)),
                            tag: "foo".into(),
                            fields: vec![ASTTyRepr::Annotated(annotation!(
                                TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(Symbol::Int, "Int".into()),
                                    generics: vec![]
                                }
                            ))]
                        },
                        "bar".into() =>  Variant { symbol: Symbol::Variant(VariantId(2)), tag: "bar".into(), fields: vec![] }
                    ),
                    instance_methods: Default::default()
                }
            }
        );
    }

    #[test]
    fn basic_protocol() {
        let session = type_header_decl_pass(
            "
        protocol Fizz {
            associated Buzz

            func foo() -> Int
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.protocols.get(&TypeId(1)).unwrap(),
            TypeDef {
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Fizz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Protocol,
                generics: Default::default(),
                fields: TypeFields::Protocol {
                    instance_methods: Default::default(),
                    static_methods: Default::default(),
                    method_requirements: crate::indexmap!("foo".into() => MethodRequirement {
                        id: NodeID::ANY,
                        symbol: Symbol::InstanceMethod(InstanceMethodId(1)),
                        params: vec![],
                        ret: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Int, "Int".into()),
                            generics: vec![]
                        }))
                    }),
                    associated_types: crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(2)), "Buzz".into()) => Associated {})
                }
            }
        );
    }
}
