use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node::Node,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        func::Func,
        func_signature::FuncSignature,
    },
    types::{
        arrow_n,
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        kind::Kind,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeSession},
    },
};
use derive_visitor::{Drive, Visitor};
use indexmap::IndexMap;

#[derive(Debug, Visitor)]
#[visitor(Decl(enter))]
pub struct TypeHeaderDeclPass<'a> {
    session: &'a mut TypeSession<Raw>,
}

impl<'a> TypeHeaderDeclPass<'a> {
    pub fn drive(session: &'a mut TypeSession<Raw>, ast: &AST<NameResolved>) {
        let mut instance = TypeHeaderDeclPass { session };
        for root in ast.roots.iter() {
            root.drive(&mut instance);
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
                let fields = self.collect_fields(TypeDefKind::Struct, body);
                self.session.phase.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        name: name.clone(),
                        span: decl.span,
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
            DeclKind::Protocol {
                name: name @ Name::Resolved(Symbol::Type(decl_id), _),
                generics,
                body: Block { body, .. },
                ..
            } => {
                let fields = self.collect_fields(TypeDefKind::Protocol, body);
                self.session.phase.protocols.insert(
                    *decl_id,
                    TypeDef {
                        name: name.clone(),
                        span: decl.span,
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
                let fields = self.collect_fields(TypeDefKind::Enum, body);

                self.session.phase.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        name: name.clone(),
                        span: decl.span,
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

    fn collect_fields(&self, type_kind: TypeDefKind, body: &[Node]) -> TypeFields<ASTTyRepr> {
        // Collect properties
        let mut properties: IndexMap<Label, Property<ASTTyRepr>> = Default::default();
        let mut methods: IndexMap<Name, Method<ASTTyRepr>> = Default::default();
        let mut initializers: IndexMap<Name, Initializer<ASTTyRepr>> = Default::default();
        let mut variants: IndexMap<Name, Variant<ASTTyRepr>> = Default::default();
        let mut associated_types: IndexMap<Name, Associated> = Default::default();
        let mut method_requirements: IndexMap<Name, MethodRequirement<ASTTyRepr>> =
            Default::default();

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
                    label: name,
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
                        name.clone(),
                        Property {
                            is_static: *is_static,
                            ty_repr,
                        },
                    );
                }
                DeclKind::EnumVariant(variant_name, values) => {
                    variants.insert(
                        variant_name.clone(),
                        Variant {
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
                    methods.insert(
                        name.clone(),
                        Method {
                            is_static: *is_static,
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
                            ret: ret
                                .as_ref()
                                .map(|m| ASTTyRepr::Annotated(m.clone()))
                                .unwrap_or(ASTTyRepr::Hole(*decl_id, *span)),
                        },
                    );
                }
                DeclKind::MethodRequirement(FuncSignature {
                    name, params, ret, ..
                }) => {
                    method_requirements.insert(
                        name.clone(),
                        MethodRequirement {
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
                        name.clone(),
                        Initializer {
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
                        },
                    );
                }
                _ => continue,
            };
        }

        match type_kind {
            TypeDefKind::Struct => TypeFields::Struct {
                initializers,
                methods,
                properties,
            },
            TypeDefKind::Enum => TypeFields::Enum { variants, methods },
            TypeDefKind::Protocol => TypeFields::Protocol {
                initializers,
                methods,
                properties,
                associated_types,
                method_requirements,
            },
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        annotation, assert_eq_diff,
        name::Name,
        name_resolution::{
            name_resolver_tests::tests::resolve,
            symbol::{BuiltinId, Symbol, TypeId},
        },
        node_id::NodeID,
        node_kinds::{generic_decl::GenericDecl, type_annotation::*},
        span::Span,
        types::{
            fields::{Associated, Initializer, MethodRequirement, Property, TypeFields, Variant},
            kind::Kind,
            type_header_decl_pass::TypeHeaderDeclPass,
            type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeSession},
        },
    };

    pub fn pass(code: &'static str) -> TypeSession<Raw> {
        let resolved = resolve(code);
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderDeclPass::drive(&mut session, &resolved);
        session
    }

    #[test]
    fn basic_struct() {
        let session = pass(
            "
        struct Person {
            let age: Int
        }
        ",
        );

        assert_eq!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                kind: Kind::Type,
                span: Span::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                fields: TypeFields::Struct {
                    initializers: Default::default(),
                    methods: Default::default(),
                    properties: crate::indexmap!(
                        "age".into() => Property {
                            is_static: false,
                            ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::BuiltinType(BuiltinId(1)), "Int".into()),
                                generics: vec![]
                            })),
                        }
                    )
                }
            }
        );
    }

    #[test]
    fn generic_struct() {
        let session = pass(
            "
        struct Wrapper<T> {
            let wrapped: T

            init(wrapped) {
                self.wrapped = wrapped
            }
        }
        ",
        );

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Box::new(Kind::Type)
                },
                span: Span::ANY,
                def: TypeDefKind::Struct,
                generics: crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(2)), "T".into()) => ASTTyRepr::Generic(GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Type(TypeId(2)), "T".into()),
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY,
                })),
                fields: TypeFields::Struct {
                    initializers: crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(5)), "init".into()) => Initializer {
                        params: vec![
                            ASTTyRepr::Hole(NodeID(4), Span::ANY)
                        ]
                    }),
                    methods: Default::default(),
                    properties: crate::indexmap!("wrapped".into() => Property {
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
        let session = pass(
            "
        struct Wrapper<T, U> {
            let wrapped: T<U>
        }
        ",
        );

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Kind::Arrow {
                        in_kind: Kind::Type.into(),
                        out_kind: Kind::Type.into(),
                    }
                    .into()
                },
                span: Span::ANY,
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
                    initializers: Default::default(),
                    methods: Default::default(),
                    properties: crate::indexmap!("wrapped".into() => Property {
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
        let session = pass(
            "
        enum Fizz {
            case foo(Int), bar
        }
        ",
        );

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Fizz".into()),
                kind: Kind::Type,
                span: Span::ANY,
                def: TypeDefKind::Enum,
                generics: Default::default(),
                fields: TypeFields::Enum {
                    variants: crate::indexmap!(
                        Name::Resolved(Symbol::Type(TypeId(2)), "foo".into()) => Variant {
                            fields: vec![ASTTyRepr::Annotated(annotation!(
                                TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(Symbol::Int, "Int".into()),
                                    generics: vec![]
                                }
                            ))]
                        },
                        Name::Resolved(Symbol::Type(TypeId(3)), "bar".into()) =>  Variant { fields: vec![] }
                    ),
                    methods: Default::default()
                }
            }
        );
    }

    #[test]
    fn basic_protocol() {
        let session = pass(
            "
        protocol Fizz {
            associated Buzz

            func foo() -> Int
        }
        ",
        );

        assert_eq_diff!(
            *session.phase.protocols.get(&TypeId(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Fizz".into()),
                kind: Kind::Type,
                span: Span::ANY,
                def: TypeDefKind::Protocol,
                generics: Default::default(),
                fields: TypeFields::Protocol {
                    initializers: Default::default(),
                    methods: Default::default(),
                    properties: Default::default(),
                    method_requirements: crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(3)), "foo".into()) => MethodRequirement {
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
