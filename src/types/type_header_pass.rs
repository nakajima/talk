use crate::{
    name::Name,
    name_resolution::symbol::Symbol,
    node::Node,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        func::Func,
        func_signature::FuncSignature,
    },
    types::{
        kind::Kind,
        type_session::{TyRepr, TypeDef, TypeDefKind, TypeField, TypeFieldKind, TypeSession},
    },
};
use derive_visitor::Visitor;

#[derive(Debug, Visitor)]
#[visitor(Decl(enter))]
pub struct TypeHeaderPass<'a> {
    session: &'a mut TypeSession,
}

// Helper for n-ary arrows when all args are the same:
fn arrow_n(arg: Kind, n: usize, ret: Kind) -> Kind {
    (0..n).fold(ret, |acc, _| Kind::Arrow {
        in_kind: Box::new(arg.clone()),
        out_kind: Box::new(acc),
    })
}

impl<'a> TypeHeaderPass<'a> {
    fn enter_decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Struct {
                name: name @ Name::Resolved(Symbol::Type(decl_id), _),
                generics,
                body: Block { body, .. },
                ..
            } => {
                let fields = self.collect_fields(body);
                self.session.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        name: name.clone(),
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Struct,
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
                let fields = self.collect_fields(body);
                self.session.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        name: name.clone(),
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Protocol,
                        fields,
                    },
                );
            }
            DeclKind::Enum {
                name: name @ Name::Resolved(Symbol::Type(decl_id), _),
                body: Block { body, .. },
                ..
            } => {
                let fields = self.collect_fields(body);

                self.session.type_constructors.insert(
                    *decl_id,
                    TypeDef {
                        name: name.clone(),
                        kind: Kind::Type,
                        def: TypeDefKind::Enum,
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

    fn collect_fields(&self, body: &[Node]) -> Vec<TypeField> {
        // Collect properties
        let mut fields = vec![];
        for node in body {
            let Node::Decl(Decl {
                id: decl_id, kind, ..
            }) = node
            else {
                continue;
            };

            let (name, kind) = match &kind {
                DeclKind::Property {
                    name,
                    is_static,
                    type_annotation,
                    ..
                } => {
                    let ty_repr = if let Some(type_annotation) = type_annotation {
                        TyRepr::Annotated(type_annotation.clone())
                    } else {
                        TyRepr::Hole(*decl_id)
                    };

                    (
                        name,
                        TypeFieldKind::Property {
                            is_static: *is_static,
                            ty_repr,
                        },
                    )
                }
                DeclKind::EnumVariant(variant_name, values) => (
                    variant_name,
                    TypeFieldKind::Variant {
                        fields: values
                            .iter()
                            .map(|type_annotation| TyRepr::Annotated(type_annotation.clone()))
                            .collect(),
                    },
                ),
                DeclKind::Associated { generic } => (&generic.name, TypeFieldKind::Associated),
                DeclKind::Method {
                    func:
                        box Func {
                            name, params, ret, ..
                        },
                    is_static,
                    ..
                } => (
                    name,
                    TypeFieldKind::Method {
                        is_static: *is_static,
                        params: params
                            .iter()
                            .map(|p| {
                                if let Some(type_annotation) = &p.type_annotation {
                                    TyRepr::Annotated(type_annotation.clone())
                                } else {
                                    TyRepr::Hole(p.id)
                                }
                            })
                            .collect(),
                        ret: ret
                            .as_ref()
                            .map(|m| TyRepr::Annotated(m.clone()))
                            .unwrap_or(TyRepr::Hole(*decl_id)),
                    },
                ),
                DeclKind::MethodRequirement(FuncSignature {
                    name, params, ret, ..
                }) => (
                    name,
                    TypeFieldKind::MethodRequirement {
                        params: params
                            .iter()
                            .map(|p| {
                                if let Some(type_annotation) = &p.type_annotation {
                                    TyRepr::Annotated(type_annotation.clone())
                                } else {
                                    TyRepr::Hole(p.id)
                                }
                            })
                            .collect(),
                        ret: TyRepr::Annotated(*ret.clone()),
                    },
                ),
                _ => continue,
            };

            fields.push(TypeField {
                name: name.clone(),
                kind,
            });
        }

        fields
    }
}

#[cfg(test)]
pub mod tests {
    use derive_visitor::Drive;

    use crate::{
        annotation, assert_eq_diff,
        name::Name,
        name_resolution::{
            name_resolver_tests::tests::resolve,
            symbol::{BuiltinId, DeclId, Symbol},
        },
        node_id::NodeID,
        node_kinds::type_annotation::*,
        types::{
            kind::Kind,
            type_header_pass::TypeHeaderPass,
            type_session::{TyRepr, TypeDef, TypeDefKind, TypeField, TypeFieldKind, TypeSession},
        },
    };

    pub fn pass(code: &'static str) -> TypeSession {
        let mut session = TypeSession::default();
        let mut pass = TypeHeaderPass {
            session: &mut session,
        };

        let resolved = resolve(code);
        for root in resolved.roots.iter() {
            root.drive(&mut pass);
        }

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
            *session.type_constructors.get(&DeclId(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Type(DeclId(1)), "Person".into()),
                kind: Kind::Type,
                def: TypeDefKind::Struct,
                fields: vec![TypeField {
                    kind: TypeFieldKind::Property {
                        is_static: false,
                        ty_repr: TyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::BuiltinType(BuiltinId(1)), "Int".into()),
                            generics: vec![]
                        }))
                    },
                    name: Name::Resolved(Symbol::Value(DeclId(2)), "age".into()),
                }]
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
            *session.type_constructors.get(&DeclId(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Type(DeclId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Box::new(Kind::Type)
                },
                def: TypeDefKind::Struct,
                fields: vec![TypeField {
                    name: Name::Resolved(Symbol::Value(DeclId(3)), "wrapped".into()),
                    kind: TypeFieldKind::Property {
                        is_static: false,
                        ty_repr: TyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Type(DeclId(2)), "T".into()),
                            generics: vec![]
                        }))
                    },
                }]
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
            *session.type_constructors.get(&DeclId(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Type(DeclId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Kind::Arrow {
                        in_kind: Kind::Type.into(),
                        out_kind: Kind::Type.into(),
                    }
                    .into()
                },
                def: TypeDefKind::Struct,
                fields: vec![TypeField {
                    name: Name::Resolved(Symbol::Value(DeclId(4)), "wrapped".into()),
                    kind: TypeFieldKind::Property {
                        is_static: false,
                        ty_repr: TyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Type(DeclId(2)), "T".into()),
                            generics: vec![annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::Type(DeclId(3)), "U".into()),
                                generics: vec![]
                            })]
                        }))
                    },
                }]
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
            *session.type_constructors.get(&DeclId(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Type(DeclId(1)), "Fizz".into()),
                kind: Kind::Type,
                def: TypeDefKind::Enum,
                fields: vec![
                    TypeField {
                        name: Name::Resolved(Symbol::Type(DeclId(2)), "foo".into()),
                        kind: TypeFieldKind::Variant {
                            fields: vec![TyRepr::Annotated(annotation!(
                                TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(Symbol::Int, "Int".into()),
                                    generics: vec![]
                                }
                            ))]
                        }
                    },
                    TypeField {
                        name: Name::Resolved(Symbol::Type(DeclId(3)), "bar".into()),
                        kind: TypeFieldKind::Variant { fields: vec![] }
                    }
                ]
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
            *session.type_constructors.get(&DeclId(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Type(DeclId(1)), "Fizz".into()),
                kind: Kind::Type,
                def: TypeDefKind::Protocol,
                fields: vec![
                    TypeField {
                        name: Name::Resolved(Symbol::Type(DeclId(2)), "Buzz".into()),
                        kind: TypeFieldKind::Associated,
                    },
                    TypeField {
                        name: Name::Resolved(Symbol::Type(DeclId(3)), "foo".into()),
                        kind: TypeFieldKind::MethodRequirement {
                            params: vec![],
                            ret: TyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::Int, "Int".into()),
                                generics: vec![]
                            }))
                        },
                    }
                ]
            }
        );
    }
}
