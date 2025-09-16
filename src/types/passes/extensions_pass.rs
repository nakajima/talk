use rustc_hash::FxHashMap;

use crate::{
    ast::AST,
    name_resolution::{name_resolver::NameResolved, symbol::TypeId},
    types::{
        passes::{dependencies_pass::SCCResolved, type_header_resolve_pass::HeadersResolved},
        type_session::{ASTTyRepr, Raw, TypeDef, TypeSession, TypingPhase},
    },
};

#[derive(Debug, Clone)]
pub struct ExtensionsResolved {
    pub type_constructors: FxHashMap<TypeId, TypeDef<ASTTyRepr>>,
    pub protocols: FxHashMap<TypeId, TypeDef<ASTTyRepr>>,
}

pub struct ExtensionResolverPass<'a> {
    ast: &'a mut AST<NameResolved>,
}

impl<'a> ExtensionResolverPass<'a> {
    pub fn drive(
        ast: &'a mut AST<NameResolved>,
        mut session: TypeSession<HeadersResolved>,
    ) -> TypeSession<ExtensionsResolved> {
        let type_constructors = std::mem::take(&mut session.phase.type_constructors);
        let protocols = std::mem::take(&mut session.phase.protocols);
        session.advance(ExtensionsResolved {
            type_constructors,
            protocols,
        })
    }
}

impl TypingPhase for ExtensionsResolved {
    type Next = SCCResolved;
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        annotation, assert_eq_diff,
        ast::AST,
        name::Name,
        name_resolution::{
            name_resolver::NameResolved,
            symbol::{GlobalId, Symbol, SynthesizedId, TypeId},
        },
        node_id::NodeID,
        node_kinds::type_annotation::TypeAnnotationKind,
        span::Span,
        types::{
            fields::{Initializer, Method, TypeFields},
            kind::Kind,
            passes::type_header_decl_pass::tests::type_header_decl_pass,
            type_session::{ASTTyRepr, TypeDef, TypeDefKind, TypeSession},
        },
    };
    use indexmap::indexmap;

    pub fn resolve_extensions(
        code: &'static str,
    ) -> (AST<NameResolved>, TypeSession<ExtensionsResolved>) {
        let (mut ast, session) = type_header_decl_pass(code);
        let session = ExtensionResolverPass::drive(&mut ast, session);
        (ast, session)
    }

    #[test]
    fn struct_extension() {
        let session = resolve_extensions(
            "
        struct Person {}
        extend Person {
            func foo() -> Int {}
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef::<ASTTyRepr> {
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                kind: Kind::Type,
                span: Span::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                fields: TypeFields::Struct {
                    initializers: indexmap! {
                        Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer { params: vec![
                            ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                        ]}
                    },
                    methods: crate::indexmap!("foo".into() => Method {
                        id: NodeID::ANY,
                        params: vec![
                            ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                        ],
                        is_static: false,
                        span: Span::ANY,
                        symbol: Symbol::Global(GlobalId(1)),
                        ret: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Int, "Int".into()),
                            generics: vec![]
                        }))
                    }),
                    properties: Default::default()
                }
            }
        );
    }
}
