use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::{instrument, trace_span};

use crate::{
    ast::AST,
    diagnostic::{AnyDiagnostic, Diagnostic},
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, SynthesizedId, TypeId},
    },
    node_kinds::{
        generic_decl::GenericDecl,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        builtins::resolve_builtin_type,
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        ty::Ty,
        type_error::TypeError,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeSession, TypingPhase},
    },
};

#[derive(Debug, PartialEq, Clone)]
pub struct HeadersResolved {
    pub type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    pub protocols: FxHashMap<TypeId, TypeDef<Ty>>,
}

impl TypingPhase for HeadersResolved {
    type Next = HeadersResolved;
}

#[derive(Debug)]
pub struct TypeHeaderResolvePass {
    session: TypeSession<Raw>,
    type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    protocols: FxHashMap<TypeId, TypeDef<Ty>>,
    generics_stack: Vec<IndexMap<Name, Ty>>,
    diagnostics: Vec<Diagnostic<TypeError>>,
}

impl TypeHeaderResolvePass {
    pub fn drive(
        session: TypeSession<Raw>,
        ast: &mut AST<NameResolved>,
    ) -> Result<TypeSession<HeadersResolved>, TypeError> {
        let resolver = TypeHeaderResolvePass {
            session,
            type_constructors: Default::default(),
            protocols: Default::default(),
            generics_stack: Default::default(),
            diagnostics: Default::default(),
        };

        resolver.solve(ast)
    }

    fn solve(
        mut self,
        ast: &mut AST<NameResolved>,
    ) -> Result<TypeSession<HeadersResolved>, TypeError> {
        for (decl_id, type_def) in self.session.phase.type_constructors.clone() {
            if let Ok(resolved) = self.resolve_type_def(&type_def) {
                self.type_constructors.insert(decl_id, resolved);
            }
        }

        ast.diagnostics
            .extend(self.diagnostics.into_iter().map(AnyDiagnostic::Typing));

        Ok(self.session.advance(HeadersResolved {
            type_constructors: self.type_constructors,
            protocols: self.protocols,
        }))
    }

    fn resolve_fields(&mut self, fields: &TypeFields<ASTTyRepr>) -> TypeFields<Ty> {
        let mut fields = match fields {
            TypeFields::Enum { variants, methods } => TypeFields::<Ty>::Enum {
                variants: self.resolve_variants(variants),
                methods: self.resolve_methods(methods),
            },
            TypeFields::Struct {
                initializers,
                methods,
                properties,
            } => TypeFields::<Ty>::Struct {
                initializers: self.resolve_initializers(initializers),
                methods: self.resolve_methods(methods),
                properties: self.resolve_properties(properties),
            },
            TypeFields::Protocol {
                initializers,
                methods,
                method_requirements,
                properties,
                associated_types,
            } => TypeFields::<Ty>::Protocol {
                initializers: self.resolve_initializers(initializers),
                methods: self.resolve_methods(methods),
                properties: self.resolve_properties(properties),
                method_requirements: self.resolve_method_requirements(method_requirements),
                associated_types: self.resolve_associated_types(associated_types),
            },
            TypeFields::Primitive => TypeFields::<Ty>::Primitive,
        };

        if let TypeFields::Struct {
            initializers,
            properties,
            ..
        } = &mut fields
            && initializers.is_empty()
        {
            // If we don't have an initializer, synthesize one.
            initializers.insert(
                Name::Resolved(
                    Symbol::Synthesized(SynthesizedId(self.session.synthsized_ids.next_id())),
                    "init".into(),
                ),
                Initializer {
                    params: properties
                        .values()
                        .filter_map(|p| {
                            if p.is_static {
                                None
                            } else {
                                Some(p.ty_repr.clone())
                            }
                        })
                        .collect(),
                },
            );
        }

        fields
    }

    fn resolve_type_def(
        &mut self,
        type_def: &TypeDef<ASTTyRepr>,
    ) -> Result<TypeDef<Ty>, TypeError> {
        let _s = trace_span!("resolve", type_def = format!("{type_def:?}")).entered();

        let mut generics = IndexMap::default();

        for (name, generic) in type_def.generics.iter() {
            if let Some(ty_repr) = self.resolve_ty_repr(generic) {
                generics.insert(name.clone(), ty_repr);
            }
        }

        self.generics_stack.push(generics);

        let fields = self.resolve_fields(&type_def.fields);

        generics = self.generics_stack.pop().unwrap();

        Ok(TypeDef {
            span: type_def.span,
            name: type_def.name.clone(),
            kind: type_def.kind.clone(),
            def: type_def.def,
            generics,
            fields,
        })
    }

    #[instrument]
    fn resolve_variants(
        &mut self,
        variants: &IndexMap<Name, Variant<ASTTyRepr>>,
    ) -> IndexMap<Name, Variant<Ty>> {
        let mut resolved_variants = IndexMap::default();
        for (name, variant) in variants {
            resolved_variants.insert(
                name.clone(),
                Variant {
                    fields: variant
                        .fields
                        .iter()
                        .filter_map(|f| self.resolve_ty_repr(f))
                        .collect(),
                },
            );
        }

        resolved_variants
    }

    #[instrument]
    fn resolve_methods(
        &mut self,
        methods: &IndexMap<Name, Method<ASTTyRepr>>,
    ) -> IndexMap<Name, Method<Ty>> {
        let mut resolved_methods = IndexMap::default();
        for (name, method) in methods {
            let Some(ret) = self.resolve_ty_repr(&method.ret) else {
                continue;
            };
            resolved_methods.insert(
                name.clone(),
                Method {
                    is_static: method.is_static,
                    params: method
                        .params
                        .iter()
                        .filter_map(|f| self.resolve_ty_repr(f))
                        .collect(),
                    ret,
                },
            );
        }

        resolved_methods
    }

    #[instrument]
    fn resolve_properties(
        &mut self,
        properties: &IndexMap<Label, Property<ASTTyRepr>>,
    ) -> IndexMap<Label, Property<Ty>> {
        let mut resolved_properties = IndexMap::default();
        for (name, prop) in properties {
            let Some(ty_repr) = self.resolve_ty_repr(&prop.ty_repr) else {
                continue;
            };
            resolved_properties.insert(
                name.clone(),
                Property {
                    is_static: prop.is_static,
                    ty_repr,
                },
            );
        }

        resolved_properties
    }

    #[instrument]
    fn resolve_initializers(
        &mut self,
        initializers: &IndexMap<Name, Initializer<ASTTyRepr>>,
    ) -> IndexMap<Name, Initializer<Ty>> {
        let mut resolved_initializers = IndexMap::default();
        for (name, initializer) in initializers {
            resolved_initializers.insert(
                name.clone(),
                Initializer {
                    params: initializer
                        .params
                        .iter()
                        .filter_map(|f| self.resolve_ty_repr(f))
                        .collect(),
                },
            );
        }

        resolved_initializers
    }

    #[instrument]
    fn resolve_associated_types(
        &mut self,
        associated_types: &IndexMap<Name, Associated>,
    ) -> IndexMap<Name, Associated> {
        let mut resolved_associated_types = IndexMap::default();
        for name in associated_types.keys() {
            resolved_associated_types.insert(name.clone(), Associated {});
        }

        resolved_associated_types
    }

    #[instrument]
    fn resolve_method_requirements(
        &mut self,
        requirements: &IndexMap<Name, MethodRequirement<ASTTyRepr>>,
    ) -> IndexMap<Name, MethodRequirement<Ty>> {
        let mut resolved_method_requirements = IndexMap::default();
        for (name, method_requirement) in requirements {
            let Some(ret) = self.resolve_ty_repr(&method_requirement.ret) else {
                continue;
            };

            resolved_method_requirements.insert(
                name.clone(),
                MethodRequirement {
                    params: method_requirement
                        .params
                        .iter()
                        .filter_map(|f| self.resolve_ty_repr(f))
                        .collect(),
                    ret,
                },
            );
        }

        resolved_method_requirements
    }

    #[instrument]
    fn resolve_ty_repr(&mut self, ty_repr: &ASTTyRepr) -> Option<Ty> {
        let res = match ty_repr {
            ASTTyRepr::Annotated(type_annotation) => self.resolve_type_annotation(type_annotation),
            ASTTyRepr::Hole(id, _) => Ok(Ty::Hole(*id)),
            ASTTyRepr::Generic(GenericDecl {
                name: Name::Resolved(Symbol::Type(decl_id), _),
                ..
            }) => Ok(Ty::Rigid(*decl_id)),
            _ => panic!("unresolved ty repr: {ty_repr:?}"),
        };

        match res {
            Ok(res) => Some(res),
            Err(e) => {
                self.diagnostics.push(Diagnostic {
                    path: self.session.path.clone(),
                    span: ty_repr.span(),
                    kind: e,
                });
                None
            }
        }
    }

    #[instrument]
    fn resolve_type_annotation(
        &mut self,
        type_annotation: &TypeAnnotation,
    ) -> Result<Ty, TypeError> {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal {
                name: name @ Name::Resolved(id, _),
                generics: generic_args,
            } => {
                if matches!(id, Symbol::BuiltinType(..)) {
                    if !generic_args.is_empty() {
                        return Err(TypeError::GenericArgCount {
                            expected: 0,
                            actual: generic_args.len() as u8,
                        });
                    }
                    return Ok(resolve_builtin_type(id));
                }

                match id {
                    Symbol::Type(id) => {
                        if let Some(type_def) = self.session.phase.type_constructors.get(id) {
                            if type_def.generics.len() != generic_args.len() {
                                return Err(TypeError::GenericArgCount {
                                    expected: type_def.generics.len() as u8,
                                    actual: generic_args.len() as u8,
                                });
                            }

                            let ty = generic_args.iter().fold(
                                Ty::TypeConstructor {
                                    name: name.clone(),
                                    kind: type_def.def,
                                },
                                |acc, arg| match self.resolve_type_annotation(arg) {
                                    Ok(arg) => Ty::TypeApplication(Box::new(acc), Box::new(arg)),
                                    Err(e) => {
                                        self.diagnostics.push(Diagnostic {
                                            path: self.session.path.clone(),
                                            span: arg.span,
                                            kind: e,
                                        });
                                        acc
                                    }
                                },
                            );

                            return Ok(ty);
                        };

                        if let Some(generics) = self.generics_stack.last()
                            && let Some(generic) = generics.get(name).cloned()
                        {
                            return Ok(generic);
                        }

                        Err(TypeError::TypeConstructorNotFound(*id))
                    }
                    _ => todo!(),
                }
            }
            TypeAnnotationKind::Tuple(_annotations) => {
                todo!()
            }
            _ => todo!(),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        assert_eq_diff,
        ast::AST,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{GlobalId, SynthesizedId},
        },
        types::{passes::type_header_decl_pass::TypeHeaderDeclPass, type_session::TypeDefKind},
    };

    use super::*;

    pub fn type_header_resolve_pass(code: &'static str) -> TypeSession<HeadersResolved> {
        let (ast, session) = type_header_resolve_pass_err(code).unwrap();
        assert!(
            ast.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            ast.diagnostics
        );
        session
    }

    pub fn type_header_resolve_pass_err(
        code: &'static str,
    ) -> Result<(AST<NameResolved>, TypeSession<HeadersResolved>), TypeError> {
        let mut resolved = resolve(code);
        let mut session = TypeSession::default();
        TypeHeaderDeclPass::drive(&mut session, &resolved);
        let res = TypeHeaderResolvePass::drive(session, &mut resolved)?;
        Ok((resolved, res))
    }

    #[test]
    fn synthesizes_init() {
        let session = type_header_resolve_pass(
            "
        struct Person {
            let age: Int
        }
        ",
        );

        assert_eq!(
            session
                .phase
                .type_constructors
                .get(&TypeId(1))
                .unwrap()
                .fields,
            TypeFields::Struct {
                initializers: crate::indexmap!(Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer { params: vec![Ty::Int] }),
                methods: Default::default(),
                properties: crate::indexmap!("age".into() => Property { is_static: false, ty_repr: Ty::Int }),
            }
        )
    }

    #[test]
    fn resolves_method() {
        let session = type_header_resolve_pass(
            "
        struct Person {
            func fizz(a: Int) -> Int { a }
        }
        ",
        );

        assert_eq!(
            session
                .phase
                .type_constructors
                .get(&TypeId(1))
                .unwrap()
                .fields,
            TypeFields::Struct {
                initializers: crate::indexmap!(Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer { params: vec![] }),
                methods: crate::indexmap!(Name::Resolved(Symbol::Global(GlobalId(1)), "fizz".into()) => Method { is_static: false, params: vec![Ty::Int], ret: Ty::Int }),
                properties: Default::default(),
            }
        )
    }

    #[test]
    fn resolves_out_of_order() {
        let session = type_header_resolve_pass(
            "
        struct A {
            let b: B
        }

        struct B {
            let a: A
        }
        ",
        );

        let a = Ty::TypeConstructor {
            kind: TypeDefKind::Struct,
            name: Name::Resolved(Symbol::Type(TypeId(1)), "A".into()),
        };

        let b = Ty::TypeConstructor {
            kind: TypeDefKind::Struct,
            name: Name::Resolved(Symbol::Type(TypeId(2)), "B".into()),
        };

        assert_eq!(
            session
                .phase
                .type_constructors
                .get(&TypeId(1))
                .unwrap()
                .fields,
            TypeFields::Struct {
                initializers: crate::indexmap!(
                Name::Resolved(
                    Symbol::Synthesized(SynthesizedId(2)), "init".into()) => Initializer { params: vec![b.clone()] }
                ),
                methods: Default::default(),
                properties: crate::indexmap!(
                    "b".into() => Property { is_static: false, ty_repr: b }
                ),
            }
        );

        assert_eq!(
            session
                .phase
                .type_constructors
                .get(&TypeId(2))
                .unwrap()
                .fields,
            TypeFields::Struct {
                initializers: crate::indexmap!(
                Name::Resolved(
                    Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer { params: vec![a.clone()] }
                ),
                methods: Default::default(),
                properties: crate::indexmap!(
                    "a".into() => Property { is_static: false, ty_repr: a }
                ),
            }
        );
    }

    #[test]
    fn resolves_type_params() {
        let session = type_header_resolve_pass(
            "
        struct Fizz<T> {
            let t: T
        }",
        );

        let type_def = session.phase.type_constructors.get(&TypeId(1)).unwrap();

        assert_eq!(
            type_def.generics,
            crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(2)), "T".into()) => Ty::Rigid(TypeId(2)))
        );
        let TypeFields::Struct { properties, .. } = &type_def.fields else {
            panic!("didn't get fields");
        };

        assert_eq!(
            *properties,
            crate::indexmap!(
                "t".into() => Property::<Ty> { is_static: false, ty_repr: Ty::Rigid(TypeId(2)) }
            )
        );
    }

    #[test]
    fn lowers_type_application() {
        let session = type_header_resolve_pass(
            "
            struct A<T, U> {} 
            struct B {
                let a: A<Int, Float>
            }
            ",
        );

        let type_application = Ty::TypeApplication(
            Box::new(Ty::TypeApplication(
                Box::new(Ty::TypeConstructor {
                    name: Name::Resolved(Symbol::Type(TypeId(1)), "A".into()),
                    kind: TypeDefKind::Struct,
                }),
                Box::new(Ty::Int),
            )),
            Box::new(Ty::Float),
        );

        assert_eq_diff!(
            session
                .phase
                .type_constructors
                .get(&TypeId(4))
                .unwrap()
                .fields,
            TypeFields::<Ty>::Struct {
                initializers: crate::indexmap!(
                    Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer {
                        params: vec![
                            type_application.clone()
                        ]
                }
                ),
                methods: Default::default(),
                properties: crate::indexmap!(
                    "a".into() => Property {
                        is_static: false,
                        ty_repr: type_application.clone()
                    }
                )
            }
        );
    }

    #[test]
    fn lowers_nested_type_application() {
        let session = type_header_resolve_pass(
            "
            struct A<T> {} 
            struct B<T> {} 
            struct C {
                let b: B<A<Int>>
            }
            ",
        );

        let type_application = Ty::TypeApplication(
            Box::new(Ty::TypeConstructor {
                name: Name::Resolved(Symbol::Type(TypeId(3)), "B".into()),
                kind: TypeDefKind::Struct,
            }),
            Box::new(Ty::TypeApplication(
                Box::new(Ty::TypeConstructor {
                    name: Name::Resolved(Symbol::Type(TypeId(1)), "A".into()),
                    kind: TypeDefKind::Struct,
                }),
                Box::new(Ty::Int),
            )),
        );

        assert_eq_diff!(
            session
                .phase
                .type_constructors
                .get(&TypeId(5))
                .unwrap()
                .fields,
            TypeFields::<Ty>::Struct {
                initializers: crate::indexmap!(
                    Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer {
                        params: vec![
                            type_application.clone()
                        ]
                }
                ),
                methods: Default::default(),
                properties: crate::indexmap!(
                    "b".into() => Property {
                        is_static: false,
                        ty_repr: type_application.clone()
                    }
                )
            }
        );
    }

    #[test]
    fn lowers_type_application_and_checks_arity() {
        let (ast, _session) = type_header_resolve_pass_err(
            r#"
        struct W<T> {}
        struct Bad { let x: W<Int, Int> } // too many args
         "#,
        )
        .unwrap();

        assert_eq!(ast.diagnostics.len(), 1);
    }
}
