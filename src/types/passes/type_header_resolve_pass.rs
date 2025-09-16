use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::{instrument, trace_span};

use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, TypeId},
    },
    node_kinds::type_annotation::{TypeAnnotation, TypeAnnotationKind},
    types::{
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        passes::dependencies_pass::SCCResolved,
        row::Row,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_error::TypeError,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeSession, TypingPhase},
        wants::Wants,
    },
};

#[derive(Debug, PartialEq, Clone)]
pub struct HeadersResolved {
    pub type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    pub protocols: FxHashMap<TypeId, TypeDef<Ty>>,
}

impl TypingPhase for HeadersResolved {
    type Next = SCCResolved;
}

#[derive(Debug)]
pub struct TypeHeaderResolvePass<'a> {
    session: TypeSession<Raw>,
    type_constructors: FxHashMap<TypeId, TypeDef<Ty>>,
    protocols: FxHashMap<TypeId, TypeDef<Ty>>,
    generics_stack: Vec<IndexMap<Name, Ty>>,
    ast: &'a mut AST<NameResolved>,
}

impl<'a> TypeHeaderResolvePass<'a> {
    pub fn drive(
        ast: &mut AST<NameResolved>,
        session: TypeSession<Raw>,
    ) -> TypeSession<HeadersResolved> {
        let resolver = TypeHeaderResolvePass {
            session,
            type_constructors: Default::default(),
            protocols: Default::default(),
            generics_stack: Default::default(),
            ast,
        };

        resolver.solve()
    }

    fn solve(mut self) -> TypeSession<HeadersResolved> {
        let level = Level(1);
        let mut wants = Wants::default();

        for (decl_id, type_def) in self.session.phase.type_constructors.clone() {
            if let Ok(resolved) = self.resolve_type_def(&type_def, level, &mut wants) {
                self.type_constructors.insert(decl_id, resolved.clone());
                self.session
                    .term_env
                    .promote(Symbol::Type(decl_id), resolved.to_env_entry())
            }
        }

        self.session.advance(HeadersResolved {
            type_constructors: self.type_constructors,
            protocols: self.protocols,
        })
    }

    fn resolve_fields(
        &mut self,
        fields: &TypeFields<ASTTyRepr>,
        level: Level,
        wants: &mut Wants,
    ) -> TypeFields<Ty> {
        match fields {
            TypeFields::Enum { variants, methods } => TypeFields::<Ty>::Enum {
                variants: self.resolve_variants(variants, level, wants),
                methods: self.resolve_methods(methods, level, wants),
            },
            TypeFields::Struct {
                initializers,
                methods,
                properties,
            } => TypeFields::<Ty>::Struct {
                initializers: self.resolve_initializers(initializers, level, wants),
                methods: self.resolve_methods(methods, level, wants),
                properties: self.resolve_properties(properties, level, wants),
            },
            TypeFields::Protocol {
                initializers,
                methods,
                method_requirements,
                properties,
                associated_types,
            } => TypeFields::<Ty>::Protocol {
                initializers: self.resolve_initializers(initializers, level, wants),
                methods: self.resolve_methods(methods, level, wants),
                properties: self.resolve_properties(properties, level, wants),
                method_requirements: self.resolve_method_requirements(
                    method_requirements,
                    level,
                    wants,
                ),
                associated_types: self.resolve_associated_types(associated_types),
            },
            TypeFields::Primitive => TypeFields::<Ty>::Primitive,
        }
    }

    #[instrument(skip(self))]
    fn resolve_type_def(
        &mut self,
        type_def: &TypeDef<ASTTyRepr>,
        level: Level,
        wants: &mut Wants,
    ) -> Result<TypeDef<Ty>, TypeError> {
        let _s = trace_span!("resolve", type_def = format!("{type_def:?}")).entered();

        let mut generics = IndexMap::default();

        for (name, generic) in type_def.generics.iter() {
            let ty_repr = self.infer_ast_ty_repr(generic, level, wants);
            generics.insert(name.clone(), ty_repr);
        }

        self.generics_stack.push(generics);

        let fields = self.resolve_fields(&type_def.fields, level, wants);

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

    fn resolve_variants(
        &mut self,
        variants: &IndexMap<Label, Variant<ASTTyRepr>>,
        level: Level,
        wants: &mut Wants,
    ) -> IndexMap<Label, Variant<Ty>> {
        let mut resolved_variants = IndexMap::default();
        for (name, variant) in variants {
            resolved_variants.insert(
                name.clone(),
                Variant {
                    fields: variant
                        .fields
                        .iter()
                        .map(|f| self.infer_ast_ty_repr(f, level, wants))
                        .collect(),
                    symbol: variant.symbol,
                    tag: variant.tag.clone(),
                },
            );
        }

        resolved_variants
    }

    fn resolve_methods(
        &mut self,
        methods: &IndexMap<Label, Method<ASTTyRepr>>,
        level: Level,
        wants: &mut Wants,
    ) -> IndexMap<Label, Method<Ty>> {
        let mut resolved_methods = IndexMap::default();
        for (name, method) in methods {
            let ret = self.infer_ast_ty_repr(&method.ret, Level(1), wants);
            resolved_methods.insert(
                name.clone(),
                Method {
                    id: method.id,
                    span: method.span,
                    symbol: method.symbol,
                    is_static: method.is_static,
                    params: method
                        .params
                        .iter()
                        .map(|f| self.infer_ast_ty_repr(f, level, wants))
                        .collect(),
                    ret,
                },
            );
        }

        resolved_methods
    }

    fn resolve_properties(
        &mut self,
        properties: &IndexMap<Label, Property<ASTTyRepr>>,
        level: Level,
        wants: &mut Wants,
    ) -> IndexMap<Label, Property<Ty>> {
        let mut resolved_properties = IndexMap::default();
        for (name, prop) in properties {
            let ty_repr = self.infer_ast_ty_repr(&prop.ty_repr, level, wants);
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

    fn resolve_initializers(
        &mut self,
        initializers: &IndexMap<Name, Initializer<ASTTyRepr>>,
        level: Level,
        wants: &mut Wants,
    ) -> IndexMap<Name, Initializer<Ty>> {
        let mut resolved_initializers = IndexMap::default();
        for (name, initializer) in initializers {
            resolved_initializers.insert(
                name.clone(),
                Initializer {
                    params: initializer
                        .params
                        .iter()
                        .map(|f| self.infer_ast_ty_repr(f, level, wants))
                        .collect(),
                },
            );
        }

        resolved_initializers
    }

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

    fn resolve_method_requirements(
        &mut self,
        requirements: &IndexMap<Label, MethodRequirement<ASTTyRepr>>,
        level: Level,
        wants: &mut Wants,
    ) -> IndexMap<Label, MethodRequirement<Ty>> {
        let mut resolved_method_requirements = IndexMap::default();
        for (name, method_requirement) in requirements {
            let ret = self.infer_ast_ty_repr(&method_requirement.ret, level, wants);

            resolved_method_requirements.insert(
                name.clone(),
                MethodRequirement {
                    params: method_requirement
                        .params
                        .iter()
                        .map(|f| self.infer_ast_ty_repr(f, level, wants))
                        .collect(),
                    ret,
                    id: method_requirement.id,
                },
            );
        }

        resolved_method_requirements
    }

    #[instrument(skip(self))]
    pub(crate) fn infer_type_annotation(
        &mut self,
        annotation: &TypeAnnotation,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Func { .. } => todo!(),
            TypeAnnotationKind::Tuple(..) => todo!(),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym, _),
                ..
            } => match self.session.term_env.lookup(sym).unwrap().clone() {
                EnvEntry::Mono(ty) => ty.clone(),
                EnvEntry::Scheme(scheme) => {
                    scheme
                        .inference_instantiate(&mut self.session, level, wants, annotation.span)
                        .0
                }
            },
            TypeAnnotationKind::Record { fields } => {
                let mut row = Row::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = Row::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.infer_type_annotation(&field.value, level, wants),
                    };
                }

                Ty::Struct(None, Box::new(row))
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn infer_ast_ty_repr(
        &mut self,
        ty_repr: &ASTTyRepr,
        level: Level,
        wants: &mut Wants,
    ) -> Ty {
        match &ty_repr {
            ASTTyRepr::Annotated(annotation) => {
                self.infer_type_annotation(annotation, level, wants)
            }
            ASTTyRepr::SelfType(name, _, _) => {
                let Name::Resolved(Symbol::Type(type_id), _) = name else {
                    panic!("didn't get type id");
                };
                // For self parameters in methods, look up the struct type from the environment
                // The struct type should be in the environment by now
                let entry = self
                    .session
                    .term_env
                    .lookup(&Symbol::Type(*type_id))
                    .cloned();

                let type_con = self
                    .session
                    .phase
                    .type_constructors
                    .get(type_id)
                    .expect("didn't get type");
                match entry {
                    Some(EnvEntry::Mono(ty)) => ty,
                    Some(EnvEntry::Scheme(scheme)) => scheme.ty.clone(),
                    None => unreachable!("define_type didn't work"),
                }
            }
            ASTTyRepr::Hole(..) => Ty::Param(self.session.vars.type_params.next_id()),
            ASTTyRepr::Generic(decl) => {
                let ty = Ty::Param(self.session.vars.type_params.next_id());
                self.session.term_env.promote(
                    decl.name
                        .symbol()
                        .expect("didn't resolve name of generic param"),
                    EnvEntry::Mono(ty.clone()),
                );
                ty
            }
        }
    }
}

fn build_row(kind: TypeDefKind, tys: Vec<(Label, Ty)>) -> Row {
    tys.into_iter()
        .fold(Row::Empty(kind), |mut acc, (label, ty)| {
            acc = Row::Extend {
                row: Box::new(acc),
                label: label.clone(),
                ty,
            };
            acc
        })
}

#[cfg(test)]
pub mod tests {
    use crate::{
        assert_eq_diff,
        ast::AST,
        make_row,
        name_resolution::{
            name_resolver::NameResolved, name_resolver_tests::tests::resolve, symbol::SynthesizedId,
        },
        node_id::NodeID,
        span::Span,
        types::{passes::type_header_decl_pass::TypeHeaderDeclPass, type_session::TypeDefKind},
    };

    use super::*;

    pub fn type_header_resolve_pass(
        code: &'static str,
    ) -> (AST<NameResolved>, TypeSession<HeadersResolved>) {
        let (ast, session) = type_header_resolve_pass_err(code).unwrap();
        assert!(
            ast.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            ast.diagnostics
        );
        (ast, session)
    }

    pub fn type_header_resolve_pass_err(
        code: &'static str,
    ) -> Result<(AST<NameResolved>, TypeSession<HeadersResolved>), TypeError> {
        let mut resolved = resolve(code);
        let mut session = TypeSession::default();
        TypeHeaderDeclPass::drive(&mut session, &resolved);
        let res = TypeHeaderResolvePass::drive(&mut resolved, session);
        Ok((resolved, res))
    }

    #[test]
    fn synthesizes_init() {
        let (_, session) = type_header_resolve_pass(
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
                initializers: crate::indexmap!(Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer { params: vec![
                    Ty::Int
                ] }),
                methods: Default::default(),
                properties: crate::indexmap!("age".into() => Property { is_static: false, ty_repr: Ty::Int }),
            }
        )
    }

    #[test]
    fn resolves_method() {
        let (_, session) = type_header_resolve_pass(
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
                methods: crate::indexmap!("fizz".into() => Method {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    symbol: Symbol::Type(TypeId(2)),
                    is_static: false,
                    params: vec![Ty::Int],
                    ret: Ty::Int
                }),
                properties: Default::default(),
            }
        )
    }

    #[test]
    fn resolves_out_of_order() {
        let (_, session) = type_header_resolve_pass(
            "
        struct A {
            let b: B
        }

        struct B {
            let a: A
        }
        ",
        );

        let a = Ty::Struct(
            Some(Name::Resolved(Symbol::Type(TypeId(1)), "A".into())),
            Box::new(Row::Empty(TypeDefKind::Struct)),
        );

        let b = Ty::Struct(
            Some(Name::Resolved(Symbol::Type(TypeId(2)), "B".into())),
            Box::new(Row::Empty(TypeDefKind::Struct)),
        );

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
        let (_, session) = type_header_resolve_pass(
            "
        struct Fizz<T> {
            let t: T
        }",
        );

        let type_def = session.phase.type_constructors.get(&TypeId(1)).unwrap();

        assert_eq!(
            type_def.generics,
            crate::indexmap!(Name::Resolved(Symbol::Type(TypeId(2)), "T".into()) => Ty::Param(2.into()))
        );
        let TypeFields::Struct { properties, .. } = &type_def.fields else {
            panic!("didn't get fields");
        };

        assert_eq!(
            *properties,
            crate::indexmap!(
                "t".into() => Property::<Ty> { is_static: false, ty_repr: Ty::Param(2.into()) }
            )
        );
    }

    #[test]
    fn lowers_type_application() {
        let (_, session) = type_header_resolve_pass(
            "
            struct A<T, U> {
                let t: T
                let u: U
            } 
            struct B {
                let a: A<Int, Float>
            }
            ",
        );

        let a = Ty::Struct(
            Some(Name::Resolved(Symbol::Type(TypeId(1)), "A".into())),
            Box::new(make_row!(Enum, "t" => Ty::Int, "u" => Ty::Float)),
        );

        // let type_application = Ty::TypeApplication(
        //     Box::new(Ty::TypeApplication(
        //         Box::new(Ty::TypeConstructor {
        //             name: ,
        //             kind: TypeDefKind::Struct,
        //         }),
        //         Box::new(Ty::Int),
        //     )),
        //     Box::new(Ty::Float),
        // );

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
                            a.clone()
                        ]
                }
                ),
                methods: Default::default(),
                properties: crate::indexmap!(
                    "a".into() => Property {
                        is_static: false,
                        ty_repr: a.clone()
                    }
                )
            }
        );
    }

    #[test]
    fn lowers_nested_type_application() {
        let (_, session) = type_header_resolve_pass(
            "
            struct A<T> {
                t: T
            }
            struct B<T> {
                a: A<T>
            }
            struct C {
                let b: B<A<Int>>
            }
            ",
        );

        let a = Ty::Struct(
            Some(Name::Resolved(Symbol::Type(TypeId(1)), "A".into())),
            Box::new(make_row!(Struct, "t" => Ty::Int)),
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
                            a.clone()
                        ]
                }
                ),
                methods: Default::default(),
                properties: crate::indexmap!(
                    "b".into() => Property {
                        is_static: false,
                        ty_repr: a.clone()
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
