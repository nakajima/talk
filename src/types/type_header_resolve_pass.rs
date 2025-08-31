use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use crate::{
    name::Name,
    name_resolution::symbol::{DeclId, Symbol, SynthesizedId},
    node_kinds::type_annotation::{TypeAnnotation, TypeAnnotationKind},
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

#[derive(Debug, PartialEq, Eq)]
pub struct HeadersResolved {}
impl TypingPhase for HeadersResolved {
    type TyPhase = Ty;
}

#[derive(Debug)]
pub struct TypeHeaderResolvePass {
    session: TypeSession<Raw>,
    type_constructors: FxHashMap<DeclId, TypeDef<HeadersResolved>>,
    protocols: FxHashMap<DeclId, TypeDef<HeadersResolved>>,
    type_env: FxHashMap<DeclId, Ty>,
}

impl TypeHeaderResolvePass {
    pub fn drive(session: TypeSession<Raw>) -> Result<TypeSession<HeadersResolved>, TypeError> {
        let mut resolver = TypeHeaderResolvePass {
            session,
            type_constructors: Default::default(),
            protocols: Default::default(),
            type_env: Default::default(),
        };

        resolver.solve()?;

        Ok(TypeSession::<HeadersResolved> {
            type_constructors: resolver.type_constructors,
            protocols: resolver.protocols,
            type_env: resolver.type_env,
            synthsized_ids: resolver.session.synthsized_ids,
        })
    }

    fn solve(&mut self) -> Result<(), TypeError> {
        for (decl_id, type_def) in self.session.type_constructors.iter() {
            let mut fields = match &type_def.fields {
                TypeFields::Enum { variants, methods } => TypeFields::<HeadersResolved>::Enum {
                    variants: self.resolve_variants(variants)?,
                    methods: self.resolve_methods(methods)?,
                },
                TypeFields::Struct {
                    initializers,
                    methods,
                    properties,
                } => TypeFields::<HeadersResolved>::Struct {
                    initializers: self.resolve_initializers(initializers)?,
                    methods: self.resolve_methods(methods)?,
                    properties: self.resolve_properties(properties)?,
                },
                TypeFields::Protocol {
                    initializers,
                    methods,
                    method_requirements,
                    properties,
                    associated_types,
                } => TypeFields::<HeadersResolved>::Protocol {
                    initializers: self.resolve_initializers(initializers)?,
                    methods: self.resolve_methods(methods)?,
                    properties: self.resolve_properties(properties)?,
                    method_requirements: self.resolve_method_requirements(method_requirements)?,
                    associated_types: self.resolve_associated_types(associated_types)?,
                },
                TypeFields::Primitive => TypeFields::<HeadersResolved>::Primitive,
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
                        params: properties.values().map(|p| p.ty_repr.clone()).collect(),
                    },
                );
            }

            self.type_constructors.insert(
                *decl_id,
                TypeDef {
                    name: type_def.name.clone(),
                    kind: type_def.kind.clone(),
                    def: type_def.def.clone(),
                    generics: vec![],
                    fields,
                },
            );
        }

        Ok(())
    }

    fn resolve_variants(
        &self,
        variants: &IndexMap<Name, Variant<Raw>>,
    ) -> Result<IndexMap<Name, Variant<HeadersResolved>>, TypeError> {
        let mut resolved_variants = IndexMap::default();
        for (name, variant) in variants {
            resolved_variants.insert(
                name.clone(),
                Variant {
                    fields: variant
                        .fields
                        .iter()
                        .map(|f| self.resolve_ty_repr(f))
                        .collect::<Result<_, _>>()?,
                },
            );
        }

        Ok(resolved_variants)
    }

    fn resolve_methods(
        &self,
        methods: &IndexMap<Name, Method<Raw>>,
    ) -> Result<IndexMap<Name, Method<HeadersResolved>>, TypeError> {
        let mut resolved_methods = IndexMap::default();
        for (name, method) in methods {
            resolved_methods.insert(
                name.clone(),
                Method {
                    is_static: method.is_static,
                    params: method
                        .params
                        .iter()
                        .map(|f| self.resolve_ty_repr(f))
                        .collect::<Result<_, _>>()?,
                    ret: self.resolve_ty_repr(&method.ret)?,
                },
            );
        }

        Ok(resolved_methods)
    }

    fn resolve_properties(
        &self,
        properties: &IndexMap<Name, Property<Raw>>,
    ) -> Result<IndexMap<Name, Property<HeadersResolved>>, TypeError> {
        let mut resolved_properties = IndexMap::default();
        for (name, prop) in properties {
            resolved_properties.insert(
                name.clone(),
                Property {
                    is_static: prop.is_static,
                    ty_repr: self.resolve_ty_repr(&prop.ty_repr)?,
                },
            );
        }

        Ok(resolved_properties)
    }

    fn resolve_initializers(
        &self,
        initializers: &IndexMap<Name, Initializer<Raw>>,
    ) -> Result<IndexMap<Name, Initializer<HeadersResolved>>, TypeError> {
        let mut resolved_initializers = IndexMap::default();
        for (name, initializer) in initializers {
            resolved_initializers.insert(
                name.clone(),
                Initializer {
                    params: initializer
                        .params
                        .iter()
                        .map(|f| self.resolve_ty_repr(f))
                        .collect::<Result<_, _>>()?,
                },
            );
        }

        Ok(resolved_initializers)
    }

    fn resolve_associated_types(
        &self,
        associated_types: &IndexMap<Name, Associated>,
    ) -> Result<IndexMap<Name, Associated>, TypeError> {
        let mut resolved_associated_types = IndexMap::default();
        for name in associated_types.keys() {
            resolved_associated_types.insert(name.clone(), Associated {});
        }

        Ok(resolved_associated_types)
    }

    fn resolve_method_requirements(
        &self,
        requirements: &IndexMap<Name, MethodRequirement<Raw>>,
    ) -> Result<IndexMap<Name, MethodRequirement<HeadersResolved>>, TypeError> {
        let mut resolved_method_requirements = IndexMap::default();
        for (name, method_requirement) in requirements {
            resolved_method_requirements.insert(
                name.clone(),
                MethodRequirement {
                    params: method_requirement
                        .params
                        .iter()
                        .map(|f| self.resolve_ty_repr(f))
                        .collect::<Result<_, _>>()?,
                    ret: self.resolve_ty_repr(&method_requirement.ret)?,
                },
            );
        }

        Ok(resolved_method_requirements)
    }

    fn resolve_ty_repr(&self, ty_repr: &ASTTyRepr) -> Result<Ty, TypeError> {
        match ty_repr {
            ASTTyRepr::Annotated(type_annotation) => self.resolve_type_annotation(type_annotation),
            ASTTyRepr::Hole(id) => Ok(Ty::Hole(*id)),
            ASTTyRepr::Generic(_generic) => todo!(),
        }
    }

    fn resolve_type_annotation(&self, type_annotation: &TypeAnnotation) -> Result<Ty, TypeError> {
        match &type_annotation.kind {
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(id, _),
                generics: _,
            } => {
                let constructor = match id {
                    Symbol::Type(id) => self.type_constructors.get(id),
                    Symbol::BuiltinType(..) => return Ok(resolve_builtin_type(id)),
                    _ => todo!(),
                };

                let Some(constructor) = constructor else {
                    return Err(TypeError::Any);
                };

                Ok(Ty::Nominal {
                    name: constructor.name.clone(),
                    kind: constructor.def.clone(),
                })
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
        ast::AST,
        fxhashmap,
        name_resolution::{
            name_resolver::NameResolved, name_resolver_tests::tests::resolve, symbol::SynthesizedId,
        },
        types::type_header_decl_pass::TypeHeaderDeclPass,
    };

    use super::*;

    pub fn pass(code: &'static str) -> TypeSession<HeadersResolved> {
        let (ast, session) = pass_err(code).unwrap();
        assert!(
            ast.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            ast.diagnostics
        );
        session
    }

    pub fn pass_err(
        code: &'static str,
    ) -> Result<(AST<NameResolved>, TypeSession<HeadersResolved>), TypeError> {
        let resolved = resolve(code);
        let mut session = TypeSession::default();
        TypeHeaderDeclPass::drive(&mut session, &resolved);
        Ok((resolved, TypeHeaderResolvePass::drive(session)?))
    }

    #[test]
    fn synthesizes_init() {
        let session = pass(
            "
        struct Person {
            let age: Int
        }
        ",
        );

        assert_eq!(
            session.type_constructors.get(&DeclId(1)).unwrap().fields,
            TypeFields::Struct {
                initializers: crate::indexmap!(Name::Resolved(Symbol::Synthesized(SynthesizedId(1)), "init".into()) => Initializer { params: vec![Ty::Int] }),
                methods: Default::default(),
                properties: crate::indexmap!(Name::Resolved(Symbol::Value(DeclId(2)), "age".into()) => Property { is_static: false, ty_repr: Ty::Int }),
            }
        )
    }
}
