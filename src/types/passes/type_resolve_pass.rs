use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::{instrument, trace_span};

use crate::{
    ast::AST,
    diagnostic::Diagnostic,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, TypeId},
    },
    node_kinds::type_annotation::{TypeAnnotation, TypeAnnotationKind},
    types::{
        builtins::resolve_builtin_type,
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        passes::{dependencies_pass::SCCResolved, inference_pass::curry},
        row::Row,
        scheme::Scheme,
        term_environment::EnvEntry,
        ty::Ty,
        type_catalog::{Extension, Nominal, NominalForm, Protocol, TypeCatalog},
        type_error::TypeError,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeSession, TypingPhase},
    },
};

#[derive(Debug, PartialEq)]
pub struct HeadersResolved {
    pub type_catalog: TypeCatalog,
}

impl TypingPhase for HeadersResolved {
    type Next = SCCResolved;
}

#[derive(Debug)]
pub struct TypeResolvePass<'a> {
    session: TypeSession<Raw>,
    // This is what we return
    type_catalog: TypeCatalog,
    generics: IndexMap<TypeId, Ty>,
    #[allow(dead_code)]
    ast: &'a mut AST<NameResolved>,
}

impl<'a> TypeResolvePass<'a> {
    pub fn drive(
        ast: &mut AST<NameResolved>,
        session: TypeSession<Raw>,
    ) -> TypeSession<HeadersResolved> {
        let resolver = TypeResolvePass {
            session,
            type_catalog: Default::default(),
            generics: Default::default(),
            ast,
        };

        resolver.solve()
    }

    fn solve(mut self) -> TypeSession<HeadersResolved> {
        for (decl_id, type_def) in self.session.phase.type_constructors.iter() {
            // Forward declare types with empty rows
            match type_def.def {
                TypeDefKind::Struct => self.session.term_env.insert_mono(
                    Symbol::Type(*decl_id),
                    Ty::Nominal {
                        id: *decl_id,
                        type_args: vec![],
                    },
                ),
                TypeDefKind::Enum => self.session.term_env.insert_mono(
                    Symbol::Type(*decl_id),
                    Ty::Nominal {
                        id: *decl_id,
                        type_args: vec![],
                    },
                ),
                _ => (),
            }
        }

        for (decl_id, type_def) in self.session.phase.type_constructors.clone() {
            if let Ok(resolved) = self.resolve_type_def(&type_def) {
                self.type_catalog.nominals.insert(decl_id, resolved);
            }
        }

        for (decl_id, type_def) in self.session.phase.protocols.clone() {
            if let Ok(resolved) = self.resolve_protocol(&type_def) {
                self.type_catalog.protocols.insert(decl_id, resolved);
            }
        }

        TypeSession::<HeadersResolved> {
            vars: self.session.vars,
            synthsized_ids: self.session.synthsized_ids,
            phase: HeadersResolved {
                type_catalog: self.type_catalog,
            },
            term_env: self.session.term_env,
            meta_levels: self.session.meta_levels,
        }
    }

    fn resolve_form(&mut self, type_def: &TypeDef<ASTTyRepr>, generics: Vec<Ty>) -> NominalForm {
        match &type_def.fields {
            TypeFields::Enum { variants, methods } => {
                let variants = self.resolve_variants(variants);

                NominalForm::Enum {
                    variants,
                    methods: self.resolve_methods(methods),
                    static_methods: Default::default(),
                }
            }
            TypeFields::Struct {
                initializers,
                methods,
                properties,
            } => {
                let properties = self.resolve_properties(type_def, properties, generics.clone());
                let initializers =
                    self.resolve_initializers(type_def, initializers, generics.clone());

                NominalForm::Struct {
                    initializers,
                    properties,
                    methods: self.resolve_methods(methods),
                    static_methods: Default::default(),
                }
            }
            TypeFields::Primitive => todo!(),
            _ => unreachable!(),
        }
    }

    fn resolve_protocol(&mut self, type_def: &TypeDef<ASTTyRepr>) -> Result<Protocol, TypeError> {
        let Symbol::Type(_id) = type_def.name.symbol().unwrap() else {
            unreachable!()
        };

        let TypeFields::Protocol {
            methods,
            method_requirements,
            associated_types: _,
        } = &type_def.fields
        else {
            unreachable!()
        };

        let methods = self.resolve_methods(methods);
        let method_requirements = self.resolve_method_requirements(method_requirements);

        Ok(Protocol {
            node_id: type_def.node_id,
            methods,
            method_requirements,
        })
    }

    #[instrument(skip(self))]
    fn resolve_type_def(&mut self, type_def: &TypeDef<ASTTyRepr>) -> Result<Nominal, TypeError> {
        let _s = trace_span!("resolve", type_def = format!("{type_def:?}")).entered();

        let mut generics = vec![];

        for (name, generic) in type_def.generics.iter() {
            let Name::Resolved(Symbol::Type(type_id), _) = name else {
                tracing::error!("didn't resolve {name:?}");
                continue;
            };

            let ty_repr = self.infer_ast_ty_repr(generic);
            generics.push(ty_repr.clone());
            self.generics.insert(*type_id, ty_repr);
        }

        let form = self.resolve_form(type_def, generics.clone());

        // Promote forward declared monotype into a scheme
        let symbol = type_def.name.symbol().unwrap();
        let foralls = generics
            .into_iter()
            .flat_map(|g| g.collect_foralls())
            .collect();

        // Protocols aren't actually ever terms
        if type_def.def != TypeDefKind::Protocol {
            let Some(EnvEntry::Mono(ty)) = self.session.term_env.lookup(&symbol) else {
                panic!("didn't forward declare properly: {symbol:?}");
            };
            self.session.term_env.promote(
                symbol,
                EnvEntry::Scheme(Scheme::new(foralls, vec![], ty.clone())),
            );
        }

        let extensions = type_def
            .extensions
            .iter()
            .map(|extension| Extension {
                node_id: extension.node_id,
                conformances: extension.conformances.clone(),
                methods: self.resolve_methods(&extension.methods),
            })
            .collect();

        Ok(Nominal {
            node_id: type_def.node_id,
            form,
            extensions,
        })
    }

    fn resolve_variants(
        &mut self,
        variants: &IndexMap<Label, Variant<ASTTyRepr>>,
    ) -> FxHashMap<Label, Symbol> {
        let mut resolved_variants = FxHashMap::<Label, Symbol>::default();
        for (name, variant) in variants {
            let ty = match variant.fields.len() {
                0 => Ty::Void,
                1 => self.infer_ast_ty_repr(&variant.fields[0]),
                _ => Ty::Tuple(
                    variant
                        .fields
                        .iter()
                        .map(|f| self.infer_ast_ty_repr(f))
                        .collect(),
                ),
            };

            let foralls = ty.collect_foralls();
            let scheme = Scheme::new(foralls, vec![], ty);
            self.session
                .term_env
                .promote(variant.symbol, EnvEntry::Scheme(scheme));

            resolved_variants.insert(name.clone(), variant.symbol);
        }

        resolved_variants
    }

    fn resolve_methods(
        &mut self,
        methods: &IndexMap<Label, Method<ASTTyRepr>>,
    ) -> FxHashMap<Label, Symbol> {
        let mut resolved_methods = FxHashMap::default();
        for (name, method) in methods {
            println!("method params: {:?}", method.params);
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| self.infer_ast_ty_repr(f))
                .collect();
            let ret = self.infer_ast_ty_repr(&method.ret);
            let fn_ty = curry(params.clone(), ret.clone());

            self.session.term_env.promote(
                method.symbol,
                EnvEntry::Scheme(Scheme::new(fn_ty.collect_foralls(), vec![], fn_ty)),
            );

            resolved_methods.insert(name.clone(), method.symbol);
        }

        resolved_methods
    }

    fn resolve_properties(
        &mut self,
        type_def: &TypeDef<ASTTyRepr>,
        properties: &IndexMap<Label, Property<ASTTyRepr>>,
        _generics: Vec<Ty>,
    ) -> Row {
        let mut row = Row::Empty(type_def.def);

        for (label, prop) in properties {
            if prop.is_static {
                continue;
            }

            let ty = self.infer_ast_ty_repr(&prop.ty_repr);
            row = Row::Extend {
                row: Box::new(row),
                label: label.clone(),
                ty,
            }
        }

        row
    }

    fn resolve_initializers(
        &mut self,
        type_def: &TypeDef<ASTTyRepr>,
        initializers: &IndexMap<Label, Initializer<ASTTyRepr>>,
        generics: Vec<Ty>,
    ) -> FxHashMap<Label, Symbol> {
        let mut out = FxHashMap::default();
        let Name::Resolved(Symbol::Type(type_id), _) = &type_def.name else {
            unreachable!()
        };

        let result_self = Ty::Nominal {
            id: *type_id,
            type_args: generics,
        };

        for (label, init) in initializers {
            let params: Vec<Ty> = init.params[1..]
                .iter()
                .map(|p| self.infer_ast_ty_repr(p))
                .collect();

            let ctor_fn = curry(params, result_self.clone());
            let foralls = ctor_fn.collect_foralls();

            self.session.term_env.promote(
                init.symbol,
                EnvEntry::Scheme(Scheme::new(foralls, vec![], ctor_fn)),
            );

            out.insert(label.clone(), init.symbol);
        }

        out
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
    ) -> FxHashMap<Label, Symbol> {
        let mut resolved_methods = FxHashMap::default();
        for (name, method) in requirements {
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| self.infer_ast_ty_repr(f))
                .collect();
            let ret = self.infer_ast_ty_repr(&method.ret);
            let fn_ty = curry(params.clone(), ret.clone());

            self.session.term_env.promote(
                method.symbol,
                EnvEntry::Scheme(Scheme::new(fn_ty.collect_foralls(), vec![], fn_ty)),
            );

            resolved_methods.insert(name.clone(), method.symbol);
        }
        resolved_methods
    }

    #[instrument(skip(self))]
    pub(crate) fn infer_type_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
        match &annotation.kind {
            TypeAnnotationKind::Func { .. } => todo!(),
            TypeAnnotationKind::Tuple(..) => todo!(),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::BuiltinType(..), _),
                ..
            } => resolve_builtin_type(sym),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(Symbol::Type(type_id), _),
                generics,
            } => {
                match self
                    .session
                    .phase
                    .type_constructors
                    .get(type_id)
                    .map(|f| f.def)
                {
                    Some(TypeDefKind::Struct) => Ty::Nominal {
                        id: *type_id,
                        type_args: generics
                            .iter()
                            .map(|g| self.infer_type_annotation(g))
                            .collect(),
                    },
                    Some(TypeDefKind::Enum) => Ty::Nominal {
                        id: *type_id,
                        type_args: generics
                            .iter()
                            .map(|g| self.infer_type_annotation(g))
                            .collect(),
                    },
                    _ => {
                        if let Some(generic) = self.generics.get(type_id) {
                            return generic.clone();
                        }

                        tracing::error!(
                            "didn't find {type_id:?} in {:?}",
                            self.session.phase.type_constructors
                        );

                        self.ast
                            .diagnostics
                            .push(crate::diagnostic::AnyDiagnostic::Typing(Diagnostic {
                                path: self.ast.path.clone(),
                                span: annotation.span,
                                kind: TypeError::TypeConstructorNotFound(*type_id),
                            }));

                        Ty::Void
                    }
                }
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = Row::Empty(TypeDefKind::Struct);
                for field in fields.iter().rev() {
                    row = Row::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty: self.infer_type_annotation(&field.value),
                    };
                }

                Ty::Record(Box::new(row))
            }
            _ => unreachable!("unhandled type annotation: {annotation:?}"),
        }
    }

    pub(crate) fn infer_ast_ty_repr(&mut self, ty_repr: &ASTTyRepr) -> Ty {
        match &ty_repr {
            ASTTyRepr::Annotated(annotation) => self.infer_type_annotation(annotation),
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

                match entry {
                    Some(EnvEntry::Mono(ty)) => ty,
                    Some(EnvEntry::Scheme(scheme)) => scheme.ty.clone(),
                    None => unreachable!("define_type didn't work: {ty_repr:?}"),
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

#[cfg(test)]
pub mod tests {
    use crate::{
        ast::AST,
        fxhashmap, make_row,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{GlobalId, PropertyId, TypeId},
        },
        types::{passes::type_headers_pass::TypeHeaderPass, ty::TypeParamId},
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
        TypeHeaderPass::drive(&mut session, &resolved);
        let res = TypeResolvePass::drive(&mut resolved, session);
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
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: Default::default(),
                properties: make_row!(Struct, "age" => Ty::Int),
                methods: Default::default(),
                static_methods: Default::default()
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
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: Default::default(),
                properties: Row::Empty(TypeDefKind::Struct),
                methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::Global(GlobalId(1))),
                static_methods: Default::default()
            }
        )
    }

    #[test]
    fn resolves_type_params() {
        let (_, session) = type_header_resolve_pass(
            "
        struct Fizz<T> {
            let t: T
        }",
        );

        assert_eq!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: Default::default(),
                properties: make_row!(Struct, "t" => Ty::Param(1.into())),
                methods: Default::default(),
                static_methods: Default::default()
            }
        )
    }

    #[test]
    fn lowers_nested_type_application() {
        let (_, session) = type_header_resolve_pass(
            "
            struct A<T> {
                let t: T
            }
            struct B<T> {
                let a: A<T>
            }
            struct C {
                let b: B<A<Int>>
            }
            ",
        );

        assert_eq!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(5))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: Default::default(),
                properties: make_row!(Struct,
                    "b" => Ty::Nominal { id: TypeId(1), type_args: vec![]}
                ),
                methods: Default::default(),
                static_methods: Default::default()
            }
        );
    }

    #[test]
    #[ignore = "we should fix this"]
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
