use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::{instrument, trace_span};

use crate::{
    ast::AST,
    guard_found_ty,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, TypeId},
    },
    node_kinds::type_annotation::{TypeAnnotation, TypeAnnotationKind},
    span::Span,
    types::{
        builtins::resolve_builtin_type,
        constraints::{
            constraint::{Constraint, ConstraintCause},
            type_member::TypeMember,
        },
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        passes::{
            dependencies_pass::{Conformance, ConformanceRequirement, SCCResolved},
            inference_pass::curry,
        },
        predicate::Predicate,
        row::Row,
        scheme::Scheme,
        term_environment::EnvEntry,
        ty::{Level, Ty},
        type_catalog::{ConformanceKey, Extension, Nominal, NominalForm, Protocol, TypeCatalog},
        type_error::TypeError,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeSession, TypingPhase},
    },
};

#[derive(Debug)]
pub struct HeadersResolved {
    pub type_catalog: TypeCatalog,
    pub resolver_constraints: Vec<Constraint>,
}

impl TypingPhase for HeadersResolved {
    type Next = SCCResolved;
}

// Takes the raw types from the headers pass and starts turning them into actual types in the type catalog
#[derive(Debug)]
pub struct TypeResolvePass<'a> {
    session: TypeSession<Raw>,
    type_catalog: TypeCatalog,
    generics: IndexMap<Symbol, Ty>,
    conformance_keys: Vec<(ConformanceKey, Span)>,
    resolver_constraints: Vec<Constraint>,
    self_symbols: Vec<Symbol>,
    self_tys: Vec<Ty>,
    _ast: &'a mut AST<NameResolved>,
}

impl<'a> TypeResolvePass<'a> {
    pub fn drive(
        ast: &mut AST<NameResolved>,
        session: TypeSession<Raw>,
    ) -> TypeSession<HeadersResolved> {
        let resolver = TypeResolvePass {
            session,
            type_catalog: Default::default(),
            resolver_constraints: Default::default(),
            generics: Default::default(),
            conformance_keys: Default::default(),
            self_symbols: Default::default(),
            self_tys: Default::default(),
            _ast: ast,
        };

        resolver.solve()
    }

    // Go through all headers and gather up properties/methods/variants/etc. Don't perform
    // any generalization until the very end.
    fn solve(mut self) -> TypeSession<HeadersResolved> {
        for (id, ty_repr) in std::mem::take(&mut self.session.phase.globals) {
            let ty = self.infer_ast_ty_repr(&ty_repr);
            self.session.types_by_node.insert(id, ty);
        }

        let mut row_vars: Vec<Row> = (0..self.session.phase.type_constructors.len())
            .map(|_| self.session.new_row_meta_var(Level(1)))
            .collect();
        for (decl_id, ty) in self.session.phase.type_constructors.iter() {
            // Forward declare types with empty rows
            match ty.def {
                TypeDefKind::Struct => self.session.term_env.insert_mono(
                    Symbol::Type(*decl_id),
                    Ty::Nominal {
                        id: *decl_id,
                        row: Box::new(row_vars.pop().unwrap()),
                        type_args: vec![],
                    },
                ),
                TypeDefKind::Enum => self.session.term_env.insert_mono(
                    Symbol::Type(*decl_id),
                    Ty::Nominal {
                        id: *decl_id,
                        row: Box::new(row_vars.pop().unwrap()),
                        type_args: vec![],
                    },
                ),
                _ => (),
            }
        }

        for (decl_id, type_def) in std::mem::take(&mut self.session.phase.type_constructors) {
            if let Ok(resolved) = self.resolve_type_def(&type_def) {
                self.type_catalog.nominals.insert(decl_id, resolved);
            }
        }

        for (decl_id, type_def) in std::mem::take(&mut self.session.phase.protocols) {
            if let Ok(resolved) = self.resolve_protocol(&type_def) {
                self.type_catalog.protocols.insert(decl_id, resolved);
            }
        }

        // Resolve associated types for conforming types
        for (conformance_key, span) in self.conformance_keys.iter() {
            let ty = self
                .type_catalog
                .nominals
                .get(&conformance_key.conforming_id)
                .unwrap();

            let protocol = self
                .type_catalog
                .protocols
                .get(&conformance_key.protocol_id)
                .unwrap();

            let associated_types = protocol
                .associated_types
                .iter()
                .map(|t| {
                    let Name::Resolved(Symbol::AssociatedType(id), name) = t.0 else {
                        unreachable!()
                    };

                    let symbol = ty
                        .child_types
                        .get(name)
                        .unwrap_or_else(|| panic!("did not get child type named: {name}"));

                    (*id, *symbol)
                })
                .collect();

            self.type_catalog.conformances.insert(
                *conformance_key,
                Conformance {
                    conforming_id: conformance_key.conforming_id,
                    protocol_id: conformance_key.protocol_id,
                    requirements: protocol.requirements.clone(),
                    associated_types,
                    span: *span,
                },
            );
        }

        self.session.advance(HeadersResolved {
            resolver_constraints: self.resolver_constraints,
            type_catalog: self.type_catalog,
        })
    }

    fn resolve_form(&mut self, type_def: &TypeDef) -> NominalForm {
        match &type_def.fields {
            TypeFields::Enum {
                variants,
                static_methods,
                instance_methods: methods,
            } => {
                let variants = self.resolve_variants(variants);

                NominalForm::Enum {
                    variants,
                    instance_methods: self.resolve_instance_methods(methods),
                    static_methods: self.resolve_static_methods(static_methods),
                }
            }
            TypeFields::Struct {
                initializers,
                static_methods,
                instance_methods: methods,
                properties,
            } => {
                let properties = self.resolve_properties(properties);
                let initializers = self.resolve_initializers(type_def, initializers);

                NominalForm::Struct {
                    initializers,
                    properties,
                    instance_methods: self.resolve_instance_methods(methods),
                    static_methods: self.resolve_static_methods(static_methods),
                }
            }
            TypeFields::Primitive => todo!(),
            _ => unreachable!(),
        }
    }

    fn resolve_protocol(&mut self, type_def: &TypeDef) -> Result<Protocol, TypeError> {
        let ty = self.session.new_type_param();
        self.self_symbols.push(type_def.name.symbol().unwrap());
        self.self_tys.push(ty);

        let TypeFields::Protocol {
            static_methods,
            instance_methods: methods,
            method_requirements,
            associated_types,
        } = &type_def.fields
        else {
            unreachable!()
        };

        let methods = self.resolve_instance_methods(methods);
        let method_requirements = self.resolve_method_requirements(method_requirements);
        let mut requirements = FxHashMap::default();
        for method_requirement in method_requirements {
            requirements.insert(
                method_requirement.0,
                ConformanceRequirement::Unfulfilled(method_requirement.1),
            );
        }

        self.self_symbols.pop();
        self.self_tys.pop();

        Ok(Protocol {
            node_id: type_def.node_id,
            methods,
            requirements,
            static_methods: self.resolve_static_methods(static_methods),
            associated_types: associated_types.clone(),
        })
    }

    #[instrument(skip(self))]
    fn resolve_type_def(&mut self, type_def: &TypeDef) -> Result<Nominal, TypeError> {
        let _s = trace_span!("resolve", type_def = format!("{type_def:?}")).entered();

        let sym = type_def.name.symbol().unwrap();
        let EnvEntry::Mono(ty) = self.session.term_env.lookup(&sym).unwrap() else {
            unreachable!()
        };

        self.self_symbols.push(sym);
        self.self_tys.push(ty.clone());

        let mut generics = vec![];

        for (name, generic) in type_def.generics.iter() {
            let Name::Resolved(sym, _) = name else {
                tracing::error!("didn't resolve {name:?}");
                continue;
            };

            let ty_repr = self.infer_ast_ty_repr(generic);
            generics.push(ty_repr.clone());
            self.generics.insert(*sym, ty_repr);
        }

        let mut form = self.resolve_form(type_def);
        let symbol = type_def.name.symbol().unwrap();
        let Symbol::Type(type_id) = &symbol else {
            unreachable!();
        };

        for c in type_def.conformances.iter() {
            self.conformance_keys.push((
                ConformanceKey {
                    protocol_id: c.protocol_id,
                    conforming_id: *type_id,
                },
                c.span,
            ));
        }

        let Some(EnvEntry::Mono(ty)) = self.session.term_env.lookup(&symbol).cloned() else {
            panic!("didn't get ty");
        };

        let type_scheme = self.session.generalize(Level(0), ty.clone(), &[]);
        self.session.term_env.promote(symbol, type_scheme);

        let extensions = type_def
            .extensions
            .iter()
            .map(|extension| {
                form.extend_methods(self.resolve_instance_methods(&extension.methods));
                Extension {
                    conformances: extension.conformances.clone(),
                    node_id: extension.node_id,
                }
            })
            .collect();

        self.self_symbols.pop();
        self.self_tys.pop();

        Ok(Nominal {
            type_id: *type_id,
            node_id: type_def.node_id,
            form,
            extensions,
            child_types: type_def.child_types.clone(),
            conformances: type_def.conformances.clone(),
        })
    }

    fn resolve_variants(
        &mut self,
        variants: &IndexMap<Label, Variant>,
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
            if foralls.is_empty() {
                self.session.term_env.insert_mono(variant.symbol, ty);
            } else {
                self.session.term_env.promote(
                    variant.symbol,
                    EnvEntry::Scheme(Scheme::new(foralls, vec![], ty)),
                );
            }

            resolved_variants.insert(name.clone(), variant.symbol);
        }

        resolved_variants
    }

    fn resolve_static_methods(
        &mut self,
        methods: &IndexMap<Label, Method>,
    ) -> FxHashMap<Label, Symbol> {
        let mut resolved_methods = FxHashMap::default();
        for (name, method) in methods {
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| self.infer_ast_ty_repr(f))
                .collect();
            let ret = self.infer_ast_ty_repr(&method.ret);
            let fn_ty = if params.is_empty() {
                Ty::Func(Box::new(Ty::Void), Box::new(ret.clone()))
            } else {
                curry(params.clone(), ret.clone())
            };

            let foralls = fn_ty.collect_foralls();

            if foralls.is_empty() {
                // No quantification necessary
                self.session.term_env.insert_mono(method.symbol, fn_ty);
            } else {
                use crate::types::{scheme::Scheme, term_environment::EnvEntry};
                self.session.term_env.promote(
                    method.symbol,
                    EnvEntry::Scheme(Scheme::new(foralls, vec![], fn_ty)),
                );
            }

            resolved_methods.insert(name.clone(), method.symbol);
        }

        resolved_methods
    }

    fn resolve_instance_methods(
        &mut self,
        methods: &IndexMap<Label, Method>,
    ) -> FxHashMap<Label, Symbol> {
        let mut resolved_methods = FxHashMap::default();
        for (name, method) in methods {
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| self.infer_ast_ty_repr(f))
                .collect();
            let ret = self.infer_ast_ty_repr(&method.ret);
            let fn_ty = if params.is_empty() {
                Ty::Func(Box::new(Ty::Void), Box::new(ret.clone()))
            } else {
                curry(params.clone(), ret.clone())
            };

            let foralls = fn_ty.collect_foralls();

            if foralls.is_empty() {
                self.session.term_env.insert_mono(method.symbol, fn_ty);
            } else {
                let mut predicates = Vec::new();
                let self_ty = params
                    .first()
                    .expect("did not create `self` param for instance method");
                predicates.push(Predicate::Member {
                    receiver: self_ty.clone(),
                    label: name.clone(),
                    ty: fn_ty.clone(),
                });

                self.session.term_env.promote(
                    method.symbol,
                    EnvEntry::Scheme(Scheme::new(foralls, predicates, fn_ty)),
                );
            }

            resolved_methods.insert(name.clone(), method.symbol);
        }

        resolved_methods
    }

    fn resolve_properties(
        &mut self,
        properties: &IndexMap<Label, Property>,
    ) -> IndexMap<Label, Symbol> {
        let mut result: IndexMap<Label, Symbol> = Default::default();

        for (label, prop) in properties {
            if prop.is_static {
                continue;
            }

            let ty = self.infer_ast_ty_repr(&prop.ty_repr);
            self.session.term_env.insert_mono(prop.symbol, ty);
            result.insert(label.clone(), prop.symbol);
        }

        result
    }

    fn resolve_initializers(
        &mut self,
        type_def: &TypeDef,
        initializers: &IndexMap<Label, Initializer>,
    ) -> FxHashMap<Label, Symbol> {
        let mut out = FxHashMap::default();
        let Name::Resolved(Symbol::Type(type_id), _) = &type_def.name else {
            unreachable!()
        };

        for (label, init) in initializers {
            let params: Vec<Ty> = init
                .params
                .iter()
                .map(|p| self.infer_ast_ty_repr(p))
                .collect();

            let ret = Ty::Nominal {
                id: *type_id,
                row: Box::new(self.session.new_row_meta_var(Level(1))),
                type_args: vec![],
            };

            let ty = curry(params, ret);

            let foralls = ty.collect_foralls();
            if foralls.is_empty() {
                self.session.term_env.insert_mono(init.symbol, ty);
            } else {
                use crate::types::{scheme::Scheme, term_environment::EnvEntry};
                self.session.term_env.promote(
                    init.symbol,
                    EnvEntry::Scheme(Scheme::new(foralls, vec![], ty)),
                );
            }
            out.insert(label.clone(), init.symbol);
        }

        out
    }

    fn _resolve_associated_types(
        &mut self,
        protocol_id: TypeId,
        associated_types: &IndexMap<Name, Associated>,
    ) -> IndexMap<Name, Associated> {
        let mut resolved_associated_types = IndexMap::default();
        for name in associated_types.keys() {
            resolved_associated_types.insert(
                name.clone(),
                Associated {
                    protocol_id,
                    symbol: name.symbol().unwrap(),
                },
            );
        }

        resolved_associated_types
    }

    fn resolve_method_requirements(
        &mut self,
        requirements: &IndexMap<Label, MethodRequirement>,
    ) -> FxHashMap<Label, Symbol> {
        let mut resolved_methods = FxHashMap::default();
        for (name, method) in requirements {
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| self.infer_ast_ty_repr(f))
                .collect();
            let ret = if let Some(ret) = &method.ret {
                self.infer_ast_ty_repr(ret)
            } else {
                Ty::Void
            };
            let fn_ty = curry(params.clone(), ret.clone());

            self.session.term_env.insert_mono(method.symbol, fn_ty);
            resolved_methods.insert(name.clone(), method.symbol);
        }
        resolved_methods
    }

    #[instrument(skip(self))]
    pub(crate) fn infer_type_annotation(&mut self, annotation: &TypeAnnotation) -> Ty {
        guard_found_ty!(self, annotation.id);

        let ty = match &annotation.kind {
            TypeAnnotationKind::SelfType(_id) => self.session.new_ty_meta_var(Level(0)),
            TypeAnnotationKind::Func { .. } => todo!(),
            TypeAnnotationKind::Tuple(..) => todo!(),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::Builtin(..), _),
                ..
            } => resolve_builtin_type(sym),
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::TypeParameter(..), ..),
                generics,
            } => {
                let mut base = self.generics.get(sym).cloned().unwrap_or_else(|| {
                    let ty = self.session.new_type_param();
                    self.generics.insert(*sym, ty.clone());
                    ty
                });

                for g in generics {
                    base = Ty::TypeApplication(base.into(), self.infer_type_annotation(g).into());
                }

                base
            }
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::Type(type_id), ..),
                generics,
            } => {
                // Check if this is a generic parameter (from type defs or functions)
                let mut base = if let Some(generic) = self.generics.get(sym).cloned() {
                    // Type definition generic (e.g., struct Foo<T>)
                    generic
                } else if let Some(entry) = self.session.term_env.lookup(sym) {
                    // Function generic (e.g., func foo<T>)
                    match entry {
                        EnvEntry::Mono(ty) => ty.clone(),
                        EnvEntry::Scheme(s) => s.ty.clone(),
                    }
                } else {
                    // It's a type constructor
                    Ty::TypeConstructor(*type_id)
                };

                // Apply generic arguments if any
                for g in generics {
                    base = Ty::TypeApplication(base.into(), self.infer_type_annotation(g).into());
                }

                base
            }
            TypeAnnotationKind::NominalPath {
                box base,
                member: Label::Named(member_name),
                member_generics,
            } => {
                let base_ty = self.infer_type_annotation(base);
                let result = self.session.new_ty_meta_var(Level(1));
                let constraint = Constraint::TypeMember(TypeMember {
                    base: base_ty,
                    name: member_name.into(),
                    generics: member_generics
                        .iter()
                        .map(|t| self.infer_type_annotation(t))
                        .collect(),
                    result: result.clone(),
                    cause: ConstraintCause::Internal,
                    span: annotation.span,
                });
                tracing::debug!(
                    "pushing constraint {:?} {:?} {constraint:?}",
                    annotation.id,
                    base
                );
                self.resolver_constraints.push(constraint);
                result
            }
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(Symbol::AssociatedType(..), ..),
                ..
            } => {
                let Symbol::Type(..) = self.self_symbols.last().cloned().unwrap() else {
                    unreachable!("didn't get protocol id");
                };

                let Some(..) = self.self_tys.last().cloned() else {
                    unreachable!("didn't get self_ty");
                };

                self.session.new_ty_meta_var(Level(1))
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
        };

        self.session.types_by_node.insert(annotation.id, ty.clone());

        ty
    }

    pub(crate) fn infer_ast_ty_repr(&mut self, ty_repr: &ASTTyRepr) -> Ty {
        match &ty_repr {
            ASTTyRepr::Annotated(annotation) => {
                guard_found_ty!(self, annotation.id);
                self.infer_type_annotation(annotation)
            }
            ASTTyRepr::SelfType(..) => self.self_tys.last().cloned().unwrap(),
            ASTTyRepr::Hole(id, ..) => Ty::Hole(*id),
            ASTTyRepr::Generic(decl) => {
                guard_found_ty!(self, decl.id);

                let ty = self.session.new_type_param();

                self.generics
                    .insert(decl.name.symbol().unwrap(), ty.clone());

                self.session.term_env.promote(
                    decl.name
                        .symbol()
                        .expect("didn't resolve name of generic param"),
                    EnvEntry::Mono(ty.clone()),
                );

                self.session.types_by_node.insert(decl.id, ty.clone());
                ty
            }
        }
    }
}

#[cfg(test)]
pub mod tests {
    use indexmap::indexmap;

    use crate::{
        assert_eq_diff,
        ast::AST,
        fxhashmap,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{
                AssociatedTypeId, InstanceMethodId, PropertyId, StaticMethodId, SynthesizedId,
                TypeId,
            },
        },
        span::Span,
        types::{
            passes::{dependencies_pass::Conformance, type_headers_pass::TypeHeaderPass},
            type_catalog::ConformanceKey,
        },
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

        assert_eq_diff!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId(1))),
                properties: indexmap! {
                    "age".into() => Symbol::Property(PropertyId(1))
                },
                instance_methods: Default::default(),
                static_methods: Default::default()
            }
        )
    }

    #[test]
    fn resolves_instance_method() {
        let (_, session) = type_header_resolve_pass(
            "
        struct Person {
            func fizz(a: Int) -> Int { a }
        }
        ",
        );

        assert_eq_diff!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId(1))),
                properties: Default::default(),
                instance_methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::InstanceMethod(InstanceMethodId(1))),
                static_methods: Default::default(),
            }
        )
    }

    #[test]
    fn resolves_extended_members() {
        let (_, session) = type_header_resolve_pass(
            "
        struct Person {}
        extend Person {
            func fizz(a: Int) -> Int { a }
        }
        ",
        );

        assert_eq_diff!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId(1))),
                properties: Default::default(),
                instance_methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::InstanceMethod(InstanceMethodId(1))),
                static_methods: Default::default(),
            }
        )
    }

    #[test]
    fn resolves_static_method() {
        let (_, session) = type_header_resolve_pass(
            "
        struct Person {
            static func fizz(a: Int) -> Int { a }
        }
        ",
        );

        assert_eq_diff!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(1))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId(1))),
                properties: Default::default(),
                instance_methods: Default::default(),
                static_methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::StaticMethod(StaticMethodId(1))),
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
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId(1))),
                properties: indexmap! { "t".into() => Symbol::Property(PropertyId(1)) },
                instance_methods: Default::default(),
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

        assert_eq_diff!(
            session
                .phase
                .type_catalog
                .nominals
                .get(&TypeId(3))
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId(3))),
                properties: indexmap! {
                    "b".into() => Symbol::Property(PropertyId(3))
                },
                instance_methods: Default::default(),
                static_methods: Default::default()
            }
        );
    }

    #[test]
    fn resolves_conformances() {
        let (_ast, session) = type_header_resolve_pass(
            "
            protocol Count {
                func count() -> Int
            }
            struct Person {}
            extend Person: Count {}
            ",
        );

        assert_eq!(
            *session
                .phase
                .type_catalog
                .conformances
                .get(&ConformanceKey {
                    protocol_id: TypeId(1),
                    conforming_id: TypeId(2)
                })
                .unwrap_or_else(|| panic!(
                    "didn't get conformance: {:?}",
                    session.phase.type_catalog.conformances
                )),
            Conformance {
                conforming_id: TypeId(2),
                protocol_id: TypeId(1),
                requirements: fxhashmap!("count".into() => ConformanceRequirement::Unfulfilled(Symbol::InstanceMethod(InstanceMethodId(1)))),
                span: Span::ANY,
                associated_types: Default::default()
            }
        )
    }

    #[test]
    fn resolves_nested_types() {
        let (_ast, session) = type_header_resolve_pass(
            "
            struct Fizz {
                struct Buzz {}
                typealias Foo = Int
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
                .child_types,
            fxhashmap!("Buzz".to_string() => Symbol::Type(TypeId(2)), "Foo".into() => Symbol::Type(TypeId(3)))
        )
    }

    #[test]
    fn resolves_associated_types() {
        let (_ast, session) = type_header_resolve_pass(
            "
            protocol Fizz {
                associated A

                func getA() -> A
                func setA(a: A)
            }
            struct Person {}
            extend Person: Fizz {
                typealias A = Int
            }
            ",
        );

        assert_eq!(
            *session
                .phase
                .type_catalog
                .conformances
                .get(&ConformanceKey {
                    protocol_id: TypeId(1),
                    conforming_id: TypeId(2)
                })
                .unwrap_or_else(|| panic!(
                    "didn't get conformance: {:?}",
                    session.phase.type_catalog.conformances
                )),
            Conformance {
                conforming_id: TypeId(2),
                protocol_id: TypeId(1),
                requirements: fxhashmap!(
                    "getA".into() => ConformanceRequirement::Unfulfilled(Symbol::InstanceMethod(InstanceMethodId(1))),
                    "setA".into() => ConformanceRequirement::Unfulfilled(Symbol::InstanceMethod(InstanceMethodId(2)))
                ),
                span: Span::ANY,
                associated_types: fxhashmap!(AssociatedTypeId(1) => Symbol::Type(TypeId(3)))
            }
        )
    }

    #[test]
    fn resolves_nominal_path_annotations() {
        let (_ast, session) = type_header_resolve_pass(
            "
            struct C {
                struct B {}
                let a: A.B
            }

            struct A {
                struct B {}
                let c: C.B
            }
            ",
        );

        // Make sure constraints are there
        assert_eq!(
            session.phase.resolver_constraints.len(),
            2,
            "{:#?}",
            session.phase.resolver_constraints
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

    #[test]
    #[ignore = "wip"]
    fn resolve_instance_method_emits_assoc_eq_predicates_for_param_and_return() {
        let code = r#"
        protocol Aged {
            associated T
        }

        struct Wrapper<U: Aged> {
            func use(value: U.T) -> U.T { value }
        }
    "#;

        // headers + resolve
        let resolved =
            crate::types::passes::type_resolve_pass::tests::type_header_resolve_pass(code);
        let (_ast, session) = resolved;

        // Sanity: protocol + type exist
        assert!(
            session
                .phase
                .type_catalog
                .protocols
                .contains_key(&TypeId(1)),
            "Aged protocol missing"
        );
        assert!(
            session.phase.type_catalog.nominals.contains_key(&TypeId(2)),
            "Wrapper type missing"
        );

        // Grab the instance method symbol for `use`
        let method_sym = Symbol::InstanceMethod(InstanceMethodId(1));
        let entry = session
            .term_env
            .lookup(&method_sym)
            .unwrap_or_else(|| panic!("no term-env entry for instance method"));

        // We expect a generalized scheme with predicates
        let Scheme { predicates, .. } = match entry {
            crate::types::term_environment::EnvEntry::Scheme(s) => s.clone(),
            other => panic!("expected Scheme, got {:?}", other),
        };

        // Find all AssociatedTypeEquals predicates
        let assoc_preds: Vec<_> = predicates
            .into_iter()
            .filter_map(|p| match p {
                Predicate::AssociatedEquals {
                    subject,
                    protocol_id,
                    associated_type_id,
                    output,
                    ..
                } => Some((subject, protocol_id, associated_type_id, output)),
                _ => None,
            })
            .collect();

        // There should be *at least* two: one for the param U.T, one for the return U.T
        assert!(
            assoc_preds.len() >= 2,
            "expected at least two AssociatedTypeEquals predicates; got {:?}",
            assoc_preds
        );

        // The subject must be the method’s first generic param U (as a Ty::Param)
        // Protocol id is Aged (TypeId(1)), associated id is T (AssociatedTypeId(1))
        for (subject, pid, aid, _out) in assoc_preds.iter() {
            assert!(
                matches!(subject, crate::types::ty::Ty::Param(_)),
                "subject should be Ty::Param for U, got {:?}",
                subject
            );
            assert_eq!(*pid, TypeId(1), "protocol id should be Aged");
            assert_eq!(*aid, AssociatedTypeId(1), "associated id should be T");
        }
    }
}
