use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::{instrument, trace_span};

use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{ProtocolId, Symbol},
    },
    node_kinds::{
        generic_decl::GenericDecl,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    span::Span,
    types::{
        builtins::resolve_builtin_type,
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        infer_row::InferRow,
        infer_ty::{InferTy, Level},
        passes::{
            dependencies_pass::{Conformance, ConformanceRequirement},
            inference_pass::curry,
        },
        predicate::Predicate,
        scheme::{ForAll, Scheme},
        term_environment::EnvEntry,
        type_catalog::{ConformanceKey, Extension, Nominal, NominalForm, Protocol},
        type_error::TypeError,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeSession},
    },
};

#[derive(Debug, Clone)]
pub struct HeadersResolved {}

// Takes the raw types from the headers pass and starts turning them into actual types in the type catalog
#[derive(Debug)]
pub struct TypeResolvePass<'a> {
    session: &'a mut TypeSession,
    raw: Raw,
    conformance_keys: Vec<(ConformanceKey, Span)>,
    self_symbols: Vec<Symbol>,
    _ast: &'a mut AST<NameResolved>,
}

impl<'a> TypeResolvePass<'a> {
    pub fn drive(
        ast: &mut AST<NameResolved>,
        session: &mut TypeSession,
        raw: Raw,
    ) -> HeadersResolved {
        let mut resolver = TypeResolvePass {
            session,
            raw,
            conformance_keys: Default::default(),
            self_symbols: Default::default(),
            _ast: ast,
        };

        resolver.solve()
    }

    // Go through all headers and gather up properties/methods/variants/etc. Don't perform
    // any generalization until the very end.
    fn solve(&mut self) -> HeadersResolved {
        for (decl_id, type_def) in self.raw.type_constructors.clone().iter() {
            let base = InferTy::Nominal {
                id: *decl_id,
                type_args: type_def
                    .generics
                    .iter()
                    .map(|_| self.session.new_type_param())
                    .collect(),
                row: Box::new(self.session.new_row_meta_var(Level(1))),
            };

            self.session.insert_mono(Symbol::Type(*decl_id), base);
        }

        for (_id, (name, rhs)) in std::mem::take(&mut self.raw.typealiases) {
            let symbol = name.symbol().unwrap();
            let entry = self.infer_type_annotation(&rhs);
            self.session.insert_term(symbol, entry.into());
        }

        for ty_repr in std::mem::take(&mut self.raw.annotations).values() {
            self.infer_ast_ty_repr(ty_repr);
        }

        for (decl_id, type_def) in self.raw.type_constructors.clone().iter() {
            if let Ok(resolved) = self.resolve_type_def(type_def) {
                self.session
                    .type_catalog
                    .nominals
                    .insert(decl_id.into(), resolved);
            }
        }

        for (decl_id, type_def) in std::mem::take(&mut self.raw.protocols) {
            if let Ok(resolved) = self.resolve_protocol(&type_def) {
                self.session
                    .type_catalog
                    .protocols
                    .insert(decl_id, resolved);
            }
        }

        // Resolve associated types for conforming types
        for (conformance_key, span) in self.conformance_keys.iter() {
            let ty = self
                .session
                .type_catalog
                .nominals
                .get(&conformance_key.conforming_id)
                .unwrap();

            let protocol = self
                .session
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

            self.session.type_catalog.conformances.insert(
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

        HeadersResolved {}
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

        // The Self type parameter should be quantified in a scheme
        let entry = if let InferTy::Param(param_id) = ty.clone() {
            EnvEntry::Scheme(Scheme {
                foralls: vec![ForAll::Ty(param_id)],
                predicates: vec![],
                ty,
            })
        } else {
            EnvEntry::Mono(ty)
        };

        self.session
            .insert_term(type_def.name.symbol().unwrap(), entry);

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
        let (ty, _, _) = self.session.lookup(&sym).unwrap().into();

        self.self_symbols.push(sym);

        for (name, generic) in type_def.generics.iter() {
            let Name::Resolved(sym, _) = name else {
                tracing::error!("didn't resolve {name:?}");
                continue;
            };

            let entry = self.infer_ast_ty_repr(generic);
            self.session.insert_term(*sym, entry.into());
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
                    conforming_id: sym,
                },
                c.span,
            ));
        }

        let type_scheme = self.session.generalize(Level(0), ty.clone(), &[]);
        self.session.insert_term(symbol, type_scheme);

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
            let mut predicates = vec![];
            let mut foralls = vec![];
            let ty = match variant.fields.len() {
                0 => InferTy::Void,
                1 => {
                    let (ty, preds, fas) = self.infer_ast_ty_repr(&variant.fields[0]);
                    predicates.extend(preds);
                    foralls.extend(fas);
                    ty
                }
                _ => InferTy::Tuple(
                    variant
                        .fields
                        .iter()
                        .map(|f| {
                            let (ty, preds, fas) = self.infer_ast_ty_repr(f);
                            predicates.extend(preds);
                            foralls.extend(fas);
                            ty
                        })
                        .collect(),
                ),
            };

            let foralls = ty.collect_foralls();
            if foralls.is_empty() {
                self.session.insert_mono(variant.symbol, ty);
            } else {
                self.session.insert_term(
                    variant.symbol,
                    EnvEntry::Scheme(Scheme::<InferTy>::new(foralls, vec![], ty)),
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
            let mut predicates = vec![];
            let mut foralls = vec![];
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| {
                    let (ty, preds, fas) = self.infer_ast_ty_repr(f);
                    predicates.extend(preds);
                    foralls.extend(fas);
                    ty
                })
                .collect();
            let (ret, preds, fas) = self.infer_ast_ty_repr(&method.ret);

            predicates.extend(preds);
            foralls.extend(fas);

            let fn_ty = if params.is_empty() {
                InferTy::Func(Box::new(InferTy::Void), Box::new(ret.clone()))
            } else {
                curry(params.clone(), ret.clone())
            };

            let foralls = fn_ty.collect_foralls();

            if foralls.is_empty() {
                // No quantification necessary
                self.session.insert_mono(method.symbol, fn_ty);
            } else {
                use crate::types::{scheme::Scheme, term_environment::EnvEntry};
                self.session.insert_term(
                    method.symbol,
                    EnvEntry::Scheme(Scheme::<InferTy>::new(foralls, vec![], fn_ty)),
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
            let mut predicates = vec![];
            let mut foralls = vec![];
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| {
                    let (ty, preds, fas) = self.infer_ast_ty_repr(f);
                    predicates.extend(preds);
                    foralls.extend(fas);
                    ty
                })
                .collect();
            let (ret, preds, fas) = self.infer_ast_ty_repr(&method.ret);

            predicates.extend(preds);
            foralls.extend(fas);
            let fn_ty = if params.is_empty() {
                InferTy::Func(Box::new(InferTy::Void), Box::new(ret.clone()))
            } else {
                curry(params.clone(), ret.clone())
            };

            if foralls.is_empty() {
                self.session.insert_mono(method.symbol, fn_ty);
            } else {
                let self_ty = params
                    .first()
                    .expect("did not create `self` param for instance method");
                predicates.push(Predicate::Member {
                    receiver: self_ty.clone(),
                    label: name.clone(),
                    ty: fn_ty.clone(),
                });

                let scheme = EnvEntry::Scheme(Scheme::<InferTy>::new(foralls, predicates, fn_ty));

                println!(
                    "[resolve_instance_methods] promoting {:?}: {scheme:?}",
                    method.symbol
                );
                self.session.insert_term(method.symbol, scheme);
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

            let (ty, predicates, foralls) = self.infer_ast_ty_repr(&prop.ty_repr);

            if predicates.is_empty() && foralls.is_empty() {
                self.session.insert_mono(prop.symbol, ty);
            } else {
                self.session.insert_term(
                    prop.symbol,
                    EnvEntry::Scheme(Scheme {
                        foralls,
                        predicates,
                        ty,
                    }),
                );
            }
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
            let mut predicates = vec![];
            let mut foralls = vec![];

            let params: Vec<_> = init
                .params
                .iter()
                .map(|f| {
                    let (ty, preds, fas) = self.infer_ast_ty_repr(f);
                    predicates.extend(preds);
                    foralls.extend(fas);
                    ty
                })
                .collect();

            let ret = InferTy::Nominal {
                id: *type_id,
                row: Box::new(self.session.new_row_meta_var(Level(1))),
                type_args: vec![],
            };

            let ty = curry(params, ret);

            if foralls.is_empty() && predicates.is_empty() {
                self.session.insert_mono(init.symbol, ty);
            } else {
                self.session.insert_term(
                    init.symbol,
                    EnvEntry::Scheme(Scheme::<InferTy>::new(foralls, predicates, ty)),
                );
            }
            out.insert(label.clone(), init.symbol);
        }

        out
    }

    fn _resolve_associated_types(
        &mut self,
        protocol_id: ProtocolId,
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
            let mut predicates = vec![];
            let mut foralls = vec![];
            let params: Vec<_> = method
                .params
                .iter()
                .map(|f| {
                    let (ty, preds, fas) = self.infer_ast_ty_repr(f);
                    predicates.extend(preds);
                    foralls.extend(fas);
                    ty
                })
                .collect();

            let ret = if let Some(ret) = &method.ret {
                let (ty, preds, fas) = self.infer_ast_ty_repr(ret);
                predicates.extend(preds);
                foralls.extend(fas);
                ty
            } else {
                InferTy::Void
            };

            let fn_ty = curry(params.clone(), ret.clone());

            let entry = if predicates.is_empty() && foralls.is_empty() {
                EnvEntry::Mono(fn_ty)
            } else {
                EnvEntry::Scheme(Scheme {
                    foralls,
                    predicates,
                    ty: fn_ty,
                })
            };

            println!("about to promote {:?}: {entry:?}", method.symbol);
            self.session.insert_term(method.symbol, entry);

            println!("inserting {} -> {:?}", name, method.symbol);
            resolved_methods.insert(name.clone(), method.symbol);
        }
        resolved_methods
    }

    #[instrument(skip(self))]
    pub(crate) fn infer_type_annotation(
        &mut self,
        annotation: &TypeAnnotation,
    ) -> (InferTy, Vec<Predicate<InferTy>>, Vec<ForAll>) {
        match &annotation.kind {
            TypeAnnotationKind::SelfType(Name::Resolved(sym @ Symbol::Type(id), ..)) => {
                let mut predicates = vec![];
                let mut foralls = vec![];

                for generic in self
                    .raw
                    .type_constructors
                    .get(id)
                    .cloned()
                    .unwrap_or_else(|| {
                        panic!(
                            "did not get type for id: {id:?} in {:?}",
                            self.raw.type_constructors
                        )
                    })
                    .generics
                    .values()
                {
                    let (_, preds, fas) = self.infer_ast_ty_repr(generic);
                    predicates.extend(preds);
                    foralls.extend(fas);
                }

                let row = self.session.new_row_meta_var(Level(1)).into();
                let ty = InferTy::Nominal {
                    id: *id,
                    type_args: vec![],
                    row,
                };

                let entry: EnvEntry = (ty, predicates, foralls).into();
                self.session.insert_term(*sym, entry.clone());
                entry.into()
            }
            TypeAnnotationKind::SelfType(Name::Resolved(Symbol::Protocol(..), ..)) => {
                let Some(sym) = self.self_symbols.last() else {
                    unreachable!("didn't get self symbol for protocol");
                };

                self.session
                    .lookup(sym)
                    .expect("didn't get self entry")
                    .into()
            }
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
                let mut predicates = vec![];
                let mut foralls = vec![];

                // Check if this type parameter already has an entry
                let base = if let Some(entry) = self.session.lookup(sym) {
                    let (ty, preds, fas) = entry.into();
                    predicates.extend(preds);
                    foralls.extend(fas);
                    ty
                } else {
                    self.session.new_type_param()
                };

                for g in generics {
                    let (_, preds, fas) = self.infer_type_annotation(g);
                    predicates.extend(preds);
                    foralls.extend(fas);
                }

                let entry = (base, predicates, foralls);
                self.session.insert_term(*sym, entry.clone().into());
                entry
            }
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(Symbol::Protocol(..), ..),
                ..
            } => {
                // Protocols aren't values
                (InferTy::Void, vec![], vec![])
            }
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(sym @ Symbol::Type(..), ..),
                generics,
            } => {
                // Check if this is a generic parameter (from type defs or functions)
                let (base, mut predicates, mut foralls) =
                    if let Some(entry) = self.session.lookup(sym) {
                        // Type definition generic (e.g., struct Foo<T>)
                        entry.into()
                    } else if let Some(entry) = self.session.lookup(sym) {
                        // Function generic (e.g., func foo<T>)
                        entry.into()
                    } else {
                        // It's a type constructor
                        (self.session.new_ty_meta_var(Level(1)), vec![], vec![])
                    };

                // Apply generic arguments if any
                for g in generics {
                    let (_, preds, fas) = self.infer_type_annotation(g);
                    predicates.extend(preds);
                    foralls.extend(fas);
                }

                (base, predicates, foralls)
            }
            TypeAnnotationKind::NominalPath {
                box base,
                member: Label::Named(..),
                member_generics,
            } => {
                let (_, mut predicates, mut foralls) = self.infer_type_annotation(base);
                let result = self.session.new_type_param();

                let InferTy::Param(id) = &result else {
                    unreachable!()
                };

                foralls.push(ForAll::Ty(*id));

                for g in member_generics {
                    let (_, preds, fas) = self.infer_type_annotation(g);
                    predicates.extend(preds);
                    foralls.extend(fas);
                }

                (result, predicates, foralls)
            }
            TypeAnnotationKind::Nominal {
                name: Name::Resolved(Symbol::AssociatedType(assoc_id), _),
                ..
            } => {
                let Some(Symbol::Protocol(protocol_id)) = self.self_symbols.last().cloned() else {
                    println!("nope");
                    unreachable!("didn't get protocol id");
                };

                let Some(self_symbol) = self.self_symbols.last().cloned() else {
                    unreachable!("didn't get self_symbol");
                };

                let result = self.session.new_type_param();

                let (self_ty, mut predicates, mut foralls) = self
                    .session
                    .lookup(&self_symbol)
                    .expect("didn't get protocol self")
                    .into();

                // Store predicate indexed by the type parameter (Self)
                if let InferTy::Param(..) = self_ty {
                    predicates.push(Predicate::AssociatedEquals {
                        subject: self_ty.clone(),
                        protocol_id,
                        associated_type_id: *assoc_id,
                        output: result.clone(),
                    });
                }

                // Add the result type parameter to the foralls list
                if let InferTy::Param(param_id) = result.clone() {
                    foralls.push(ForAll::Ty(param_id));
                }

                // Update the Self symbol's entry to include the new predicate and forall
                let updated_self_entry = (self_ty.clone(), predicates.clone(), foralls.clone());
                self.session
                    .insert_term(self_symbol, updated_self_entry.into());

                // Return the result type for this associated type reference
                (result, predicates, foralls)
            }
            TypeAnnotationKind::Record { fields } => {
                let mut row = InferRow::Empty(TypeDefKind::Struct);
                let mut predicates = vec![];
                let mut foralls = vec![];
                for field in fields.iter().rev() {
                    let (ty, preds, fas) = self.infer_type_annotation(&field.value);
                    predicates.extend(preds);
                    foralls.extend(fas);

                    row = InferRow::Extend {
                        row: Box::new(row),
                        label: field.label.name_str().into(),
                        ty,
                    };
                }

                (InferTy::Record(Box::new(row)), predicates, foralls)
            }
            _ => unreachable!("unhandled type annotation: {annotation:?}"),
        }
    }

    pub(crate) fn infer_ast_ty_repr(
        &mut self,
        ty_repr: &ASTTyRepr,
    ) -> (InferTy, Vec<Predicate<InferTy>>, Vec<ForAll>) {
        match &ty_repr {
            ASTTyRepr::Annotated(annotation) => self.infer_type_annotation(annotation),
            ASTTyRepr::SelfType(..) => {
                if let Some(sym) = self.self_symbols.last()
                    && let Some(entry) = self.session.lookup(sym)
                {
                    return entry.into();
                }

                panic!("didn't get self type for protocol");
            }
            ASTTyRepr::Hole(id, ..) => (InferTy::Hole(*id), vec![], vec![]),
            ASTTyRepr::Generic(decl) => self.infer_generic_decl(decl),
        }
    }

    fn infer_generic_decl(
        &mut self,
        decl: &GenericDecl,
    ) -> (InferTy, Vec<Predicate<InferTy>>, Vec<ForAll>) {
        let ty = self.session.new_type_param();

        let InferTy::Param(id) = ty else {
            unreachable!();
        };

        let mut predicates: Vec<Predicate<InferTy>> = vec![];
        let mut foralls: Vec<ForAll> = vec![ForAll::Ty(id)];

        for generic in decl.generics.iter() {
            let (_, preds, fas) = self.infer_generic_decl(generic);
            predicates.extend(preds);
            foralls.extend(fas);
        }

        let entry = (ty, predicates, foralls);
        self.session
            .insert_term(decl.name.symbol().unwrap(), entry.clone().into());
        entry
    }
}

#[cfg(test)]
pub mod tests {

    use std::rc::Rc;

    use indexmap::indexmap;

    use crate::{
        assert_eq_diff,
        ast::AST,
        compiling::module::{ModuleEnvironment, ModuleId},
        fxhashmap,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{
                AssociatedTypeId, InstanceMethodId, PropertyId, ProtocolId, StaticMethodId,
                SynthesizedId, TypeId,
            },
        },
        span::Span,
        types::{
            passes::{dependencies_pass::Conformance, type_headers_pass::TypeHeaderPass},
            type_catalog::ConformanceKey,
        },
    };

    use super::*;

    pub fn type_header_resolve_pass(code: &'static str) -> (AST<NameResolved>, TypeSession) {
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
    ) -> Result<(AST<NameResolved>, TypeSession), TypeError> {
        let mut resolved = resolve(code);
        let modules = ModuleEnvironment::default();
        let mut session = TypeSession::new(Rc::new(modules));
        let raw = TypeHeaderPass::drive(&mut session, &resolved);
        _ = TypeResolvePass::drive(&mut resolved, &mut session, raw);
        Ok((resolved, session))
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
                .type_catalog
                .nominals
                .get(&TypeId::from(1).into())
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1))),
                properties: indexmap! {
                    "age".into() => Symbol::Property(PropertyId::from(1))
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
                .type_catalog
                .nominals
                .get(&TypeId::from(1).into())
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1))),
                properties: Default::default(),
                instance_methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::InstanceMethod(InstanceMethodId::from(1))),
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
                .type_catalog
                .nominals
                .get(&TypeId::from(1).into())
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1))),
                properties: Default::default(),
                instance_methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::InstanceMethod(InstanceMethodId::from(1))),
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
                .type_catalog
                .nominals
                .get(&TypeId::from(1).into())
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1))),
                properties: Default::default(),
                instance_methods: Default::default(),
                static_methods: fxhashmap!(Label::Named("fizz".into()) => Symbol::StaticMethod(StaticMethodId::from(1))),
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
                .type_catalog
                .nominals
                .get(&TypeId::from(1).into())
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1))),
                properties: indexmap! { "t".into() => Symbol::Property(PropertyId::from(1)) },
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
                .type_catalog
                .nominals
                .get(&TypeId::from(3).into())
                .unwrap()
                .form,
            NominalForm::Struct {
                initializers: fxhashmap!(Label::Named("init".into()) => Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 3))),
                properties: indexmap! {
                    "b".into() => Symbol::Property(PropertyId::from(3))
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
                .type_catalog
                .conformances
                .get(&ConformanceKey {
                    protocol_id: ProtocolId::from(1),
                    conforming_id: TypeId::from(1).into(),
                })
                .unwrap_or_else(|| panic!("didn't get conformance: {:?}", session)),
            Conformance {
                conforming_id: TypeId::from(1).into(),
                protocol_id: ProtocolId::from(1),
                requirements: fxhashmap!("count".into() => ConformanceRequirement::Unfulfilled(Symbol::InstanceMethod(InstanceMethodId::from(1)))),
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
                .type_catalog
                .nominals
                .get(&TypeId::from(1).into())
                .unwrap()
                .child_types,
            fxhashmap!("Buzz".to_string() => Symbol::Type(TypeId::from(2)), "Foo".into() => Symbol::Type(TypeId::from(3)))
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
                .type_catalog
                .conformances
                .get(&ConformanceKey {
                    protocol_id: ProtocolId::from(1),
                    conforming_id: TypeId::from(1).into()
                })
                .unwrap_or_else(|| panic!("didn't get conformance: {:?}", session)),
            Conformance {
                conforming_id: TypeId::from(1).into(),
                protocol_id: ProtocolId::from(1),
                requirements: fxhashmap!(
                    "getA".into() => ConformanceRequirement::Unfulfilled(Symbol::InstanceMethod(InstanceMethodId::from(1))),
                    "setA".into() => ConformanceRequirement::Unfulfilled(Symbol::InstanceMethod(InstanceMethodId::from(2)))
                ),
                span: Span::ANY,
                associated_types: fxhashmap!(AssociatedTypeId::from(1) => Symbol::Type(TypeId::from(2)))
            }
        )
    }

    #[test]
    fn resolves_nominal_path_annotations() {
        let (ast, session) = type_header_resolve_pass(
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

        // no errors during header/resolve
        assert!(ast.diagnostics.is_empty(), "{:?}", ast.diagnostics);

        let c_nominal = session
            .type_catalog
            .nominals
            .get(&TypeId::from(1).into())
            .expect("missing C");
        let a_nominal = session
            .type_catalog
            .nominals
            .get(&TypeId::from(3).into())
            .expect("missing A");

        // child types are registered: C.B and A.B exist and are reachable by name
        assert!(c_nominal.child_types.contains_key("B"), "C.B not recorded");
        assert!(a_nominal.child_types.contains_key("B"), "A.B not recorded");

        // properties `a` (in C) and `c` (in A) exist in the catalog
        match &c_nominal.form {
            NominalForm::Struct { properties, .. } => {
                assert!(
                    properties.contains_key(&Label::Named("a".into())),
                    "C missing property `a`"
                );
            }
            _ => panic!("C should be a struct"),
        }
        match &a_nominal.form {
            NominalForm::Struct { properties, .. } => {
                assert!(
                    properties.contains_key(&Label::Named("c".into())),
                    "A missing property `c`"
                );
            }
            _ => panic!("A should be a struct"),
        }
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
        let (_ast, mut session) = resolved;

        // Sanity: protocol + type exist
        assert!(
            session
                .type_catalog
                .protocols
                .contains_key(&ProtocolId::from(1)),
            "Aged protocol missing"
        );
        assert!(
            session
                .type_catalog
                .nominals
                .contains_key(&TypeId::from(1).into()),
            "Wrapper type missing"
        );

        // Grab the instance method symbol for `use`
        let method_sym = Symbol::InstanceMethod(InstanceMethodId::from(1));
        let entry = session
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
        // Protocol id is Aged (TypeId::from(1)), associated id is T (AssociatedTypeId::from(1))
        for (subject, pid, aid, _out) in assoc_preds.iter() {
            assert!(
                matches!(subject, crate::types::infer_ty::InferTy::Param(_)),
                "subject should be Ty::Param for U, got {:?}",
                subject
            );
            assert_eq!(*pid, ProtocolId::from(1), "protocol id should be Aged");
            assert_eq!(*aid, AssociatedTypeId::from(1), "associated id should be T");
        }
    }
}
