use crate::{
    ast::AST,
    compiling::driver::Source,
    label::Label,
    name::Name,
    name_resolution::{name_resolver::NameResolved, symbol::Symbol},
    node::Node,
    node_id::NodeID,
    node_kinds::{
        block::Block,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
    types::{
        fields::{Associated, Initializer, Method, MethodRequirement, Property, Variant},
        kind::Kind,
        type_catalog::ConformanceStub,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeExtension},
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

// Gathers up all the raw types from the AST
#[derive(Debug, Visitor)]
#[visitor(Decl, Expr(enter), TypeAnnotation(enter))]
pub struct TypeHeaderPass<'a> {
    type_stack: Vec<Symbol>,
    raw: &'a mut Raw,
    annotations: FxHashMap<NodeID, ASTTyRepr>,
}

impl<'a> TypeHeaderPass<'a> {
    pub fn drive(ast: &AST<NameResolved>) -> Raw {
        let mut raw = Raw::default();

        let mut instance = TypeHeaderPass {
            type_stack: Default::default(),
            raw: &mut raw,
            annotations: Default::default(),
        };

        for root in ast.roots.iter() {
            root.drive(&mut instance);
        }

        instance.raw.annotations = std::mem::take(&mut instance.annotations);

        raw
    }

    pub fn drive_all(asts: &IndexMap<Source, AST<NameResolved>>) -> Raw {
        let mut raw = Raw::default();

        for ast in asts.values() {
            let file_raw = TypeHeaderPass::drive(ast);
            raw.type_constructors.extend(file_raw.type_constructors);
            raw.protocols.extend(file_raw.protocols);
            raw.annotations.extend(file_raw.annotations);
            raw.typealiases.extend(file_raw.typealiases);
            raw.extensions.extend(file_raw.extensions);

            // Merge nested maps for instance_methods
            for (symbol, methods) in file_raw.instance_methods {
                raw.instance_methods
                    .entry(symbol)
                    .or_default()
                    .extend(methods);
            }

            // Merge nested maps for static_methods
            for (symbol, methods) in file_raw.static_methods {
                raw.static_methods
                    .entry(symbol)
                    .or_default()
                    .extend(methods);
            }

            // Merge nested maps for initializers
            for (symbol, inits) in file_raw.initializers {
                raw.initializers.entry(symbol).or_default().extend(inits);
            }

            // Merge nested maps for properties
            for (symbol, props) in file_raw.properties {
                raw.properties.entry(symbol).or_default().extend(props);
            }

            // Merge nested maps for method_requirements
            for (symbol, reqs) in file_raw.method_requirements {
                raw.method_requirements
                    .entry(symbol)
                    .or_default()
                    .extend(reqs);
            }

            // Merge nested maps for associated_types
            for (symbol, types) in file_raw.associated_types {
                raw.associated_types
                    .entry(symbol)
                    .or_default()
                    .extend(types);
            }

            // Merge nested maps for variants
            for (symbol, vars) in file_raw.variants {
                raw.variants.entry(symbol).or_default().extend(vars);
            }

            // Merge nested maps for generics
            for (symbol, generics) in file_raw.generics {
                raw.generics.entry(symbol).or_default().extend(generics);
            }

            // Merge nested maps for conformances
            for (symbol, conformances) in file_raw.conformances {
                raw.conformances
                    .entry(symbol)
                    .or_default()
                    .extend(conformances);
            }

            // Merge nested maps for child_types
            for (symbol, children) in file_raw.child_types {
                raw.child_types.entry(symbol).or_default().extend(children);
            }
        }

        raw
    }

    fn enter_type_annotation(&mut self, annotation: &TypeAnnotation) {
        tracing::warn!("stashing annotation: {annotation:?}");

        if matches!(
            &annotation.kind,
            TypeAnnotationKind::SelfType(..)
                | TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::AssociatedType(..), ..),
                    ..
                }
        ) {
            return;
        }

        self.annotations
            .insert(annotation.id, ASTTyRepr::Annotated(annotation.clone()));
    }

    fn enter_expr(&mut self, expr: &Expr) {
        if let Expr {
            kind: ExprKind::Call { type_args, .. },
            ..
        } = expr
        {
            for arg in type_args {
                self.annotations
                    .insert(arg.id, ASTTyRepr::Annotated(arg.clone()));
            }
        }

        if let Expr {
            kind:
                ExprKind::Func(Func {
                    generics,
                    params,
                    ret,
                    ..
                }),
            ..
        } = expr
        {
            if let Some(ret) = ret {
                self.annotations
                    .insert(ret.id, ASTTyRepr::Annotated(ret.clone()));
            }

            for generic in generics {
                self.annotations
                    .insert(generic.id, ASTTyRepr::Generic(generic.clone()));
            }

            for param in params {
                if let Some(annotation) = &param.type_annotation {
                    self.annotations
                        .insert(annotation.id, ASTTyRepr::Annotated(annotation.clone()));
                }
            }
        }
    }

    fn enter_decl(&mut self, decl: &Decl) {
        match &decl.kind {
            DeclKind::Struct {
                name: name @ Name::Resolved(sym @ Symbol::Struct(..), type_name),
                generics,
                body: Block { body, .. },
                conformances,
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.raw
                        .child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);

                self.raw
                    .conformances
                    .entry(*sym)
                    .or_default()
                    .extend(Self::collect_conformance_stubs(*sym, conformances));

                self.raw.generics.entry(*sym).or_default().extend(
                    generics
                        .iter()
                        .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                        .collect::<IndexMap<Name, ASTTyRepr>>(),
                );

                self.collect_fields(name, decl.id, body);
                self.raw.type_constructors.insert(
                    *sym,
                    TypeDef {
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Struct,
                    },
                );
            }
            DeclKind::Extend {
                name:
                    name @ Name::Resolved(sym @ (Symbol::Struct(..) | Symbol::Enum(..)), type_name),
                body: Block { body, .. },
                conformances,
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.raw
                        .child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);
                self.collect_fields(name, decl.id, body);

                self.raw
                    .conformances
                    .entry(*sym)
                    .or_default()
                    .extend(Self::collect_conformance_stubs(*sym, conformances));

                self.raw
                    .extensions
                    .entry(*sym)
                    .or_default()
                    .push(TypeExtension { node_id: decl.id });
            }
            DeclKind::Extend {
                name: name @ Name::Resolved(sym @ Symbol::Builtin(builtin_id), ..),
                body: Block { body, .. },
                conformances,
                ..
            } => {
                self.type_stack.push(*sym);
                self.collect_fields(name, decl.id, body);

                self.raw
                    .conformances
                    .entry(*sym)
                    .or_default()
                    .extend(Self::collect_conformance_stubs(*sym, conformances));

                self.raw
                    .extensions
                    .entry(Symbol::Builtin(*builtin_id))
                    .or_default()
                    .push(TypeExtension { node_id: decl.id });
            }
            DeclKind::Protocol {
                name: name @ Name::Resolved(sym @ Symbol::Protocol(protocol_id), type_name),
                generics,
                conformances,
                body: Block { body, .. },
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.raw
                        .child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);
                self.collect_fields(name, decl.id, body);

                self.raw
                    .conformances
                    .entry(*sym)
                    .or_default()
                    .extend(Self::collect_conformance_stubs(*sym, conformances));

                self.raw.generics.entry(*sym).or_default().extend(
                    generics
                        .iter()
                        .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                        .collect::<IndexMap<Name, ASTTyRepr>>(),
                );

                self.raw.protocols.insert(
                    *protocol_id,
                    TypeDef {
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Protocol,
                    },
                );
            }
            DeclKind::Enum {
                name: name @ Name::Resolved(sym @ Symbol::Enum(..), type_name),
                body: Block { body, .. },
                generics,
                conformances,
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.raw
                        .child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);
                self.collect_fields(name, decl.id, body);

                self.raw
                    .conformances
                    .entry(*sym)
                    .or_default()
                    .extend(Self::collect_conformance_stubs(*sym, conformances));

                self.raw.generics.entry(*sym).or_default().extend(
                    generics
                        .iter()
                        .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                        .collect::<FxHashMap<Name, ASTTyRepr>>(),
                );

                self.raw.type_constructors.insert(
                    *sym,
                    TypeDef {
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Enum,
                    },
                );
            }
            DeclKind::Associated {
                generic:
                    GenericDecl {
                        name: Name::Resolved(sym, name),
                        ..
                    },
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.raw
                        .child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(name.to_string(), *sym);
                }
            }

            DeclKind::TypeAlias(
                TypeAnnotation {
                    kind:
                        TypeAnnotationKind::Nominal {
                            name: name @ Name::Resolved(sym, type_name),
                            ..
                        },
                    ..
                },
                rhs,
            ) => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.raw
                        .child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.raw
                    .typealiases
                    .entry(decl.id)
                    .or_insert((name.clone(), rhs.clone()));
                self.annotations
                    .insert(rhs.id, ASTTyRepr::Annotated(rhs.clone()));
            }
            DeclKind::Let {
                type_annotation: Some(annotation),
                ..
            } => {
                self.annotations
                    .insert(annotation.id, ASTTyRepr::Annotated(annotation.clone()));
            }
            _ => (),
        }
    }

    fn exit_decl(&mut self, decl: &Decl) {
        if matches!(
            &decl.kind,
            DeclKind::Struct { .. }
                | DeclKind::Enum { .. }
                | DeclKind::Extend { .. }
                | DeclKind::Protocol { .. }
        ) {
            self.type_stack.pop();
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Helpers
    ///////////////////////////////////////////////////////////////////////////

    fn collect_conformance_stubs(
        conforming_id: Symbol,
        conformances: &[TypeAnnotation],
    ) -> Vec<ConformanceStub> {
        conformances
            .iter()
            .map(|c| {
                let TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Protocol(protocol_id), _),
                    ..
                } = &c.kind
                else {
                    unreachable!();
                };

                ConformanceStub {
                    conforming_id,
                    protocol_id: *protocol_id,
                    span: c.span,
                }
            })
            .collect()
    }

    fn collect_fields(&mut self, type_name: &Name, id: NodeID, body: &[Node]) {
        // Collect properties
        let mut properties: IndexMap<Label, Property> = Default::default();
        let mut instance_methods: IndexMap<Label, Method> = Default::default();
        let mut static_methods: IndexMap<Label, Method> = Default::default();
        let mut initializers: IndexMap<Label, Initializer> = Default::default();
        let mut variants: IndexMap<Label, Variant> = Default::default();
        let mut associated_types: FxHashMap<Name, Associated> = Default::default();
        let mut method_requirements: IndexMap<Label, MethodRequirement> = Default::default();

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
                DeclKind::EnumVariant(variant_name, .., values) => {
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
                    let Name::Resolved(Symbol::Protocol(type_id), _) = &type_name else {
                        unreachable!("didn't resolve type");
                    };

                    associated_types.insert(
                        generic.name.clone(),
                        Associated {
                            protocol_id: *type_id,
                            symbol: generic.name.symbol().unwrap(),
                        },
                    );
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
                    generics,
                    params,
                    ret,
                    ..
                }) => {
                    method_requirements.insert(
                        name.into(),
                        MethodRequirement {
                            id,
                            symbol: *symbol,
                            generics: generics
                                .iter()
                                .map(|g| ASTTyRepr::Generic(g.clone()))
                                .collect(),
                            params: params
                                .iter()
                                .enumerate()
                                .map(|(i, p)| {
                                    if i == 0 {
                                        ASTTyRepr::SelfType(type_name.clone(), p.id, *span)
                                    } else if let Some(ann) = &p.type_annotation {
                                        ASTTyRepr::Annotated(ann.clone())
                                    } else {
                                        ASTTyRepr::Hole(p.id, *span)
                                    }
                                })
                                .collect(),
                            ret: ret.as_ref().map(|r| ASTTyRepr::Annotated(*r.clone())),
                        },
                    );
                }
                DeclKind::Init { name, params, .. } => {
                    let Name::Resolved(Symbol::Struct(type_id), _) = &type_name else {
                        unreachable!("didn't resolve type");
                    };
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

        let methods = self
            .raw
            .instance_methods
            .entry(type_name.symbol().unwrap())
            .or_default();
        methods.extend(instance_methods);

        let methods = self
            .raw
            .static_methods
            .entry(type_name.symbol().unwrap())
            .or_default();
        methods.extend(static_methods);

        let inits = self
            .raw
            .initializers
            .entry(type_name.symbol().unwrap())
            .or_default();
        inits.extend(initializers);

        let props = self
            .raw
            .properties
            .entry(type_name.symbol().unwrap())
            .or_default();
        props.extend(properties);

        let vars = self
            .raw
            .variants
            .entry(type_name.symbol().unwrap())
            .or_default();
        vars.extend(variants);

        let reqs = self
            .raw
            .method_requirements
            .entry(type_name.symbol().unwrap())
            .or_default();
        reqs.extend(method_requirements);

        let associates = self
            .raw
            .associated_types
            .entry(type_name.symbol().unwrap())
            .or_default();
        associates.extend(associated_types);
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{
        annotation, any, assert_eq_diff,
        ast::AST,
        compiling::module::ModuleId,
        fxhashmap,
        label::Label,
        name::Name,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{
                AssociatedTypeId, BuiltinId, EnumId, GlobalId, InstanceMethodId, PropertyId,
                ProtocolId, StructId, Symbol, SynthesizedId, TypeParameterId, VariantId,
            },
        },
        node::Node,
        node_id::{FileID, NodeID},
        node_kinds::{generic_decl::GenericDecl, type_annotation::*},
        span::Span,
        types::{
            fields::{Associated, Initializer, MethodRequirement, Property, Variant},
            kind::Kind,
            passes::type_headers_pass::TypeHeaderPass,
            type_catalog::ConformanceStub,
            type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeExtension},
        },
    };

    pub fn type_header_decl_pass(code: &'static str) -> (AST<NameResolved>, Raw) {
        let resolved = resolve(code);
        let raw = TypeHeaderPass::drive(&resolved);
        (resolved, raw)
    }

    #[test]
    fn basic_struct() {
        let raw = type_header_decl_pass(
            "
        struct Person {
            let age: Int
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *raw.initializers
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            fxhashmap! {
                Label::Named("init".into()) => Initializer {
                    symbol: Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1)),
                    initializes_type_id: StructId::from(1),
                    params: vec![
                        ASTTyRepr::SelfType(Name::Resolved(StructId::from(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                        ASTTyRepr::Annotated(
                            annotation!(
                                TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(Symbol::Int, "Int".into()),
                                    name_span: Span::ANY,
                                    generics: vec!{}
                                }
                            )
                        )
                    ]
                }
            }
        );

        assert_eq_diff!(
            *raw.properties
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            crate::indexmap!(Label::Named("age".into()) => Property {
                symbol: Symbol::Property(PropertyId::from(1)),
                is_static: false,
                ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Builtin(BuiltinId::new(crate::compiling::module::ModuleId::Builtin, 1)), "Int".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                })),
            })
        );

        assert_eq_diff!(
            *raw.type_constructors
                .get(&StructId::from(1).into())
                .unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
            }
        );
    }

    #[test]
    fn struct_extension() {
        let raw = type_header_decl_pass(
            "
        struct Person {}
        extend Person {}
        ",
        )
        .1;

        assert_eq!(
            *raw.extensions
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            vec![TypeExtension {
                node_id: NodeID::ANY,
            }]
        );

        assert_eq_diff!(
            *raw.type_constructors
                .get(&StructId::from(1).into())
                .unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
            }
        );
    }

    #[test]
    fn generic_struct() {
        let raw = type_header_decl_pass(
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
            *raw.initializers
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            fxhashmap!(Label::Named("init".into()) => Initializer {
                symbol: Symbol::Global(GlobalId::from(1)),
                initializes_type_id: StructId::from(1),
                params: vec![
                    ASTTyRepr::SelfType(Name::Resolved(Symbol::Struct(StructId::from(1)), "Wrapper".into()), NodeID::ANY, Span::ANY),
                    ASTTyRepr::Hole(NodeID(FileID(0), 4), Span::ANY)
                ]
            })
        );

        assert_eq_diff!(
            *raw.properties
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            crate::indexmap!(Label::Named("wrapped".into()) => Property {
                symbol: Symbol::Property(PropertyId::from(1)),
                is_static: false,
                ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                }))
            })
        );

        assert_eq_diff!(
            *raw.generics
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            crate::indexmap!(Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()) => ASTTyRepr::Generic(GenericDecl {
                id: NodeID::ANY,
                name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                name_span: Span::ANY,
                generics: vec![],
                conformances: vec![],
                span: Span::ANY,
            }))
        );

        assert_eq_diff!(
            *raw.type_constructors
                .get(&StructId::from(1).into())
                .unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Box::new(Kind::Type)
                },
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
            }
        );
    }

    #[test]
    fn nested_generic_struct() {
        let raw = type_header_decl_pass(
            "
        struct Wrapper<T, U> {
            let wrapped: T<U>
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *raw.initializers
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            fxhashmap!(Label::Named("init".into()) => Initializer {
                symbol: Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1)),
                initializes_type_id: StructId::from(1),
                params: vec![
                ASTTyRepr::SelfType(Name::Resolved(StructId::from(1).into(), "Wrapper".into()), NodeID::ANY, Span::ANY),
                ASTTyRepr::Annotated(
                    annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()), name_span: Span::ANY, generics: vec![
                    annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(TypeParameterId(2).into(), "U".into()), name_span: Span::ANY, generics: vec![] })
                ] }))
                ]
            })
        );

        assert_eq_diff!(
            *raw.properties
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            crate::indexmap!(Label::Named("wrapped".into()) => Property {
                symbol: Symbol::Property(PropertyId::from(1)),
                is_static: false,
                ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(2)), "U".into()),
                        name_span: Span::ANY,
                        generics: vec![]
                    })]
                }))
            })
        );

        assert_eq!(
            *raw.generics
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            crate::indexmap!(
              Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()) =>  ASTTyRepr::Generic(GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY,
                }),
               Name::Resolved(Symbol::TypeParameter(TypeParameterId(2)), "U".into()) => ASTTyRepr::Generic(GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(2)), "U".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY,
                })
            )
        );

        assert_eq_diff!(
            *raw.type_constructors
                .get(&StructId::from(1).into())
                .unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Wrapper".into()),
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
            }
        );
    }

    #[test]
    fn basic_enum() {
        let raw = type_header_decl_pass(
            "
        enum Fizz {
            case foo(Int), bar
        }
        ",
        )
        .1;

        assert_eq!(
            *raw.variants.get(&Symbol::Enum(EnumId::from(1))).unwrap(),
            crate::indexmap!(
                Label::Named("foo".into()) => Variant {
                    symbol: Symbol::Variant(VariantId::from(1)),
                    tag: "foo".into(),
                    fields: vec![ASTTyRepr::Annotated(annotation!(
                        TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Int, "Int".into()),
                            name_span: Span::ANY,
                            generics: vec![]
                        }
                    ))]
                },
                "bar".into() =>  Variant { symbol: Symbol::Variant(VariantId::from(2)), tag: "bar".into(), fields: vec![] }
            )
        );

        assert_eq_diff!(
            *raw.type_constructors.get(&EnumId::from(1).into()).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Enum(EnumId::from(1)), "Fizz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Enum,
            }
        );
    }

    #[test]
    fn basic_protocol() {
        let raw = type_header_decl_pass(
            "
        protocol Fizz {
            associated Buzz

            func foo<G>(g: G) -> Int
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *raw.method_requirements
                .get(&Symbol::Protocol(ProtocolId::from(1)))
                .unwrap(),
            crate::indexmap!(Label::Named("foo".into()) => MethodRequirement {
                id: NodeID::ANY,
                symbol: Symbol::InstanceMethod(InstanceMethodId::from(1)),
                generics: vec![
                    ASTTyRepr::Generic(any!(GenericDecl, {
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId::from(1u32)), "G".into()),
                        name_span: Span::ANY,
                        generics: vec![],
                        conformances: vec![],
                    }))
                ],
                params: vec![
                    ASTTyRepr::SelfType(
                        Name::Resolved(ProtocolId::from(1).into(), "Fizz".into()),
                        NodeID::ANY,
                        Span::ANY,
                    ),
                    ASTTyRepr::Annotated(
                        annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(TypeParameterId::from(1u32).into(), "G".into()),
                            name_span: Span::ANY,
                            generics: vec![],
                        })
                    )
                ],
                ret: Some(ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Int, "Int".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                })))
            })
        );
        assert_eq_diff!(
            *raw.associated_types
                .get(&Symbol::Protocol(ProtocolId::from(1)))
                .unwrap(),
            crate::indexmap!(Name::Resolved(Symbol::AssociatedType(AssociatedTypeId::from(1)), "Buzz".into()) => Associated {
                protocol_id: ProtocolId::from(1),
                symbol: Symbol::AssociatedType(AssociatedTypeId::from(1))
            })
        );

        assert_eq_diff!(
            *raw.protocols.get(&ProtocolId::from(1)).unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Protocol(ProtocolId::from(1)), "Fizz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Protocol,
            }
        );
    }

    #[test]
    fn basic_conformance() {
        let raw = type_header_decl_pass(
            "
        protocol Fizz {}
        struct Buzz: Fizz {}
        ",
        )
        .1;

        assert_eq_diff!(
            *raw.initializers
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            fxhashmap!(Label::Named("init".into()) => Initializer {
                symbol: Symbol::Synthesized(SynthesizedId::new(ModuleId::Current, 1)),
                initializes_type_id: StructId::from(1),
                params: vec![
                    ASTTyRepr::SelfType(
                        Name::Resolved(Symbol::Struct(StructId::from(1)), "Buzz".into()),
                        NodeID::ANY,
                        Span::ANY
                    ),
                ]
            })
        );

        assert_eq!(
            *raw.conformances.get(&StructId::from(1).into()).unwrap(),
            vec![ConformanceStub {
                conforming_id: StructId::from(1).into(),
                protocol_id: ProtocolId::from(1),
                span: Span::ANY,
            }]
        );

        assert_eq_diff!(
            *raw.type_constructors
                .get(&StructId::from(1).into())
                .unwrap(),
            TypeDef {
                name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Buzz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
            }
        );
    }

    #[test]
    fn global_let() {
        let (ast, raw) = type_header_decl_pass(
            "
        let x: Int = 123
        ",
        );

        assert!(matches!(
            ast.find(NodeID(FileID(0), 2)).unwrap(),
            Node::TypeAnnotation(TypeAnnotation { .. })
        ));

        assert_eq!(
            *raw.annotations.get(&NodeID(FileID(0), 2)).unwrap(),
            ASTTyRepr::Annotated(TypeAnnotation {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Int, "Int".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                }
            })
        );
    }

    #[test]
    fn global_func() {
        let (ast, raw) = type_header_decl_pass(
            "
        func fizz<T>(t: T) {}
        ",
        );

        assert!(matches!(
            ast.find(NodeID(FileID(0), 2)).unwrap(),
            Node::TypeAnnotation(TypeAnnotation { .. })
        ));

        assert_eq!(
            *raw.annotations.get(&NodeID(FileID(0), 2)).unwrap(),
            ASTTyRepr::Annotated(TypeAnnotation {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                }
            })
        );
    }
}
