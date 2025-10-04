use crate::{
    ast::AST,
    label::Label,
    name::Name,
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, SynthesizedId, TypeId},
    },
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
    span::Span,
    types::{
        fields::{
            Associated, Initializer, Method, MethodRequirement, Property, TypeFields, Variant,
        },
        kind::Kind,
        type_catalog::ConformanceStub,
        type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeExtension, TypeSession},
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
    child_types: FxHashMap<Symbol, FxHashMap<String, Symbol>>,
    session: &'a mut TypeSession<Raw>,
    extensions: FxHashMap<TypeId, Vec<TypeExtension>>,
    annotations: FxHashMap<NodeID, ASTTyRepr>,
    typealiases: FxHashMap<NodeID, (Name, TypeAnnotation)>,
}

impl<'a> TypeHeaderPass<'a> {
    pub fn drive(session: &'a mut TypeSession<Raw>, ast: &AST<NameResolved>) {
        let mut instance = TypeHeaderPass {
            type_stack: Default::default(),
            session,
            child_types: Default::default(),
            extensions: Default::default(),
            annotations: Default::default(),
            typealiases: Default::default(),
        };

        for root in ast.roots.iter() {
            root.drive(&mut instance);
        }

        instance.session.phase.annotations = std::mem::take(&mut instance.annotations);
        instance.session.phase.typealiases = std::mem::take(&mut instance.typealiases);

        let mut extensions = std::mem::take(&mut instance.extensions);
        for (id, type_constructor) in instance.session.phase.type_constructors.iter_mut() {
            type_constructor.child_types = instance
                .child_types
                .get(&type_constructor.name.symbol().unwrap())
                .cloned()
                .unwrap_or_default();

            if let Some(mut extensions) = extensions.remove(id) {
                type_constructor.conformances = extensions
                    .iter_mut()
                    .flat_map(|e| std::mem::take(&mut e.conformances))
                    .collect();
                type_constructor.extensions = extensions;
            }
        }
    }

    fn enter_type_annotation(&mut self, annotation: &TypeAnnotation) {
        tracing::warn!("stashing annotation: {annotation:?}");

        if matches!(
            &annotation.kind,
            TypeAnnotationKind::Nominal {
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
                name: name @ Name::Resolved(sym @ Symbol::Type(type_id), type_name),
                generics,
                body: Block { body, .. },
                conformances,
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);

                let fields =
                    self.collect_fields(name, decl.id, decl.span, TypeDefKind::Struct, body);
                self.session.phase.type_constructors.insert(
                    *type_id,
                    TypeDef {
                        extensions: Default::default(),
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Struct,
                        conformances: Self::collect_conformance_stubs(*sym, conformances),
                        child_types: Default::default(),
                        generics: generics
                            .iter()
                            .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                            .collect(),
                        fields,
                    },
                );
            }
            DeclKind::Extend {
                name: name @ Name::Resolved(sym @ Symbol::Type(type_id), type_name),
                body: Block { body, .. },
                conformances,
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);

                let TypeFields::Extension {
                    static_methods,
                    instance_methods: methods,
                } = self.collect_fields(name, decl.id, decl.span, TypeDefKind::Extension, body)
                else {
                    unreachable!()
                };

                self.extensions
                    .entry(*type_id)
                    .or_default()
                    .push(TypeExtension {
                        node_id: decl.id,
                        conformances: Self::collect_conformance_stubs(*sym, conformances),
                        methods,
                        static_methods,
                    });
            }
            DeclKind::Protocol {
                name: name @ Name::Resolved(sym @ Symbol::Protocol(protocol_id), type_name),
                generics,
                conformances,
                body: Block { body, .. },
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);

                let fields =
                    self.collect_fields(name, decl.id, decl.span, TypeDefKind::Protocol, body);

                self.session.phase.protocols.insert(
                    *protocol_id,
                    TypeDef {
                        extensions: Default::default(),
                        child_types: Default::default(),
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Protocol,
                        conformances: Self::collect_conformance_stubs(*sym, conformances),
                        generics: generics
                            .iter()
                            .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                            .collect(),
                        fields,
                    },
                );
            }
            DeclKind::Enum {
                name: name @ Name::Resolved(sym @ Symbol::Type(type_id), type_name),
                body: Block { body, .. },
                generics,
                conformances,
                ..
            } => {
                if let Some(parent_id) = self.type_stack.last() {
                    self.child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.type_stack.push(*sym);

                let fields = self.collect_fields(name, decl.id, decl.span, TypeDefKind::Enum, body);

                self.session.phase.type_constructors.insert(
                    *type_id,
                    TypeDef {
                        extensions: Default::default(),
                        child_types: Default::default(),
                        name: name.clone(),
                        node_id: decl.id,
                        kind: arrow_n(Kind::Type, generics.len(), Kind::Type),
                        def: TypeDefKind::Enum,
                        conformances: Self::collect_conformance_stubs(*sym, conformances),
                        generics: generics
                            .iter()
                            .map(|g| (g.name.clone(), ASTTyRepr::Generic(g.clone())))
                            .collect(),
                        fields,
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
                    self.child_types
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
                    self.child_types
                        .entry(*parent_id)
                        .or_default()
                        .insert(type_name.to_string(), *sym);
                }

                self.typealiases
                    .insert(decl.id, (name.clone(), rhs.clone()));
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

    fn collect_fields(
        &mut self,
        type_name: &Name,
        id: NodeID,
        span: Span,
        type_kind: TypeDefKind,
        body: &[Node],
    ) -> TypeFields {
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
                DeclKind::EnumVariant(variant_name, values) => {
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
                    params,
                    ret,
                    ..
                }) => {
                    method_requirements.insert(
                        name.into(),
                        MethodRequirement {
                            id,
                            symbol: *symbol,
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
                    let Name::Resolved(Symbol::Type(type_id), _) = &type_name else {
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

        if type_kind == TypeDefKind::Struct && initializers.is_empty() {
            let Name::Resolved(Symbol::Type(type_id), _) = &type_name else {
                unreachable!("didn't resolve type");
            };

            // If we don't have an initializer, synthesize one.
            let mut params: Vec<ASTTyRepr> = properties
                .values()
                .filter_map(|p| {
                    if p.is_static {
                        None
                    } else {
                        Some(p.ty_repr.clone())
                    }
                })
                .collect();

            // At this point, we've already prepend `self` to param lists so we need to do so here as well
            params.insert(0, ASTTyRepr::SelfType(type_name.clone(), id, span));

            let sym = Symbol::Synthesized(SynthesizedId(self.session.synthsized_ids.next_id()));

            initializers.insert(
                "init".into(),
                Initializer {
                    initializes_type_id: *type_id,
                    symbol: sym,
                    params,
                },
            );
        }

        match type_kind {
            TypeDefKind::Extension => TypeFields::Extension {
                instance_methods,
                static_methods,
            },
            TypeDefKind::Struct => TypeFields::Struct {
                initializers,
                instance_methods,
                static_methods,
                properties,
            },
            TypeDefKind::Enum => TypeFields::Enum {
                variants,
                instance_methods,
                static_methods,
            },
            TypeDefKind::Protocol => TypeFields::Protocol {
                instance_methods,
                static_methods,
                associated_types,
                method_requirements,
            },
        }
    }
}

#[cfg(test)]
pub mod tests {
    use indexmap::indexmap;

    use crate::{
        annotation, assert_eq_diff,
        ast::AST,
        fxhashmap,
        label::Label,
        name::Name,
        name_resolution::{
            name_resolver::NameResolved,
            name_resolver_tests::tests::resolve,
            symbol::{
                AssociatedTypeId, BuiltinId, GlobalId, InstanceMethodId, PropertyId, ProtocolId,
                Symbol, SynthesizedId, TypeId, TypeParameterId, VariantId,
            },
        },
        node::Node,
        node_id::NodeID,
        node_kinds::{generic_decl::GenericDecl, type_annotation::*},
        span::Span,
        types::{
            fields::{Associated, Initializer, MethodRequirement, Property, TypeFields, Variant},
            kind::Kind,
            passes::type_headers_pass::TypeHeaderPass,
            type_catalog::ConformanceStub,
            type_session::{ASTTyRepr, Raw, TypeDef, TypeDefKind, TypeExtension, TypeSession},
        },
    };

    pub fn type_header_decl_pass(code: &'static str) -> (AST<NameResolved>, TypeSession<Raw>) {
        let resolved = resolve(code);
        let mut session = TypeSession::<Raw>::default();
        TypeHeaderPass::drive(&mut session, &resolved);
        (resolved, session)
    }

    #[test]
    fn basic_struct() {
        let session = type_header_decl_pass(
            "
        struct Person {
            let age: Int
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef {
                extensions: Default::default(),
                child_types: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                conformances: Default::default(),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: indexmap! {
                        Label::Named("init".into()) => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                                ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                                ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::Int, "Int".into()), generics: vec!{} }))
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    properties: crate::indexmap!(
                        "age".into() => Property {
                            symbol: Symbol::Property(PropertyId(1)),
                            is_static: false,
                            ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::Builtin(BuiltinId(1)), "Int".into()),
                                generics: vec![]
                            })),
                        }
                    )
                }
            }
        );
    }

    #[test]
    fn struct_extension() {
        let session = type_header_decl_pass(
            "
        struct Person {}
        extend Person {}
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef {
                child_types: Default::default(),
                extensions: vec![TypeExtension {
                    node_id: NodeID::ANY,
                    conformances: Default::default(),
                    methods: Default::default(),
                    static_methods: Default::default(),
                }],
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Person".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                conformances: Default::default(),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: indexmap! {
                        "init".into() => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                                ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Person".into()), NodeID::ANY, Span::ANY),
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    properties: Default::default()
                }
            }
        );
    }

    #[test]
    fn generic_struct() {
        let session = type_header_decl_pass(
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
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef {
                child_types: Default::default(),
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()),
                kind: Kind::Arrow {
                    in_kind: Box::new(Kind::Type),
                    out_kind: Box::new(Kind::Type)
                },
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                conformances: Default::default(),
                generics: crate::indexmap!(Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()) => ASTTyRepr::Generic(GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    generics: vec![],
                    conformances: vec![],
                    span: Span::ANY,
                })),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: crate::indexmap!("init".into() => Initializer {
                        symbol: Symbol::Global(GlobalId(1)),
                        initializes_type_id: TypeId(1),
                        params: vec![
                            ASTTyRepr::SelfType(Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()), NodeID::ANY, Span::ANY),
                            ASTTyRepr::Hole(NodeID(4), Span::ANY)
                        ]
                    }),
                    instance_methods: Default::default(),
                    properties: crate::indexmap!("wrapped".into() => Property {
                        symbol: Symbol::Property(PropertyId(1)),
                        is_static: false,
                        ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                            generics: vec![]
                        }))
                    })
                }
            }
        );
    }

    #[test]
    fn nested_generic_struct() {
        let session = type_header_decl_pass(
            "
        struct Wrapper<T, U> {
            let wrapped: T<U>
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef {
                child_types: Default::default(),
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Wrapper".into()),
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
                conformances: Default::default(),
                generics: crate::indexmap!(
                  Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()) =>  ASTTyRepr::Generic(GenericDecl {
                        id: NodeID::ANY,
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                        generics: vec![],
                        conformances: vec![],
                        span: Span::ANY,
                    }),
                   Name::Resolved(Symbol::TypeParameter(TypeParameterId(2)), "U".into()) => ASTTyRepr::Generic(GenericDecl {
                        id: NodeID::ANY,
                        name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(2)), "U".into()),
                        generics: vec![],
                        conformances: vec![],
                        span: Span::ANY,
                    })
                ),
                fields: TypeFields::Struct {
                    static_methods: Default::default(),
                    initializers: indexmap! {
                        "init".into() => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                            ASTTyRepr::SelfType(Name::Resolved(TypeId(1).into(), "Wrapper".into()), NodeID::ANY, Span::ANY),
                            ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()), generics: vec![
                                annotation!(TypeAnnotationKind::Nominal { name: Name::Resolved(TypeParameterId(2).into(), "U".into()), generics: vec![] })
                            ] }))
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    properties: crate::indexmap!("wrapped".into() => Property {
                        symbol: Symbol::Property(PropertyId(1)),
                        is_static: false,
                        ty_repr: ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                            generics: vec![annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(2)), "U".into()),
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
        let session = type_header_decl_pass(
            "
        enum Fizz {
            case foo(Int), bar
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef {
                child_types: Default::default(),
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Fizz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Enum,
                generics: Default::default(),
                conformances: Default::default(),
                fields: TypeFields::Enum {
                    static_methods: Default::default(),
                    variants: crate::indexmap!(
                        "foo".into() => Variant {
                            symbol: Symbol::Variant(VariantId(1)),
                            tag: "foo".into(),
                            fields: vec![ASTTyRepr::Annotated(annotation!(
                                TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(Symbol::Int, "Int".into()),
                                    generics: vec![]
                                }
                            ))]
                        },
                        "bar".into() =>  Variant { symbol: Symbol::Variant(VariantId(2)), tag: "bar".into(), fields: vec![] }
                    ),
                    instance_methods: Default::default()
                }
            }
        );
    }

    #[test]
    fn basic_protocol() {
        let session = type_header_decl_pass(
            "
        protocol Fizz {
            associated Buzz

            func foo() -> Int
        }
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.protocols.get(&ProtocolId(1)).unwrap(),
            TypeDef {
                child_types: Default::default(),
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Protocol(ProtocolId(1)), "Fizz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Protocol,
                generics: Default::default(),
                conformances: Default::default(),
                fields: TypeFields::Protocol {
                    instance_methods: Default::default(),
                    static_methods: Default::default(),
                    method_requirements: crate::indexmap!("foo".into() => MethodRequirement {
                        id: NodeID::ANY,
                        symbol: Symbol::InstanceMethod(InstanceMethodId(1)),
                        params: vec![
                            ASTTyRepr::SelfType(
                                Name::Resolved(ProtocolId(1).into(), "Fizz".into()),
                                NodeID::ANY,
                                Span::ANY,
                            )
                        ],
                        ret: Some(ASTTyRepr::Annotated(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(Symbol::Int, "Int".into()),
                            generics: vec![]
                        })))
                    }),
                    associated_types: fxhashmap!(Name::Resolved(Symbol::AssociatedType(AssociatedTypeId(1)), "Buzz".into()) => Associated {
                        protocol_id: ProtocolId(1),
                        symbol: Symbol::AssociatedType(AssociatedTypeId(1))
                    })
                }
            }
        );
    }

    #[test]
    fn basic_conformance() {
        let session = type_header_decl_pass(
            "
        protocol Fizz {}
        struct Buzz: Fizz {}
        ",
        )
        .1;

        assert_eq_diff!(
            *session.phase.type_constructors.get(&TypeId(1)).unwrap(),
            TypeDef {
                child_types: Default::default(),
                extensions: Default::default(),
                name: Name::Resolved(Symbol::Type(TypeId(1)), "Buzz".into()),
                kind: Kind::Type,
                node_id: NodeID::ANY,
                def: TypeDefKind::Struct,
                generics: Default::default(),
                conformances: vec![ConformanceStub {
                    conforming_id: TypeId(1).into(),
                    protocol_id: ProtocolId(1),
                    span: Span::ANY,
                }],
                fields: TypeFields::Struct {
                    initializers: indexmap! {
                        "init".into() => Initializer {
                            symbol: Symbol::Synthesized(SynthesizedId(1)),
                            initializes_type_id: TypeId(1),
                            params: vec![
                                ASTTyRepr::SelfType(
                                    Name::Resolved(Symbol::Type(TypeId(1)), "Buzz".into()),
                                    NodeID::ANY,
                                    Span::ANY
                                ),
                            ]
                        }
                    },
                    instance_methods: Default::default(),
                    static_methods: Default::default(),
                    properties: Default::default()
                }
            }
        );
    }

    #[test]
    fn global_let() {
        let (ast, session) = type_header_decl_pass(
            "
        let x: Int = 123
        ",
        );

        assert!(matches!(
            ast.find(NodeID(2)).unwrap(),
            Node::TypeAnnotation(TypeAnnotation { .. })
        ));

        assert_eq!(
            *session.phase.annotations.get(&NodeID(2)).unwrap(),
            ASTTyRepr::Annotated(TypeAnnotation {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Int, "Int".into()),
                    generics: vec![]
                }
            })
        );
    }

    #[test]
    fn global_func() {
        let (ast, session) = type_header_decl_pass(
            "
        func fizz<T>(t: T) {}
        ",
        );

        assert!(matches!(
            ast.find(NodeID(2)).unwrap(),
            Node::TypeAnnotation(TypeAnnotation { .. })
        ));

        assert_eq!(
            *session.phase.annotations.get(&NodeID(2)).unwrap(),
            ASTTyRepr::Annotated(TypeAnnotation {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::TypeParameter(TypeParameterId(1)), "T".into()),
                    generics: vec![]
                }
            })
        );
    }
}
