#[cfg(test)]
pub mod tests {
    use std::rc::Rc;

    use indexmap::indexset;

    use crate::{
        annotation, any, any_block, any_body, any_decl, any_expr, any_expr_stmt, any_stmt,
        assert_eq_diff,
        ast::{AST, NameResolved},
        compiling::module::{ModuleEnvironment, ModuleId},
        diagnostic::{AnyDiagnostic, Diagnostic, Severity},
        hygiene::{
            MaterializedIdentifier, SyntaxContext, SyntaxMetadata, SyntaxOrigin, SyntaxScope,
        },
        label::Label,
        name::Name,
        name_resolution::{
            name_resolver::{NameResolver, NameResolverError, ResolvedNames},
            symbol::{
                AssociatedTypeId, BuiltinId, DeclaredLocalId, EffectId, EnumId, GlobalId,
                InitializerId, InstanceMethodId, MethodRequirementId, ParamLocalId,
                PatternBindLocalId, PropertyId, ProtocolId, StaticMethodId, StructId, Symbol,
                SynthesizedId, TypeAliasId, TypeParameterId, VariantId,
            },
        },
        node_id::{FileID, NodeID},
        node_kinds::type_application::TypeApplication,
        node_kinds::{
            block::Block,
            call_arg::{CallArg, CallArgOrigin},
            decl::{Decl, DeclKind, ReceiverMode},
            expr::{Expr, ExprKind},
            func::{CaptureMode, EffectSet, Func, FuncOrigin},
            func_signature::FuncSignature,
            generic_decl::GenericDecl,
            match_arm::MatchArm,
            parameter::{ParamLabel, ParamMode, Parameter},
            pattern::{Pattern, PatternKind},
            stmt::{Stmt, StmtKind},
            type_annotation::{TypeAnnotation, TypeAnnotationKind},
        },
        parsing::parser_tests::tests::parse,
        span::Span,
    };

    fn enum_variant(name: Name, name_span: Span, payloads: Vec<TypeAnnotation>) -> DeclKind {
        DeclKind::EnumVariant {
            name,
            name_span,
            generics: vec![],
            payload_labels: vec![None; payloads.len()],
            payloads,
            result: None,
        }
    }

    /// Helper to create a test TypeParameterId using ModuleId::Current
    fn test_type_param(id: u32) -> Symbol {
        Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, id))
    }

    #[macro_export]
    macro_rules! param {
        ($id:expr, $name:expr) => {
            Parameter {
                label: None,
                label_span: None,
                mode: None,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: None,
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, mode: $mode:expr) => {
            Parameter {
                label: None,
                label_span: None,
                mode: $mode,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: None,
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr) => {
            Parameter {
                label: None,
                label_span: None,
                mode: None,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: Some($ty),
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr, mode: $mode:expr) => {
            Parameter {
                label: None,
                label_span: None,
                mode: $mode,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: Some($ty),
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr, label: $label:expr) => {
            Parameter {
                label: Some(ParamLabel::Named($label.into())),
                label_span: Some(Span::ANY),
                mode: None,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: Some($ty),
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr, label: $label:expr, mode: $mode:expr) => {
            Parameter {
                label: Some(ParamLabel::Named($label.into())),
                label_span: Some(Span::ANY),
                mode: $mode,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: Some($ty),
                span: Span::ANY,
            }
        };
        ($id:expr, $name:expr, $ty:expr, synthetic_label: $label:expr, mode: $mode:expr) => {
            Parameter {
                label: Some(ParamLabel::Named($label.into())),
                label_span: None,
                mode: $mode,
                mode_span: None,
                id: NodeID::ANY,
                name: Name::Resolved($id.into(), $name.into()),
                name_span: Span::ANY,
                type_annotation: Some($ty),
                span: Span::ANY,
            }
        };
    }

    macro_rules! variable {
        ($id:expr, $name:expr) => {
            Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Variable(Name::Resolved($id.into(), $name.into())),
            }
        };
        ($name:expr) => {
            Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Variable(Name::Raw($name.into())),
            }
        };
    }

    #[macro_export]
    macro_rules! any_pattern {
        ($kind: expr) => {
            $crate::parsing::node_kinds::pattern::Pattern {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: $kind,
            }
        };
    }

    pub fn resolve(code: &'static str) -> (AST<NameResolved>, ResolvedNames) {
        let (ast, resolved) = resolve_err(code);
        assert!(
            resolved.diagnostics.is_empty(),
            "diagnostics not empty: {:?}",
            resolved.diagnostics
        );
        (ast, resolved)
    }

    fn resolve_err(code: &'static str) -> (AST<NameResolved>, ResolvedNames) {
        let parsed = parse(code);
        let modules = ModuleEnvironment::default();
        let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let mut parseds = vec![parsed];
        crate::desugar::desugar(&mut parseds);
        let (asts, resolved) = name_resolver.resolve(parseds);
        (asts[0].clone(), resolved)
    }

    #[test]
    fn hygienic_bindings_do_not_capture_use_site_references() {
        let source = "let x = 1\n{\n\tlet x = 2\n\tlet generated = x\n\tlet caller = x\n}\n";
        let mut parsed = parse(source);
        let file_id = parsed.file_id;
        let root_scope = NodeID(file_id, 0);
        let introduced = SyntaxContext::lexical(root_scope).with_scope(SyntaxScope::Expansion {
            namespace: 7,
            ordinal: 1,
        });
        let use_site = SyntaxContext::lexical(root_scope);
        let positions: Vec<usize> = source
            .match_indices('x')
            .map(|(offset, _)| offset)
            .collect();
        assert_eq!(positions.len(), 4);
        let identifier = |offset: usize, context: SyntaxContext| MaterializedIdentifier {
            text: "x".into(),
            span: Span {
                file_id,
                start: offset as u32,
                end: offset as u32 + 1,
            },
            lexeme: Span {
                file_id,
                start: offset as u32,
                end: offset as u32 + 1,
            },
            context,
            origin: SyntaxOrigin::DefinitionSite,
            source_span: Span {
                file_id,
                start: offset as u32,
                end: offset as u32 + 1,
            },
            source_lexeme: Span {
                file_id,
                start: offset as u32,
                end: offset as u32 + 1,
            },
        };
        parsed.apply_syntax_metadata(SyntaxMetadata::new(vec![
            identifier(positions[1], introduced.clone()),
            identifier(positions[2], introduced),
            MaterializedIdentifier {
                origin: SyntaxOrigin::UseSite,
                ..identifier(positions[3], use_site)
            },
        ]));

        let modules = ModuleEnvironment::default();
        let mut resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let mut parseds = vec![parsed];
        crate::desugar::desugar(&mut parseds);
        let (asts, resolved) = resolver.resolve(parseds);
        assert!(
            resolved.diagnostics.is_empty(),
            "{:?}",
            resolved.diagnostics
        );

        let outer = match &asts[0].roots[0] {
            crate::node::Node::Decl(Decl {
                kind: DeclKind::Let { lhs, .. },
                ..
            }) => lhs.kind.clone(),
            other => panic!("expected outer let, got {other:?}"),
        };
        let PatternKind::Bind(Name::Resolved(outer_symbol, _)) = outer else {
            panic!("outer binding was not resolved")
        };

        let mut references = Vec::new();
        let mut collector = derive_visitor::visitor_enter_fn(|expr: &Expr| {
            if let ExprKind::Variable(Name::Resolved(symbol, name)) = &expr.kind
                && name == "x"
            {
                references.push(*symbol);
            }
        });
        for root in &asts[0].roots {
            derive_visitor::Drive::drive(root, &mut collector);
        }
        drop(collector);
        assert_eq!(references.len(), 2);
        assert_ne!(
            references[0], outer_symbol,
            "introduced reference missed its binder"
        );
        assert_eq!(
            references[1], outer_symbol,
            "use-site reference was captured"
        );
    }

    #[test]
    fn definition_site_reference_ignores_use_site_shadowing() {
        let source = "let helper = 1\n{\n\tlet helper = 2\n\tlet result = helper\n}\n";
        let mut parsed = parse(source);
        let file_id = parsed.file_id;
        let root_scope = NodeID(file_id, 0);
        let context = SyntaxContext::lexical(root_scope).with_scope(SyntaxScope::Expansion {
            namespace: 9,
            ordinal: 1,
        });
        let positions: Vec<usize> = source
            .match_indices("helper")
            .map(|(offset, _)| offset)
            .collect();
        assert_eq!(positions.len(), 3);
        let start = positions[2] as u32;
        let span = Span {
            file_id,
            start,
            end: start + "helper".len() as u32,
        };
        parsed.apply_syntax_metadata(SyntaxMetadata::new(vec![MaterializedIdentifier {
            text: "helper".into(),
            span,
            lexeme: span,
            context,
            origin: SyntaxOrigin::DefinitionSite,
            source_span: span,
            source_lexeme: span,
        }]));

        let modules = ModuleEnvironment::default();
        let mut resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let mut parseds = vec![parsed];
        crate::desugar::desugar(&mut parseds);
        let (asts, resolved) = resolver.resolve(parseds);
        assert!(
            resolved.diagnostics.is_empty(),
            "{:?}",
            resolved.diagnostics
        );

        let outer = match &asts[0].roots[0] {
            crate::node::Node::Decl(Decl {
                kind: DeclKind::Let { lhs, .. },
                ..
            }) => lhs.kind.clone(),
            other => panic!("expected outer let, got {other:?}"),
        };
        let PatternKind::Bind(Name::Resolved(outer_symbol, _)) = outer else {
            panic!("outer helper was not resolved")
        };
        let mut references = Vec::new();
        let mut collector = derive_visitor::visitor_enter_fn(|expr: &Expr| {
            if let ExprKind::Variable(Name::Resolved(symbol, name)) = &expr.kind
                && name == "helper"
            {
                references.push(*symbol);
            }
        });
        for root in &asts[0].roots {
            derive_visitor::Drive::drive(root, &mut collector);
        }
        drop(collector);
        assert_eq!(references, vec![outer_symbol]);
    }

    #[test]
    fn resolves_simple_variable() {
        let tree = resolve("let hello = 1; hello");
        assert_eq!(
            *tree.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                Symbol::Global(GlobalId::from(1)),
                "hello".into()
            )))
        );

        // The declaration node: the binding pattern of the `let`
        // (id numbering is the frontend adapter's, not asserted).
        let declaration = *tree
            .1
            .symbols_to_node
            .get(&Symbol::Global(GlobalId::from(1)))
            .unwrap();
        let node = tree.0.find(declaration).expect("declaration node exists");
        assert!(matches!(
            node,
            crate::node::Node::Pattern(crate::node_kinds::pattern::Pattern {
                kind: crate::node_kinds::pattern::PatternKind::Bind(_),
                ..
            })
        ));
    }

    #[test]
    fn resolves_builtin_type() {
        let resolved = resolve("let hello: Int");
        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "hello".into()
                    ))
                },
                type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(
                        Symbol::Builtin(BuiltinId::new(
                            crate::compiling::module::ModuleId::Core,
                            1
                        )),
                        "Int".into()
                    ),
                    name_span: Span::ANY,
                    generics: vec![]
                })),
                rhs: None,
            })
        );
    }

    /// The ids of every resolved `Variable` of symbol kind `kind` (e.g.
    /// "DeclaredLocal", "ParamLocal", "Global") named `needle`, in source
    /// order, scraped from the AST's debug rendering.
    fn variable_uses(rendered: &str, kind: &str, needle: &str) -> Vec<u32> {
        let pattern = format!("Variable(Resolved(@{kind}({kind}Id(");
        rendered
            .match_indices(&pattern)
            .filter_map(|(at, _)| {
                let rest = &rendered[at + pattern.len()..];
                let close = rest.find(')')?;
                let id = rest[..close].parse::<u32>().ok()?;
                let suffix = &rest[close..];
                suffix
                    .starts_with(&format!(")), \"{needle}\""))
                    .then_some(id)
            })
            .collect()
    }

    fn local_variable_uses(rendered: &str, needle: &str) -> Vec<u32> {
        variable_uses(rendered, "DeclaredLocal", needle)
    }

    /// Like [`variable_uses`], for `Global` symbols (module ids render as
    /// `@Global(Global(_:1))`, not `GlobalId`).
    fn global_variable_uses(rendered: &str, needle: &str) -> Vec<u32> {
        let pattern = "Variable(Resolved(@Global(Global(_:";
        rendered
            .match_indices(pattern)
            .filter_map(|(at, _)| {
                let rest = &rendered[at + pattern.len()..];
                let close = rest.find(')')?;
                let id = rest[..close].parse::<u32>().ok()?;
                let suffix = &rest[close..];
                suffix
                    .starts_with(&format!(")), \"{needle}\""))
                    .then_some(id)
            })
            .collect()
    }

    #[test]
    fn sibling_blocks_declare_same_named_lets_independently() {
        // Each branch's `y` is its own binding; the uses must resolve to
        // their own block's declaration, not whichever declared last.
        let (ast, _) = resolve(
            "func f(a: Bool, x: Int) -> Int {\n\tlet out = 0\n\tif a {\n\t\tlet y = x\n\t\tout = y\n\t}\n\tif a {\n\t\tlet y = x\n\t\tout = y\n\t}\n\tout\n}",
        );
        let rendered = format!("{ast:?}");
        let y_uses = local_variable_uses(&rendered, "y");
        assert_eq!(y_uses.len(), 2, "two y uses: {rendered}");
        assert_ne!(
            y_uses[0], y_uses[1],
            "each use must reference its own block's y"
        );
    }

    #[test]
    fn nested_shadowing_resolves_innermost_first() {
        let (ast, _) = resolve(
            "func f(a: Bool, x: Int) -> Int {\n\tlet y = x\n\tlet inner = 0\n\tif a {\n\t\tlet y = x\n\t\tinner = y\n\t}\n\ty\n}",
        );
        let rendered = format!("{ast:?}");
        let y_uses = local_variable_uses(&rendered, "y");
        // In order: the inner block's use, then the tail's outer use.
        assert_eq!(y_uses.len(), 2, "{rendered}");
        assert_ne!(
            y_uses[0], y_uses[1],
            "inner use shadows, outer use sees the outer y: {y_uses:?}"
        );
    }

    #[test]
    fn sequential_rebinding_is_legal() {
        // Rule 2: a later same-named `let` shadows from its point of
        // declaration on; earlier uses (including the shadow's own rhs)
        // keep the earlier binding.
        let (ast, _) = resolve("func f(x: Int) -> Int {\n\tlet y = x\n\tlet y = y\n\ty\n}");
        let rendered = format!("{ast:?}");
        let y_uses = variable_uses(&rendered, "DeclaredLocal", "y");
        // In source order: the second let's rhs, then the tail.
        assert_eq!(y_uses.len(), 2, "{rendered}");
        assert_ne!(
            y_uses[0], y_uses[1],
            "the rhs sees the first y, the tail sees the rebinding"
        );
    }

    #[test]
    fn duplicate_binders_in_one_pattern_are_an_error() {
        // Rebinding across `let`s is legal; binding one name twice in a
        // single pattern is not (each would silently orphan the other).
        let resolved = resolve_err("match (1, 2) {\n\t(a, a) -> a\n}");
        assert!(
            matches!(
                &resolved.1.diagnostics[0],
                AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                    kind: NameResolverError::DuplicateDeclaration(name),
                    ..
                }) if name == "a"
            ),
            "{:?}",
            resolved.1.diagnostics
        );
    }

    #[test]
    fn type_alias_shares_the_nominal_namespace() {
        // A type alias collides with a same-named nominal in its scope:
        // the merged symbol could otherwise reach the backend as an
        // alias nominal it cannot lower.
        let resolved = resolve_err("pub struct File {\n}\npub typealias File = Int\n");
        assert!(
            resolved.1.diagnostics.iter().any(|diagnostic| matches!(
                diagnostic,
                AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                    kind: NameResolverError::DuplicateDeclaration(name),
                    ..
                }) if name == "File"
            )),
            "{:?}",
            resolved.1.diagnostics
        );

        // Two same-named aliases collide too.
        let resolved = resolve_err("pub typealias File = Int\npub typealias File = String\n");
        assert!(
            resolved.1.diagnostics.iter().any(|diagnostic| matches!(
                diagnostic,
                AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                    kind: NameResolverError::DuplicateDeclaration(name),
                    ..
                }) if name == "File"
            )),
            "{:?}",
            resolved.1.diagnostics
        );
    }

    ///////////////////////////////////////////////////////////////////////
    // Sequential-scoping characterization matrix
    // (docs/adr/0013-sequential-scoping-for-locals.md). Each test locks today's
    // behavior; the ones marked "flips at step N" record the current
    // locals-hoisting semantics that sequential scoping replaces.
    ///////////////////////////////////////////////////////////////////////

    #[test]
    fn let_rhs_resolves_to_the_outer_binding() {
        // Rule 1: a binding is visible from just after its initializer, so
        // `let y = y` sees the *outer* y on the rhs.
        let (ast, _) = resolve(
            "func f(a: Bool) -> Int {\n\tlet y = 1\n\tif a {\n\t\tlet y = y\n\t\ty\n\t}\n\ty\n}",
        );
        let rendered = format!("{ast:?}");
        let y_uses = variable_uses(&rendered, "DeclaredLocal", "y");
        // In source order: the inner rhs, the inner tail, the outer tail.
        assert_eq!(y_uses.len(), 3, "{rendered}");
        assert_eq!(y_uses[0], y_uses[2], "the rhs use resolves to the outer y");
        assert_ne!(y_uses[0], y_uses[1], "the inner tail sees the shadow");
    }

    #[test]
    fn body_let_rhs_sees_the_param_it_shadows() {
        // Rule 3: parameters live in the function's scope; a body-level
        // `let x = x` reads the parameter on the rhs and shadows it after.
        let (ast, _) = resolve("func f(x: Int) -> Int {\n\tlet x = x\n\tx\n}");
        let rendered = format!("{ast:?}");
        let local = variable_uses(&rendered, "DeclaredLocal", "x");
        let param = variable_uses(&rendered, "ParamLocal", "x");
        assert_eq!(param.len(), 1, "the rhs reads the param: {rendered}");
        assert_eq!(local.len(), 1, "the tail reads the shadow: {rendered}");
    }

    #[test]
    fn use_before_declaration_is_undefined() {
        // Rule 1: a binding is not visible before its declaration.
        let resolved = resolve_err("func f() -> Int {\n\tlet a = b\n\tlet b = 2\n\tb\n}");
        assert_eq!(
            resolved.1.diagnostics,
            vec![AnyDiagnostic::NameResolution(Diagnostic::<
                NameResolverError,
            > {
                id: NodeID::ANY,
                severity: Severity::Error,
                kind: NameResolverError::UndefinedName("b".into())
            })],
            "{:?}",
            resolved.1.diagnostics
        );
    }

    #[test]
    fn closure_sees_the_binding_visible_at_the_closure() {
        // A shadow *after* (and inside a sibling block of) the closure must
        // not change which binding the closure body resolved to.
        let (ast, _) = resolve(
            "func outer() {\n\tlet x = 1\n\tfunc inner() { x }\n\tif true {\n\t\tlet x = 2\n\t\tx\n\t}\n}",
        );
        let rendered = format!("{ast:?}");
        let x_uses = variable_uses(&rendered, "DeclaredLocal", "x");
        // In source order: inner's body use, then the if-block's use.
        assert_eq!(x_uses.len(), 2, "{rendered}");
        assert_ne!(
            x_uses[0], x_uses[1],
            "inner reads the outer x, the block reads its shadow"
        );
    }

    #[test]
    fn local_named_funcs_are_mutually_visible_in_their_block() {
        // Item behavior (Rust's fn-in-block): `func a` / `func b` in one
        // block see each other regardless of order. They desugar to
        // func-valued lets before resolution; their binders must keep
        // block-wide visibility under sequential scoping.
        let (ast, _) = resolve("func outer() {\n\tfunc a() { b() }\n\tfunc b() { a() }\n\ta()\n}");
        let rendered = format!("{ast:?}");
        let a_uses = variable_uses(&rendered, "DeclaredLocal", "a");
        let b_uses = variable_uses(&rendered, "DeclaredLocal", "b");
        assert_eq!(b_uses.len(), 1, "{rendered}");
        assert_eq!(a_uses.len(), 2, "{rendered}");
        assert_eq!(a_uses[0], a_uses[1], "both a uses hit the same binder");
    }

    #[test]
    fn func_valued_let_is_visible_inside_its_own_body() {
        // Self-recursion through the binder: `func f` sugar and
        // `let f = func ...` both resolve the body's f to the binder.
        let (ast, _) = resolve("func outer() {\n\tlet f = func() { f() }\n\tf()\n}");
        let rendered = format!("{ast:?}");
        let f_uses = variable_uses(&rendered, "DeclaredLocal", "f");
        assert_eq!(f_uses.len(), 2, "{rendered}");
        assert_eq!(f_uses[0], f_uses[1]);
    }

    #[test]
    fn module_scope_rebinding_is_legal_and_last_wins() {
        // Matrix rule 4: module scope keeps its declare-then-resolve
        // semantics — redeclaration is allowed and every use resolves to
        // the newest binder (the REPL depends on this).
        let (ast, _) = resolve("let x = 1\nlet x = 2\nx");
        let rendered = format!("{ast:?}");
        let x_uses = global_variable_uses(&rendered, "x");
        assert_eq!(x_uses.len(), 1, "{rendered}");
        assert_eq!(x_uses[0], 2, "the use sees the last declaration");
    }

    #[test]
    fn each_method_body_resolves_its_own_params() {
        let (ast, _) = resolve(
            "struct P {\n\tfunc m1(a: Int) -> Int { a }\n\tfunc m2(a: Int) -> Int { a }\n}",
        );
        let rendered = format!("{ast:?}");
        let a_uses = variable_uses(&rendered, "ParamLocal", "a");
        assert_eq!(a_uses.len(), 2, "{rendered}");
        assert_ne!(
            a_uses[0], a_uses[1],
            "each method body sees its own parameter"
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        let resolved = resolve_err(
            "{
            let x = 123
            x // This one is fine.
        }
        x // This one is not
        ",
        );
        assert_eq!(1, resolved.1.diagnostics.len());
        assert_eq!(
            resolved.1.diagnostics[0],
            AnyDiagnostic::NameResolution(Diagnostic::<NameResolverError> {
                id: NodeID::ANY,
                severity: Severity::Error,
                kind: NameResolverError::UndefinedName("x".into())
            })
        )
    }

    #[test]
    fn resolves_func_params() {
        let tree = resolve("func foo(x, y) { x ; y }");

        assert_eq_diff!(
            *tree.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "foo".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "foo".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    effects: Default::default(),
                    params: vec![
                        param!(ParamLocalId(1), "x", mode: Some(ParamMode::Borrow)),
                        param!(ParamLocalId(2), "y", mode: Some(ParamMode::Borrow)),
                    ],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x")))
                            .try_into()
                            .unwrap(),
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(2), "y")))
                            .try_into()
                            .unwrap(),
                    ]),
                    ret: None,
                    attributes: vec![],
                }))),
            })
        );
    }

    #[test]
    fn resolves_mutual_recursion() {
        let resolved = resolve(
            "
          func odd() { even() }
          func even() { odd() }
          ",
        );

        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "odd".into()
                    ))
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "odd".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    effects: Default::default(),
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId::from(2)), "even")),
                        type_args: vec![],
                        args: vec![],
                        trailing_block: None,
                        desugared_operator: None,
                    })]),
                    ret: None,
                    attributes: vec![]
                }))),
            })
        );

        assert_eq_diff!(
            *resolved.0.roots[1].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(2)),
                        "even".into()
                    ))
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(2)), "even".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    effects: Default::default(),
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                        callee: Box::new(variable!(Symbol::Global(GlobalId::from(1)), "odd")),
                        type_args: vec![],
                        args: vec![],
                        trailing_block: None,
                        desugared_operator: None,
                    })]),
                    ret: None,
                    attributes: vec![]
                }))),
            })
        );
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func foo(x, y) { func bar(x) { x \n y }\nx }\n");

        assert_eq_diff!(
            *tree.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1)),
                        "foo".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "foo".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    effects: Default::default(),
                    params: vec![
                        param!(ParamLocalId(1), "x", mode: Some(ParamMode::Borrow)),
                        param!(ParamLocalId(2), "y", mode: Some(ParamMode::Borrow)),
                    ],
                    body: any_block!(vec![
                        any_decl!(DeclKind::Let {
                            lhs: Pattern {
                                id: NodeID::ANY,
                                kind: PatternKind::Bind(Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "bar".into()
                                )),
                                span: Span::ANY
                            },
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::Func(Func {
                                origin: FuncOrigin::Decl,
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "bar".into()
                                ),
                                name_span: Span::ANY,
                                generics: vec![],
                                captures: vec![],
                                where_clause: None,
                                effects: Default::default(),
                                params: vec![
                                    param!(ParamLocalId(3), "x", mode: Some(ParamMode::Borrow))
                                ],
                                body: any_block!(vec![
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(3), "x")))
                                        .into(),
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(2), "y")))
                                        .into(),
                                ]),
                                ret: None,
                                attributes: vec![],
                            }))),
                        })
                        .into(),
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x"))).into(),
                    ]),
                    ret: None,
                    attributes: vec![],
                }))),
            }),
        );
    }

    #[test]
    fn resolves_nested_func_bodies_against_enclosing_locals() {
        let resolved = resolve(
            "
        func fizz() {
            let count = 0
            func counter(x) {
                x
                count
                count
            }
        }
        ",
        );

        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                    Symbol::Global(GlobalId::from(1)),
                    "fizz".into()
                ))),
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "fizz".into()),
                    name_span: Span::ANY,
                    generics: Default::default(),
                    captures: vec![],
                    where_clause: None,
                    params: Default::default(),
                    effects: Default::default(),
                    body: any_block!(vec![
                        any_decl!(DeclKind::Let {
                            lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                                Symbol::DeclaredLocal(DeclaredLocalId(2)),
                                "count".into()
                            ))),
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::LiteralInt("0".into()))),
                        })
                        .into(),
                        any_decl!(DeclKind::Let {
                            lhs: any_pattern!(PatternKind::Bind(Name::Resolved(
                                Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                "counter".into()
                            ))),
                            type_annotation: None,
                            rhs: Some(any_expr!(ExprKind::Func(Func {
                                origin: FuncOrigin::Decl,
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    Symbol::DeclaredLocal(DeclaredLocalId(1)),
                                    "counter".into()
                                ),
                                name_span: Span::ANY,
                                generics: vec![],
                                captures: vec![],
                                where_clause: None,
                                effects: Default::default(),
                                params: vec![
                                    param!(ParamLocalId(1), "x", mode: Some(ParamMode::Borrow))
                                ],
                                body: any_block!(vec![
                                    any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "x")))
                                        .into(),
                                    any_stmt!(StmtKind::Expr(variable!(
                                        DeclaredLocalId(2),
                                        "count"
                                    )))
                                    .into(),
                                    any_stmt!(StmtKind::Expr(variable!(
                                        DeclaredLocalId(2),
                                        "count"
                                    )))
                                    .into(),
                                ]),
                                ret: None,
                                attributes: vec![]
                            }))),
                        })
                        .into()
                    ]),
                    ret: None,
                    attributes: Default::default()
                }))),
            })
        );
    }

    #[test]
    fn resolves_explicit_capture_specs() {
        let resolved = resolve(
            "
        func outer() {
            let a = 1
            let b = 2
            let c = 3
            let d = 4
            let e = 5
            let f = func() { [a, copy b, consuming c, &d, &mut e] in
                a
            }
        }
        ",
        );

        let DeclKind::Let {
            rhs: Some(outer_expr),
            ..
        } = &resolved.0.roots[0].as_decl().kind
        else {
            panic!("expected outer function declaration");
        };
        let ExprKind::Func(outer) = &outer_expr.kind else {
            panic!("expected outer function literal");
        };
        let DeclKind::Let {
            rhs: Some(inner_expr),
            ..
        } = &outer.body.body[5].as_decl().kind
        else {
            panic!("expected nested function binding");
        };
        let ExprKind::Func(inner) = &inner_expr.kind else {
            panic!("expected nested function literal");
        };

        let captures: Vec<_> = inner
            .captures
            .iter()
            .map(|capture| {
                assert!(
                    capture.name.symbol().is_ok(),
                    "capture should be resolved: {:?}",
                    capture
                );
                (capture.name.name_str(), capture.mode)
            })
            .collect();
        assert_eq!(
            captures,
            vec![
                ("a".to_string(), CaptureMode::Copy),
                ("b".to_string(), CaptureMode::Copy),
                ("c".to_string(), CaptureMode::Move),
                ("d".to_string(), CaptureMode::BorrowShared),
                ("e".to_string(), CaptureMode::BorrowMut),
            ]
        );
    }

    #[test]
    fn resolves_func_generics() {
        let resolved = resolve(
            "
        func fizz<T>(t: T) -> T { t }
        ",
        );

        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: Pattern {
                    id: NodeID::ANY,
                    kind: PatternKind::Bind(Name::Resolved(
                        Symbol::Global(GlobalId::from(1),),
                        "fizz".into()
                    )),
                    span: Span::ANY
                },
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(GlobalId::from(1)), "fizz".into()),
                    name_span: Span::ANY,
                    generics: vec![GenericDecl {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(test_type_param(1), "T".into()),
                        name_span: Span::ANY,
                        generics: vec![],
                        conformances: vec![],
                        default: None,
                        static_ty: None,
                    }],
                    captures: vec![],
                    where_clause: None,
                    effects: Default::default(),
                    params: vec![param!(
                        ParamLocalId(1),
                        "t",
                        annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(test_type_param(1), "T".into()),
                            name_span: Span::ANY,
                            generics: vec![]
                        }),
                        label: "t",
                        mode: Some(ParamMode::Borrow)
                    ),],
                    body: any_block!(vec![
                        any_stmt!(StmtKind::Expr(variable!(ParamLocalId(1), "t"))).into(),
                    ]),
                    ret: Some(annotation!(TypeAnnotationKind::Nominal {
                        name: Name::Resolved(test_type_param(1), "T".into()),
                        name_span: Span::ANY,
                        generics: vec![]
                    })),
                    attributes: vec![],
                })),),
            })
        );
    }

    #[test]
    fn resolves_static_generic_params() {
        let resolved = resolve("func width<static N: Int>() -> Int { N }");
        let DeclKind::Let { rhs: Some(rhs), .. } = &resolved.0.roots[0].as_decl().kind else {
            panic!("expected desugared func let")
        };
        let ExprKind::Func(func) = &rhs.kind else {
            panic!("expected func")
        };
        let param_symbol = func.generics[0]
            .name
            .symbol()
            .expect("resolved static param");
        assert!(matches!(param_symbol, Symbol::TypeParameter(_)));
        let static_ty = func.generics[0]
            .static_ty
            .as_ref()
            .expect("static value type");
        assert!(matches!(
            &static_ty.kind,
            TypeAnnotationKind::Nominal { name, .. } if name.symbol().ok() == Some(Symbol::Int)
        ));
        // A static parameter is usable as an ordinary value in its body
        // (ADR 0035 §6), so the body variable resolves to the parameter.
        let StmtKind::Expr(Expr {
            kind: ExprKind::Variable(body_name),
            ..
        }) = &func.body.body[0].as_stmt().kind
        else {
            panic!("expected body variable")
        };
        assert_eq!(body_name.symbol().ok(), Some(param_symbol));
    }

    #[test]
    fn resolves_static_generic_argument_reference() {
        let resolved = resolve(
            "
        struct Grid<static Rows: Int> {}
        func f<static M: Int>(g: Grid<M>) -> Int { M }
        ",
        );
        let DeclKind::Let { rhs: Some(rhs), .. } = &resolved.0.roots[1].as_decl().kind else {
            panic!("expected desugared func let")
        };
        let ExprKind::Func(func) = &rhs.kind else {
            panic!("expected func")
        };
        let param_symbol = func.generics[0]
            .name
            .symbol()
            .expect("resolved static param");
        let Some(TypeAnnotation {
            kind: TypeAnnotationKind::Nominal { generics, .. },
            ..
        }) = &func.params[0].type_annotation
        else {
            panic!("expected nominal parameter annotation")
        };
        assert!(matches!(
            &generics[0],
            crate::node_kinds::generic_arg::GenericArg::Type(TypeAnnotation {
                kind: TypeAnnotationKind::Nominal { name, .. },
                ..
            }) if name.symbol().ok() == Some(param_symbol)
        ));
    }

    #[test]
    #[allow(non_snake_case)]
    fn resolves___IR() {
        let resolved = resolve(
            "
        __IR(\"$0 = add int 1 2\")
        ",
        );
        assert_eq!(
            *resolved.0.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Variable(Name::Resolved(
                    Symbol::IR,
                    "__IR".into()
                )))
                .into(),
                type_args: vec![],
                args: vec![any!(CallArg, {
                    origin: CallArgOrigin::Written,
                    mode: None,
                    mode_span: None,
                    label: Label::Positional(0),
                    label_span: Span::ANY,
                    value: any_expr!(ExprKind::LiteralString("$0 = add int 1 2".into()))
                })],
                trailing_block: None,
                desugared_operator: None,
            })
        );
    }

    #[test]
    #[ignore = "requires core"]
    #[allow(non_snake_case)]
    fn resolves_Optional() {
        let resolved = resolve(
            "
            Optional.none
        ",
        );
        assert_eq!(
            *resolved.0.roots[0].as_stmt(),
            any_expr_stmt!(ExprKind::Member(
                Some(
                    any_expr!(ExprKind::Constructor(
                        Name::Resolved(
                            EnumId {
                                local_id: 1,
                                module_id: ModuleId::Core
                            }
                            .into(),
                            "Optional".into(),
                        ),
                        vec![]
                    ))
                    .into()
                ),
                "none".into(),
                Span::ANY,
            ))
        )
    }

    #[test]
    fn resolves_type_alias() {
        let resolved = resolve("typealias Intyfresh = Int ; Intyfresh");
        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::TypeAlias(
                Name::Resolved(Symbol::TypeAlias(TypeAliasId::from(1)), "Intyfresh".into()),
                Span::ANY,
                annotation!(TypeAnnotationKind::Nominal {
                    name: Name::Resolved(Symbol::Int, "Int".into()),
                    name_span: Span::ANY,
                    generics: vec![]
                })
            ))
        );

        assert_eq!(
            *resolved.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Constructor(
                Name::Resolved(Symbol::TypeAlias(TypeAliasId::from(1)), "Intyfresh".into()),
                vec![]
            ))
        );
    }

    #[test]
    fn resolves_struct() {
        let resolved = resolve("struct Person {}");
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Init {
                    name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                    params: vec![param!(
                        ParamLocalId(2),
                        "self",
                        annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                            StructId::from(1).into(),
                            "Self".into()
                        )))
                    )],
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        ParamLocalId(2).into(),
                        "self".into()
                    )))])
                })])
            })
        )
    }

    #[test]
    fn resolves_struct_properties() {
        let resolved = resolve(
            "
        struct Person {
            let me: Person
        }
        ",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![
                            param!(
                                ParamLocalId(3),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    StructId::from(1).into(),
                                    "Self".into()
                                )))
                            ),
                            param!(
                                ParamLocalId(4),
                                "me",
                                annotation!(TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                                    name_span: Span::ANY,
                                    generics: vec![],
                                }),
                                synthetic_label: "me",
                                mode: Some(ParamMode::Consume)
                            )
                        ],
                        body: any_block!(vec![
                            any_stmt!(StmtKind::Assignment(
                                any_expr!(ExprKind::Member(
                                    Some(variable!(ParamLocalId(3), "self").into()),
                                    Label::Named("me".into()),
                                    Span::ANY
                                ))
                                .into(),
                                variable!(ParamLocalId(4), "me").into()
                            ))
                            .into(),
                            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                                ParamLocalId(3).into(),
                                "self".into()
                            )))
                        ])
                    }),
                    any_decl!(DeclKind::Property {
                        name: Name::Resolved(Symbol::Property(PropertyId::from(1)), "me".into()),
                        name_span: Span::ANY,
                        is_static: false,
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                            name_span: Span::ANY,
                            generics: vec![]
                        })),
                        default_value: None
                    })
                ])
            })
        )
    }

    #[test]
    fn resolves_struct_init() {
        let resolved = resolve(
            "
        struct Person {
            init() {}
        }
        ",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Init {
                    name: Name::Resolved(
                        Symbol::Initializer(InitializerId::from(1)),
                        "init".into()
                    ),
                    params: vec![param!(
                        Symbol::ParamLocal(ParamLocalId(1)),
                        "self",
                        annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                            Symbol::Struct(StructId::from(1)),
                            "Self".into()
                        )))
                    )],
                    body: any_block!(vec![])
                })])
            })
        )
    }

    #[test]
    fn resolves_generic_struct_properties() {
        let resolved = resolve(
            "
        struct Person<T> {
            let me: T
        }
        ",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![GenericDecl {
                    id: NodeID::ANY,
                    name: Name::Resolved(test_type_param(1), "T".into()),
                    name_span: Span::ANY,
                    generics: vec![],
                    conformances: vec![],
                    default: None,
                    static_ty: None,
                    span: Span::ANY
                }],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![
                            param!(
                                ParamLocalId(3),
                                "self",
                                annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                    StructId::from(1).into(),
                                    "Self".into()
                                )))
                            ),
                            param!(
                                ParamLocalId(4),
                                "me",
                                annotation!(TypeAnnotationKind::Nominal {
                                    name: Name::Resolved(test_type_param(1), "T".into()),
                                    name_span: Span::ANY,
                                    generics: vec![],
                                }),
                                synthetic_label: "me",
                                mode: Some(ParamMode::Consume)
                            )
                        ],
                        body: any_block!(vec![
                            any_stmt!(StmtKind::Assignment(
                                any_expr!(ExprKind::Member(
                                    Some(variable!(ParamLocalId(3), "self").into()),
                                    Label::Named("me".into()),
                                    Span::ANY
                                ))
                                .into(),
                                variable!(ParamLocalId(4), "me").into()
                            ))
                            .into(),
                            any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                                ParamLocalId(3).into(),
                                "self".into()
                            )))
                        ])
                    }),
                    any_decl!(DeclKind::Property {
                        name: Name::Resolved(Symbol::Property(PropertyId::from(1)), "me".into()),
                        name_span: Span::ANY,
                        is_static: false,
                        type_annotation: Some(annotation!(TypeAnnotationKind::Nominal {
                            name: Name::Resolved(test_type_param(1), "T".into()),
                            name_span: Span::ANY,
                            generics: vec![]
                        })),
                        default_value: None
                    })
                ])
            })
        )
    }

    #[test]
    fn resolves_static_struct_methods() {
        let resolved = resolve(
            "struct Person {
                static func fizz() {}
            }",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![param!(
                            ParamLocalId(2),
                            "self",
                            annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                StructId::from(1).into(),
                                "Self".into()
                            )))
                        )],
                        body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                            ParamLocalId(2).into(),
                            "self".into()
                        )))])
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            origin: FuncOrigin::Decl,
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::StaticMethod(StaticMethodId::from(1)),
                                "fizz".into()
                            ),
                            name_span: Span::ANY,
                            effects: Default::default(),
                            generics: vec![],
                            captures: vec![],
                            where_clause: None,
                            params: vec![],
                            body: any_block!(vec![]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: true,
                        receiver_mode: ReceiverMode::None
                    }),
                ])
            })
        )
    }

    #[test]
    fn resolves_struct_methods() {
        let resolved = resolve(
            "struct Person {
                func fizz() {
                    self.buzz()
                }

                func buzz() {
                    self.fizz()
                }
            }",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Struct {
                linear: false,
                heap: false,
                name: Name::Resolved(StructId::from(1).into(), "Person".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(DeclKind::Init {
                        name: Name::Resolved(SynthesizedId::from(1).into(), "init".into()),
                        params: vec![param!(
                            ParamLocalId(2),
                            "self",
                            annotation!(TypeAnnotationKind::SelfType(Name::Resolved(
                                StructId::from(1).into(),
                                "Self".into()
                            )))
                        )],
                        body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                            ParamLocalId(2).into(),
                            "self".into()
                        )))])
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            origin: FuncOrigin::Decl,
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId::from(1)),
                                "fizz".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            captures: vec![],
                            where_clause: None,
                            effects: Default::default(),
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(3)),
                                "self",
                                annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        Name::Resolved(StructId::from(1).into(), "Self".into())
                                    )))
                                })
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(
                                        any_expr!(ExprKind::Variable(Name::Resolved(
                                            Symbol::ParamLocal(ParamLocalId(3)),
                                            "self".into()
                                        )))
                                        .into()
                                    ),
                                    "buzz".into(),
                                    Span::ANY,
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![],
                                trailing_block: None,
                                desugared_operator: None,
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false,
                        receiver_mode: ReceiverMode::None
                    }),
                    any_decl!(DeclKind::Method {
                        func: Box::new(Func {
                            origin: FuncOrigin::Decl,
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::InstanceMethod(InstanceMethodId::from(2)),
                                "buzz".into()
                            ),
                            name_span: Span::ANY,
                            effects: Default::default(),
                            generics: vec![],
                            captures: vec![],
                            where_clause: None,
                            params: vec![param!(
                                Symbol::ParamLocal(ParamLocalId(4)),
                                "self",
                                annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        Name::Resolved(StructId::from(1).into(), "Self".into())
                                    )))
                                })
                            )],
                            body: any_block!(vec![any_expr_stmt!(ExprKind::Call {
                                callee: any_expr!(ExprKind::Member(
                                    Some(Box::new(any_expr!(ExprKind::Variable(Name::Resolved(
                                        Symbol::ParamLocal(ParamLocalId(4)),
                                        "self".into()
                                    ))))),
                                    "fizz".into(),
                                    Span::ANY,
                                ))
                                .into(),
                                type_args: vec![],
                                args: vec![],
                                trailing_block: None,
                                desugared_operator: None,
                            })]),
                            ret: None,
                            attributes: vec![]
                        }),
                        is_static: false,
                        receiver_mode: ReceiverMode::None
                    })
                ])
            })
        )
    }

    #[test]
    fn resolves_struct_constructor() {
        let resolved = resolve(
            "
        struct Person {}
        Person()
        ",
        );
        assert_eq!(
            *resolved.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Call {
                callee: any_expr!(ExprKind::Constructor(
                    Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                    vec![]
                ))
                .into(),
                type_args: vec![],
                args: vec![],
                trailing_block: None,
                desugared_operator: None,
            })
        )
    }

    #[test]
    fn resolves_struct_extension() {
        let resolved = resolve(
            "
        struct Person {}
        extend Person {}
        ",
        );
        assert_eq!(
            *resolved.0.roots[1].as_decl(),
            any_decl!(DeclKind::Extend {
                binders: vec![],
                head: TypeApplication {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                    name_span: Span::ANY,
                    args: vec![],
                },
                conformances: vec![],
                where_clause: None,
                body: any_body!(vec![])
            }),
        )
    }

    #[test]
    fn resolves_struct_extension_out_of_order() {
        let resolved = resolve(
            "
        extend Person {
            func fizz() {}
        }
        struct Person {}
        ",
        );
        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Extend {
                binders: vec![],
                head: TypeApplication {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    name: Name::Resolved(Symbol::Struct(StructId::from(1)), "Person".into()),
                    name_span: Span::ANY,
                    args: vec![],
                },
                conformances: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::Method {
                    func: Box::new(Func {
                        origin: FuncOrigin::Decl,
                        id: NodeID::ANY,
                        name: Name::Resolved(
                            Symbol::InstanceMethod(InstanceMethodId::from(1)),
                            "fizz".into()
                        ),
                        name_span: Span::ANY,
                        generics: vec![],
                        captures: vec![],
                        where_clause: None,
                        effects: Default::default(),
                        params: vec![Parameter {
                            label: None,
                            label_span: None,
                            mode: None,
                            mode_span: None,
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::ParamLocal(ParamLocalId(2)),
                                "self".into()
                            ),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                mutable: false,
                                inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                    Name::Resolved(
                                        Symbol::Struct(StructId::from(1)),
                                        "Self".into()
                                    )
                                )))
                            })),
                            span: Span::ANY,
                        }],
                        body: any_block!(vec![]),
                        ret: None,
                        attributes: vec![]
                    }),
                    is_static: false,
                    receiver_mode: ReceiverMode::None
                })])
            }),
        )
    }

    #[test]
    fn resolves_struct_child_types() {
        let resolved = resolve(
            "
        struct A {
            struct B {}
            typealias C = Int
            enum D {}
        }
        ",
        );
        assert_eq!(
            *resolved
                .1
                .child_types
                .get(&Symbol::Struct(StructId::from(1)))
                .unwrap(),
            indexmap::indexmap! {
                "B".into() => Symbol::Struct(StructId::from(2)),
                "C".into() => Symbol::TypeAlias(TypeAliasId::from(4)),
                "D".into() => Symbol::Enum(EnumId::from(3))
            }
        )
    }

    #[test]
    fn resolves_enum_child_types() {
        let resolved = resolve(
            "
        enum A {
            struct B {}
            typealias C = Int
            enum D {}
        }
        ",
        );
        assert_eq!(
            *resolved
                .1
                .child_types
                .get(&Symbol::Enum(EnumId::from(1)))
                .unwrap(),
            indexmap::indexmap! {
                "B".into() => Symbol::Struct(StructId::from(2)),
                "C".into() => Symbol::TypeAlias(TypeAliasId::from(4)),
                "D".into() => Symbol::Enum(EnumId::from(3))
            }
        )
    }

    #[test]
    fn resolves_protocol_child_types() {
        let resolved = resolve(
            "
        protocol A {
            struct B {}
            typealias C = Int
            enum D {}
            associated E
        }
        ",
        );
        assert_eq!(
            *resolved
                .1
                .child_types
                .get(&Symbol::Protocol(ProtocolId::from(1)))
                .unwrap(),
            indexmap::indexmap! {
                "B".into() => Symbol::Struct(StructId::from(1)),
                "C".into() => Symbol::TypeAlias(TypeAliasId::from(3)),
                "D".into() => Symbol::Enum(EnumId::from(2)),
                "E".into() => Symbol::AssociatedType(AssociatedTypeId::from(1))
            }
        )
    }

    #[test]
    fn resolves_enum() {
        let resolved = resolve(
            "
        enum Fizz {
            case foo, bar
        }
        ",
        );

        assert_eq!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Enum {
                linear: false,
                heap: false,
                name: Name::Resolved(Symbol::Enum(EnumId::from(1)), "Fizz".into()),
                name_span: Span::ANY,
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(enum_variant(
                        Name::Resolved(Symbol::Variant(VariantId::from(1)), "foo".into()),
                        Span::ANY,
                        vec![]
                    )),
                    any_decl!(enum_variant(
                        Name::Resolved(Symbol::Variant(VariantId::from(2)), "bar".into()),
                        Span::ANY,
                        vec![]
                    )),
                ])
            })
        )
    }

    #[test]
    fn resolves_protocol() {
        let resolved = resolve(
            "
            protocol Fizzable {
                func buzz() -> ()
            }
        ",
        );

        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: Name::Resolved(Symbol::Protocol(ProtocolId::from(1)), "Fizzable".into()),
                name_span: Span::ANY,
                conformances: vec![],
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![any_decl!(DeclKind::MethodRequirement {
                    signature: FuncSignature {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        name: Name::Resolved(
                            Symbol::MethodRequirement(MethodRequirementId::from(1)),
                            "buzz".into()
                        ),
                        effects: Default::default(),
                        params: vec![Parameter {
                            label: None,
                            label_span: None,
                            mode: None,
                            mode_span: None,
                            id: NodeID::ANY,
                            name: Name::Resolved(ParamLocalId::from(1u32).into(), "self".into()),
                            name_span: Span::ANY,
                            type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                mutable: false,
                                inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                    Name::Resolved(ProtocolId::from(1).into(), "Self".into())
                                )))
                            })),
                            span: Span::ANY
                        }],
                        generics: vec![],
                        where_clause: None,
                        ret: Some(Box::new(annotation!(TypeAnnotationKind::Tuple(vec![]))))
                    },
                    receiver_mode: ReceiverMode::None
                })])
            })
        )
    }

    #[test]
    fn resolves_protocol_associated_types() {
        let resolved = resolve(
            "
            protocol Fizzable {
                associated T

                func buzz() -> T
            }
        ",
        );

        assert_eq_diff!(
            *resolved.0.roots[0].as_decl(),
            any_decl!(DeclKind::Protocol {
                name: Name::Resolved(Symbol::Protocol(ProtocolId::from(1)), "Fizzable".into()),
                name_span: Span::ANY,
                conformances: vec![],
                generics: vec![],
                where_clause: None,
                body: any_body!(vec![
                    any_decl!(DeclKind::Associated {
                        generic: GenericDecl {
                            id: NodeID::ANY,
                            name: Name::Resolved(
                                Symbol::AssociatedType(AssociatedTypeId::from(1)),
                                "T".into()
                            ),
                            name_span: Span::ANY,
                            generics: vec![],
                            conformances: vec![],
                            default: None,
                            static_ty: None,
                            span: Span::ANY
                        },
                        where_clause: None
                    }),
                    any_decl!(DeclKind::MethodRequirement {
                        signature: FuncSignature {
                            id: NodeID::ANY,
                            span: Span::ANY,
                            name: Name::Resolved(
                                Symbol::MethodRequirement(MethodRequirementId::from(1)),
                                "buzz".into()
                            ),
                            params: vec![Parameter {
                                label: None,
                                label_span: None,
                                mode: None,
                                mode_span: None,
                                id: NodeID::ANY,
                                name: Name::Resolved(
                                    ParamLocalId::from(1u32).into(),
                                    "self".into()
                                ),
                                name_span: Span::ANY,
                                type_annotation: Some(annotation!(TypeAnnotationKind::Borrow {
                                    mutable: false,
                                    inner: Box::new(annotation!(TypeAnnotationKind::SelfType(
                                        Name::Resolved(ProtocolId::from(1).into(), "Self".into())
                                    )))
                                })),
                                span: Span::ANY
                            }],
                            effects: Default::default(),
                            generics: vec![],
                            where_clause: None,
                            ret: Some(Box::new(annotation!(TypeAnnotationKind::Nominal {
                                name: Name::Resolved(
                                    Symbol::AssociatedType(AssociatedTypeId::from(1)),
                                    "T".into()
                                ),
                                name_span: Span::ANY,
                                generics: vec![]
                            })))
                        },
                        receiver_mode: ReceiverMode::None
                    }),
                ])
            })
        )
    }

    #[test]
    fn resolves_match() {
        let resolved = resolve(
            "
        let a = 123
        match a {
            b -> b
        }
        ",
        );

        assert_eq!(
            *resolved.0.roots[1].as_stmt(),
            any_expr_stmt!(ExprKind::Match(
                Box::new(variable!(GlobalId::from(1), "a")),
                vec![MatchArm {
                    id: NodeID::ANY,
                    span: Span::ANY,
                    pattern: Pattern {
                        id: NodeID::ANY,
                        span: Span::ANY,
                        kind: PatternKind::Bind(Name::Resolved(
                            Symbol::PatternBindLocal(PatternBindLocalId(1)),
                            "b".into()
                        ))
                    },
                    body: any_block!(vec![any_expr_stmt!(ExprKind::Variable(Name::Resolved(
                        Symbol::PatternBindLocal(PatternBindLocalId(1)),
                        "b".into()
                    )))])
                }]
            ))
        );
    }

    #[test]
    fn match_doesnt_leak() {
        let resolved = resolve_err(
            "
        match 123 {
            b -> b
        }

        b
        ",
        );

        assert_eq!(
            resolved.1.diagnostics.len(),
            1,
            "{:?}",
            resolved.1.diagnostics
        );
    }

    #[test]
    fn or_patterns_resolve_binds() {
        // An or-pattern let desugars (in the parser) to
        // `let x = match … { .a(x) | .b(x) -> x }`; both alternatives
        // must bind the same symbol, and the outer binder carries the
        // name into the enclosing scope.
        let resolved = resolve(
            "
        let .a(x) | .b(x)
        ",
        );

        let decl = resolved.0.roots[0].as_decl().clone();
        let DeclKind::Let {
            lhs,
            rhs: Some(rhs),
            ..
        } = &decl.kind
        else {
            panic!("expected a desugared let, got {decl:?}");
        };
        assert!(
            matches!(&lhs.kind, PatternKind::Bind(name) if name.name_str() == "x"),
            "outer binder: {lhs:?}"
        );
        let ExprKind::Match(_, arms) = &rhs.kind else {
            panic!("expected a match rhs, got {rhs:?}");
        };
        assert_eq!(arms.len(), 1, "no else: a miss is the match machinery's");
        let PatternKind::Or(alternatives) = &arms[0].pattern.kind else {
            panic!("expected the or-pattern in the arm: {:?}", arms[0].pattern);
        };
        let binder_symbol = |pattern: &Pattern| match &pattern.kind {
            PatternKind::Variant { fields, .. } => match &fields[0].kind {
                PatternKind::Bind(name) => name.symbol().expect("resolved"),
                other => panic!("expected a bind, got {other:?}"),
            },
            other => panic!("expected a variant alternative, got {other:?}"),
        };
        assert_eq!(
            binder_symbol(&alternatives[0]),
            binder_symbol(&alternatives[1]),
            "both alternatives bind the same symbol"
        );
    }

    #[test]
    fn or_patterns_require_matching_binds() {
        let resolved = resolve_err(
            "
        let .a(x) | .b(y)
        ",
        );

        assert_eq!(
            resolved.1.diagnostics.len(),
            1,
            "{:?}",
            resolved.1.diagnostics
        );
    }

    #[test]
    fn resolves_effect_decl() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        ",
        );

        let Decl {
            kind:
                DeclKind::Effect {
                    name: Name::Resolved(Symbol::Effect(..), ..),
                    params,
                    ..
                },
            ..
        } = &resolved.0.roots[0].as_decl()
        else {
            panic!("didn't get decl");
        };

        assert_eq!(
            *params,
            vec![any!(Parameter ,{
                label: Some(ParamLabel::Named("x".into())),
                label_span: Some(Span::ANY),
                mode: Some(ParamMode::Consume),
                mode_span: None,
                name: Name::Resolved(ParamLocalId(1).into(), "x".into()),
                name_span: Span::ANY,
                type_annotation: Some(any!(TypeAnnotation, {
                    kind: TypeAnnotationKind::Nominal { name: Name::Resolved(Symbol::Int, "Int".into()), name_span: Span::ANY, generics: vec![] }
                })),
            })],
        );
    }

    #[test]
    fn resolves_handle_stmt() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        #handle 'fizz { x in
            'continue x
        }
        ",
        );

        let Stmt {
            kind:
                StmtKind::Handling {
                    effect_name: Name::Resolved(Symbol::Effect(..), ..),
                    body: Block { args, body, .. },
                    ..
                },
            ..
        } = resolved.0.roots[1].as_stmt()
        else {
            panic!("didn't get decl: {:?}", resolved.0.roots[1])
        };

        assert_eq!(
            *args,
            vec![any!(Parameter, {
                    label: None,
                    label_span: None,
                    mode: Some(ParamMode::Borrow),
                    mode_span: None,
                name: Name::Resolved(Symbol::ParamLocal(ParamLocalId(2)), "x".into()),
                name_span: Span::ANY,
                type_annotation: None
            })]
        );

        assert_eq!(
            *body,
            vec![
                any_stmt!(StmtKind::Resume(Some(any_expr!(ExprKind::Variable(
                    Name::Resolved(Symbol::ParamLocal(ParamLocalId(2)), "x".into())
                )))))
                .into()
            ]
        )
    }

    #[test]
    fn resolves_effect_call() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        'fizz(123)
        ",
        );

        assert_eq!(
            resolved.0.roots[1],
            any_expr_stmt!(ExprKind::CallEffect {
                effect_name: Name::Resolved(Symbol::Effect(EffectId::from(1)), "fizz".into()),
                effect_name_span: Span::ANY,
                type_args: vec![],
                args: vec![any!(CallArg, {
                    origin: CallArgOrigin::Written,
                    mode: None,
                    mode_span: None,
                    label: Label::Positional(0),
                    label_span: Span::ANY,
                    value: any_expr!(ExprKind::LiteralInt("123".into()))
                })]
            })
        );
    }

    #[test]
    fn resolves_effect_annotation() {
        let resolved = resolve(
            "
        effect 'fizz(x: Int) -> ()
        func fizzes() 'fizz {}
        ",
        );

        assert_eq_diff!(
            *resolved.0.roots[1].as_decl(),
            any_decl!(DeclKind::Let {
                lhs: any!(Pattern, {
                    kind: PatternKind::Bind(Name::Resolved(Symbol::Global(1.into()), "fizzes".into()))
                }),
                type_annotation: None,
                rhs: Some(any_expr!(ExprKind::Func(Func {
                    origin: FuncOrigin::Decl,
                    id: NodeID::ANY,
                    name: Name::Resolved(Symbol::Global(1.into()), "fizzes".into()),
                    name_span: Span::ANY,
                    effects: EffectSet {
                        names: vec![Name::Resolved(Symbol::Effect(1.into()), "fizz".into())],
                        spans: vec![Span::ANY],
                        is_open: false
                    },
                    generics: vec![],
                    captures: vec![],
                    where_clause: None,
                    params: vec![],
                    body: any_block!(vec![]),
                    ret: None,
                    attributes: vec![]
                }))),
            })
        );
    }

    #[test]
    fn tracks_mutated_globals() {
        let resolved = resolve(
            "
            let foo = 123
            let bar = 456
            foo = 789
        ",
        );

        assert_eq!(
            resolved.1.mutated_symbols,
            indexset! { Symbol::Global(1.into()) }
        );
    }

    #[test]
    fn tracks_mutated_members() {
        let resolved = resolve(
            "
            let a = { b: 123 }
            a.b = 123
        ",
        );

        assert_eq!(
            resolved.1.mutated_symbols,
            indexset! { Symbol::Global(1.into()) }
        );
    }

    #[test]
    fn tracks_nested_mutated_members() {
        let resolved = resolve(
            "
            let a = { b: { c: 123 }}
            a.b.c = 456
        ",
        );

        assert_eq!(
            resolved.1.mutated_symbols,
            indexset! { Symbol::Global(1.into()) }
        );
    }

    /// Helper to resolve multiple files with isolated modules enabled
    fn resolve_multi(files: &[(&str, &str)]) -> (Vec<AST<NameResolved>>, ResolvedNames) {
        let modules = ModuleEnvironment::default();
        let mut name_resolver = NameResolver::with_source_root(
            Rc::new(modules),
            ModuleId::Current,
            std::path::PathBuf::from("."),
        );
        let mut parseds = Vec::new();

        for (i, (path, code)) in files.iter().enumerate() {
            let (ast, _) =
                crate::compiling::frontend::parse_ast(code, FileID(i as u32), path).unwrap();
            parseds.push(ast);
        }

        crate::desugar::desugar(&mut parseds);
        name_resolver.resolve(parseds)
    }

    #[test]
    fn resolves_named_import() {
        let (asts, resolved) = resolve_multi(&[
            ("./utils.tlk", "pub let helper = 42"),
            ("./main.tlk", "use package::utils::{ helper }\nhelper"),
        ]);

        // Check that the main file resolved 'helper' to the symbol from utils
        assert!(
            resolved.diagnostics.is_empty(),
            "Expected no errors but got: {:?}",
            resolved.diagnostics
        );

        // The second file should have resolved the variable reference
        let main_ast = &asts[1];
        // Check the last statement (the 'helper' reference) resolved correctly
        if let crate::node::Node::Stmt(Stmt {
            kind:
                StmtKind::Expr(Expr {
                    kind: ExprKind::Variable(name),
                    ..
                }),
            ..
        }) = &main_ast.roots[1]
        {
            assert!(
                matches!(name, Name::Resolved(Symbol::Global(_), _)),
                "Expected resolved global, got {name:?}"
            );
        } else {
            panic!("Expected variable expression");
        }
    }

    #[test]
    fn resolves_import_all() {
        let (asts, resolved) = resolve_multi(&[
            ("./lib.tlk", "pub let a = 1\npub let b = 2"),
            ("./main.tlk", "use package::lib\na\nb"),
        ]);

        assert!(
            resolved.diagnostics.is_empty(),
            "Expected no errors but got: {:?}",
            resolved.diagnostics
        );

        // Both 'a' and 'b' should be resolved in main
        let main_ast = &asts[1];
        assert!(main_ast.roots.len() >= 3, "Expected at least 3 roots");
    }

    // ADR 0042 stage 2: the resolver records each declared symbol's
    // defining file, owner, role, and visibility in one semantic product.
    #[test]
    fn declaration_records_carry_file_owner_role_and_visibility() {
        use crate::name_resolution::symbol::SymbolKind;
        use crate::node_kinds::decl::Visibility;

        let (_, resolved) = resolve(
            "pub struct Account {\n\tpub let display_name: Int\n\tlet token: Int\n\tpub func label() -> Int { 1 }\n}",
        );

        let symbol_named = |name: &str, role: SymbolKind| {
            *resolved
                .symbol_names
                .iter()
                .find(|(sym, n)| {
                    n.as_str() == name
                        && resolved
                            .declarations
                            .get(sym)
                            .is_some_and(|record| record.role == role)
                })
                .unwrap_or_else(|| panic!("no {role:?} symbol named {name}"))
                .0
        };

        let account = symbol_named("Account", SymbolKind::Struct);
        let record = resolved.declarations.get(&account).expect("Account record");
        assert_eq!(record.file, FileID(0));
        assert_eq!(record.owner, None);
        assert_eq!(record.role, SymbolKind::Struct);
        assert_eq!(record.declared, Visibility::Public);
        assert_eq!(record.effective, Visibility::Public);

        let display_name = symbol_named("display_name", SymbolKind::Property);
        let record = resolved.declarations.get(&display_name).expect("record");
        assert_eq!(record.file, FileID(0));
        assert_eq!(record.owner, Some(account));
        assert_eq!(record.role, SymbolKind::Property);
        assert_eq!(record.declared, Visibility::Public);

        let token = symbol_named("token", SymbolKind::Property);
        let record = resolved.declarations.get(&token).expect("record");
        assert_eq!(record.owner, Some(account));
        assert_eq!(record.declared, Visibility::Private);

        let label = symbol_named("label", SymbolKind::InstanceMethod);
        let record = resolved.declarations.get(&label).expect("record");
        assert_eq!(record.owner, Some(account));
        assert_eq!(record.role, SymbolKind::InstanceMethod);
        assert_eq!(record.declared, Visibility::Public);
    }

    #[test]
    fn public_member_with_private_owner_is_rejected() {
        for code in [
            "struct Hidden {\n\tpub func reveal() -> Int { 1 }\n}",
            "struct Hidden {\n\tpub let field: Int\n}",
            "struct Outer {\n\tpub struct Inner {}\n}",
            "struct Hidden {}\nextend Hidden {\n\tpub func reveal() -> Int { 1 }\n}",
        ] {
            let (_, resolved) = resolve_err(code);
            assert!(
                resolved.diagnostics.iter().any(|d| matches!(
                    d,
                    AnyDiagnostic::NameResolution(Diagnostic {
                        kind: NameResolverError::PublicMemberPrivateOwner { .. },
                        ..
                    })
                )),
                "expected public-member-private-owner diagnostic for {code:?}, got {:?}",
                resolved.diagnostics
            );
        }
    }

    #[test]
    fn public_member_with_public_owner_is_accepted() {
        let (_, resolved) =
            resolve("pub struct Open {}\nextend Open {\n\tpub func fine() -> Int { 1 }\n}");
        assert!(resolved.diagnostics.is_empty());
    }

    // ADR 0042 stage 3: import insertion never overwrites an existing
    // declaration or import; collisions are structured diagnostics.
    #[test]
    fn named_import_collision_with_local_declaration_diagnoses() {
        for local in ["pub let value = 2", "let value = 2"] {
            let (_, resolved) = resolve_multi(&[
                ("./lib.tlk", "pub let value = 1"),
                (
                    "./main.tlk",
                    &format!("{local}\nuse package::lib::{{ value }}"),
                ),
            ]);
            assert!(
                resolved.diagnostics.iter().any(|d| matches!(
                    d,
                    AnyDiagnostic::NameResolution(Diagnostic {
                        kind: NameResolverError::ImportCollision { .. },
                        ..
                    })
                )),
                "expected import collision with {local:?}, got {:?}",
                resolved.diagnostics
            );
        }
    }

    #[test]
    fn two_named_imports_of_different_symbols_collide() {
        let (_, resolved) = resolve_multi(&[
            ("./lib_a.tlk", "pub let shared = 1"),
            ("./lib_b.tlk", "pub let shared = 2"),
            (
                "./main.tlk",
                "use package::lib_a::{ shared }\nuse package::lib_b::{ shared }",
            ),
        ]);
        assert!(
            resolved.diagnostics.iter().any(|d| matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::ImportCollision { .. },
                    ..
                })
            )),
            "expected import collision, got {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn aliased_import_avoids_collision() {
        let (_, resolved) = resolve_multi(&[
            ("./lib_a.tlk", "pub let shared = 1"),
            ("./lib_b.tlk", "pub let shared = 2"),
            (
                "./main.tlk",
                "use package::lib_a::{ shared }\nuse package::lib_b::{ shared as other }\nshared\nother",
            ),
        ]);
        assert!(
            resolved.diagnostics.is_empty(),
            "expected no diagnostics, got {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn import_all_collision_diagnoses() {
        let (_, resolved) = resolve_multi(&[
            ("./lib_a.tlk", "pub let shared = 1"),
            ("./lib_b.tlk", "pub let shared = 2"),
            ("./main.tlk", "use package::lib_a\nuse package::lib_b"),
        ]);
        assert!(
            resolved.diagnostics.iter().any(|d| matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::ImportCollision { .. },
                    ..
                })
            )),
            "expected import collision, got {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn reimporting_the_same_symbol_is_not_a_collision() {
        let (_, resolved) = resolve_multi(&[
            ("./lib.tlk", "pub let value = 1"),
            (
                "./main.tlk",
                "use package::lib::{ value }\nuse package::lib\nvalue",
            ),
        ]);
        assert!(
            resolved.diagnostics.is_empty(),
            "expected no diagnostics, got {:?}",
            resolved.diagnostics
        );
    }

    // ADR 0042 stage 3: every binder of a public top-level destructuring
    // declaration is predeclared and exported.
    #[test]
    fn public_destructuring_binders_are_importable() {
        let (_, resolved) = resolve_multi(&[
            ("./lib.tlk", "pub let (first, second) = (1, 2)"),
            (
                "./main.tlk",
                "use package::lib::{ first, second }\nfirst\nsecond",
            ),
        ]);
        assert!(
            resolved.diagnostics.is_empty(),
            "expected no diagnostics, got {:?}",
            resolved.diagnostics
        );
    }

    // ADR 0042: duplicate exported declaration keys diagnose; they are
    // never resolved by declaration or map order.
    #[test]
    fn duplicate_public_type_across_files_diagnoses() {
        let (_, resolved) = resolve_multi(&[
            ("./lib_a.tlk", "pub struct Thing {}"),
            ("./lib_b.tlk", "pub struct Thing {}"),
        ]);
        assert!(
            resolved.diagnostics.iter().any(|d| matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::DuplicateExport(_),
                    ..
                })
            )),
            "expected duplicate export, got {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn private_same_named_types_in_separate_files_are_legal() {
        let (_, resolved) = resolve_multi(&[
            ("./lib_a.tlk", "struct Helper {}"),
            ("./lib_b.tlk", "struct Helper {}"),
        ]);
        assert!(
            resolved.diagnostics.is_empty(),
            "expected no diagnostics, got {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn same_file_duplicate_nominals_diagnose() {
        for code in [
            "struct Twice {}\nstruct Twice {}",
            "struct Twice {}\nenum Twice { case a }",
        ] {
            let (_, resolved) = resolve_err(code);
            assert!(
                resolved.diagnostics.iter().any(|d| matches!(
                    d,
                    AnyDiagnostic::NameResolution(Diagnostic {
                        kind: NameResolverError::DuplicateDeclaration(_),
                        ..
                    })
                )),
                "expected duplicate declaration for {code:?}, got {:?}",
                resolved.diagnostics
            );
        }
    }

    #[test]
    fn import_nonexistent_symbol_errors() {
        let (_, resolved) = resolve_multi(&[
            ("./lib.tlk", "let existing = 1"),
            ("./main.tlk", "use package::lib::{ nonexistent }"),
        ]);

        assert!(
            !resolved.diagnostics.is_empty(),
            "Expected error for nonexistent symbol"
        );
    }

    #[test]
    fn import_nonexistent_module_errors() {
        let (_, resolved) = resolve_multi(&[("./main.tlk", "use package::missing::{ a }")]);

        assert!(
            !resolved.diagnostics.is_empty(),
            "Expected error for missing module"
        );
    }

    #[test]
    fn import_private_symbol_errors() {
        let (_, resolved) = resolve_multi(&[
            ("./lib.tlk", "let private_val = 42"),
            ("./main.tlk", "use package::lib::{ private_val }"),
        ]);

        assert!(
            !resolved.diagnostics.is_empty(),
            "Expected error for importing private symbol"
        );
        // Verify it's specifically a SymbolNotPublic error
        let has_private_error = resolved.diagnostics.iter().any(|d| {
            matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::SymbolNotPublic(_),
                    ..
                })
            )
        });
        assert!(has_private_error, "Expected SymbolNotPublic error");
    }

    #[test]
    fn duplicate_export_emits_error() {
        let code = r#"
pub let a = 1
pub let a = 2
"#;
        let (_, resolved) = resolve_err(code);
        let has_duplicate_error = resolved.diagnostics.iter().any(|d| {
            matches!(
                d,
                AnyDiagnostic::NameResolution(Diagnostic {
                    kind: NameResolverError::DuplicateExport(_),
                    ..
                })
            )
        });
        assert!(has_duplicate_error, "Expected DuplicateExport error");
    }

    #[test]
    fn core_prelude_imports_types_and_values() {
        use crate::compiling::core;

        // Get the compiled Core module
        let core_module = core::compile();
        let mut modules = ModuleEnvironment::default();
        modules.import_core(core_module);

        // Now resolve code that uses Core types without imports
        let code = "let x: Optional<Int> = Optional.some(42)";
        let parsed = parse(code);
        let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
        let mut parseds = vec![parsed];
        crate::desugar::desugar(&mut parseds);
        let (_, resolved) = name_resolver.resolve(parseds);

        assert!(
            resolved.diagnostics.is_empty(),
            "Expected no errors using Core prelude, got: {:?}",
            resolved.diagnostics
        );
    }

    #[test]
    fn no_core_directive_skips_core_prelude() {
        use crate::compiling::core;

        let code = "let x = 1";

        // Verify that without skip_core_prelude, the file scope contains Core symbols
        {
            let core_module = core::compile();
            let mut modules = ModuleEnvironment::default();
            modules.import_core(core_module);
            let parsed = parse(code);
            let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
            let mut parseds = vec![parsed];
            crate::desugar::desugar(&mut parseds);
            let (_, resolved) = name_resolver.resolve(parseds);
            let file_scope = resolved.scopes.get(&NodeID(FileID(0), 0)).unwrap();
            assert!(
                file_scope.types.contains_key("Optional"),
                "Without skip_core_prelude, file scope should contain Core types"
            );
        }

        // Now verify that with skip_core_prelude, the file scope does NOT contain Core symbols
        {
            let core_module = core::compile();
            let mut modules = ModuleEnvironment::default();
            modules.import_core(core_module);
            let mut parsed = parse(code);
            parsed.skip_core_prelude = true;
            let mut name_resolver = NameResolver::new(Rc::new(modules), ModuleId::Current);
            let mut parseds = vec![parsed];
            crate::desugar::desugar(&mut parseds);
            let (_, resolved) = name_resolver.resolve(parseds);
            let file_scope = resolved.scopes.get(&NodeID(FileID(0), 0)).unwrap();
            assert!(
                !file_scope.types.contains_key("Optional"),
                "With skip_core_prelude, file scope should NOT contain Core types"
            );
        }
    }
}
