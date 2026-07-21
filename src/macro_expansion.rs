use std::collections::{HashMap, HashSet};

use derive_visitor::{Drive, DriveMut, Visitor, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        attribute::Attribute,
        block::Block,
        call_arg::CallArg,
        decl::{Decl, DeclKind, MacroParameter},
        expr::{Expr, ExprKind},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        inline_ir_instruction::InlineIRInstruction,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::Pattern,
        record_field::RecordField,
        stmt::{Stmt, StmtKind},
        type_annotation::TypeAnnotation,
    },
    parser_error::ParserError,
};

const MAX_EXPANSIONS_PER_FILE: usize = 4096;

type MacroKey = (FileID, String, usize);

#[derive(Clone, Debug)]
struct MacroDefinition {
    params: Vec<MacroParameter>,
    template: Expr,
}

/// Expand ADR 0026's first, deliberately restricted expression-template
/// macros. Definitions are file-local in this slice.
pub fn expand_macros(asts: &mut [AST<Parsed>]) -> Vec<AnyDiagnostic> {
    expand_macros_with_sources(asts, &HashMap::new())
}

/// Expand macros with the original source text available to source-reflecting
/// built-ins such as `#assert`.
pub fn expand_macros_with_sources(
    asts: &mut [AST<Parsed>],
    sources: &HashMap<FileID, String>,
) -> Vec<AnyDiagnostic> {
    let mut definitions = HashMap::new();
    let mut diagnostics = Vec::new();

    for ast in asts.iter_mut() {
        let mut retained = Vec::with_capacity(ast.roots.len());
        for root in std::mem::take(&mut ast.roots) {
            let Node::Decl(decl) = &root else {
                retained.push(root);
                continue;
            };
            let DeclKind::Macro {
                name,
                name_span,
                params,
                template,
            } = &decl.kind
            else {
                retained.push(root);
                continue;
            };

            if name == "assert" {
                diagnostics.push(
                    Diagnostic {
                        id: decl.id,
                        severity: Severity::Error,
                        kind: ParserError::InvalidMacroTemplate {
                            name: name.clone(),
                            reason: "`assert` is a compiler-provided macro".into(),
                            span: decl.span,
                        },
                    }
                    .into(),
                );
                continue;
            }

            if decl.visibility == crate::node_kinds::decl::Visibility::Public {
                diagnostics.push(
                    Diagnostic {
                        id: decl.id,
                        severity: Severity::Error,
                        kind: ParserError::InvalidMacroTemplate {
                            name: name.clone(),
                            reason: "exported macros are not implemented".into(),
                            span: decl.span,
                        },
                    }
                    .into(),
                );
                continue;
            }

            let key = (ast.file_id, name.clone(), params.len());
            if definitions.contains_key(&key) {
                diagnostics.push(
                    Diagnostic {
                        id: decl.id,
                        severity: Severity::Error,
                        kind: ParserError::DuplicateMacroRule {
                            name: name.clone(),
                            arity: params.len(),
                            span: *name_span,
                        },
                    }
                    .into(),
                );
                continue;
            }

            match TemplateValidator::validate(params, template) {
                Ok(()) => {
                    definitions.insert(
                        key,
                        MacroDefinition {
                            params: params.clone(),
                            template: template.clone(),
                        },
                    );
                }
                Err(reason) => diagnostics.push(
                    Diagnostic {
                        id: decl.id,
                        severity: Severity::Error,
                        kind: ParserError::InvalidMacroTemplate {
                            name: name.clone(),
                            reason,
                            span: decl.span,
                        },
                    }
                    .into(),
                ),
            }
        }
        ast.roots = retained;
    }

    for ast in asts {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut expander = MacroExpander {
            file_id: ast.file_id,
            definitions: &definitions,
            diagnostics: Vec::new(),
            node_ids,
            expansions: 0,
            changed: false,
            source: sources.get(&ast.file_id).map(String::as_str),
        };
        loop {
            expander.changed = false;
            for root in &mut ast.roots {
                root.drive_mut(&mut expander);
            }
            if !expander.changed {
                break;
            }
        }
        ast.node_ids = expander.node_ids;
        diagnostics.extend(expander.diagnostics);
    }

    diagnostics
}

#[derive(Visitor)]
#[visitor(Node(enter), Expr(enter), Stmt(enter), TypeAnnotation(enter))]
struct TemplateValidator<'a> {
    params: HashSet<&'a str>,
    uses: HashMap<String, usize>,
    error: Option<String>,
}

impl<'a> TemplateValidator<'a> {
    fn validate(params: &'a [MacroParameter], template: &Expr) -> Result<(), String> {
        let mut names = HashSet::new();
        for param in params {
            if !names.insert(param.name.as_str()) {
                return Err(format!(
                    "parameter `${}` is declared more than once",
                    param.name
                ));
            }
        }

        let mut validator = Self {
            params: names,
            uses: HashMap::new(),
            error: None,
        };
        template.drive(&mut validator);

        if let Some(error) = validator.error {
            return Err(error);
        }
        if let Some((param, _)) = validator.uses.iter().find(|(_, uses)| **uses > 1) {
            return Err(format!(
                "expression parameter `${param}` is spliced more than once; explicit duplication is not implemented"
            ));
        }

        Ok(())
    }

    fn reject(&mut self, reason: impl Into<String>) {
        if self.error.is_none() {
            self.error = Some(reason.into());
        }
    }

    fn enter_node(&mut self, node: &Node) {
        if matches!(node, Node::Decl(_)) {
            self.reject("binding and declaration forms are not yet allowed");
        }
    }

    fn enter_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::For { .. } => self.reject("`for` introduces bindings"),
            StmtKind::Handling { .. } => {
                self.reject("effect names in templates require definition-site hygiene")
            }
            _ => {}
        }
    }

    fn enter_type_annotation(&mut self, _annotation: &TypeAnnotation) {
        self.reject("type names in templates require definition-site hygiene");
    }

    fn enter_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Variable(Name::Raw(name)) if name.starts_with('$') => {
                let param = &name[1..];
                if self.params.contains(param) {
                    *self.uses.entry(param.into()).or_default() += 1;
                } else {
                    self.reject(format!("unknown template parameter `${param}`"));
                }
            }
            ExprKind::Variable(name) => self.reject(format!(
                "free identifier `{}` requires definition-site hygiene",
                name.name_str()
            )),
            ExprKind::Constructor(name) => self.reject(format!(
                "constructor `{}` requires definition-site hygiene",
                name.name_str()
            )),
            ExprKind::CallEffect { .. } => {
                self.reject("effect names in templates require definition-site hygiene")
            }
            ExprKind::Func(_) => self.reject("function templates introduce bindings"),
            ExprKind::Match(..) => self.reject("match templates may introduce pattern bindings"),
            ExprKind::As(..) => {
                self.reject("type names in templates require definition-site hygiene")
            }
            ExprKind::InlineIR(..) => self.reject("inline IR is not valid macro template syntax"),
            _ => {}
        }
    }
}

#[derive(Debug, VisitorMut)]
#[visitor(Expr(enter))]
struct MacroExpander<'a> {
    file_id: FileID,
    definitions: &'a HashMap<MacroKey, MacroDefinition>,
    diagnostics: Vec<AnyDiagnostic>,
    node_ids: IDGenerator,
    expansions: usize,
    changed: bool,
    source: Option<&'a str>,
}

impl MacroExpander<'_> {
    fn error(&mut self, id: NodeID, kind: ParserError) {
        self.diagnostics.push(
            Diagnostic {
                id,
                severity: Severity::Error,
                kind,
            }
            .into(),
        );
    }

    fn replace_with_unit(&mut self, expr: &mut Expr) {
        expr.kind = ExprKind::Tuple(Vec::new());
        self.changed = true;
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn assertion_source(&self, condition: &Expr) -> String {
        let Some(source) = self.source else {
            return "<expression>".into();
        };
        source
            .get(condition.span.start as usize..condition.span.end as usize)
            .unwrap_or("<expression>")
            .to_string()
    }

    fn string_literal_contents(value: &str) -> String {
        let mut escaped = String::new();
        for ch in value.chars() {
            match ch {
                '"' => escaped.push_str("\\\""),
                '\\' => escaped.push_str("\\\\"),
                '\n' => escaped.push_str("\\n"),
                '\r' => escaped.push_str("\\r"),
                '\t' => escaped.push_str("\\t"),
                ch if ch <= '\u{1f}' => escaped.push_str(&format!("\\u{{{:x}}}", ch as u32)),
                ch => escaped.push(ch),
            }
        }
        escaped
    }

    fn expand_assert(&mut self, expr: &mut Expr, name: String, args: Vec<Expr>) {
        if args.len() != 1 {
            self.error(
                expr.id,
                ParserError::MacroArityMismatch {
                    name,
                    actual: args.len(),
                    expected: vec![1],
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        }

        let Some(condition) = args.into_iter().next() else {
            self.replace_with_unit(expr);
            return;
        };
        let message = format!("assertion failed: {}", self.assertion_source(&condition));
        let message = Expr {
            id: self.next_id(),
            span: condition.span,
            kind: ExprKind::LiteralString(Self::string_literal_contents(&message)),
        };
        let callee = Expr {
            id: self.next_id(),
            span: expr.span,
            kind: ExprKind::Variable(Name::Raw("testing::assert_message".into())),
        };
        let condition_id = self.next_id();
        let message_id = self.next_id();
        expr.id = self.next_id();
        expr.kind = ExprKind::Call {
            callee: Box::new(callee),
            type_args: Vec::new(),
            args: vec![
                CallArg {
                    id: condition_id,
                    label: Label::Positional(0),
                    label_span: condition.span,
                    value: condition,
                    span: expr.span,
                    mode: None,
                    mode_span: None,
                },
                CallArg {
                    id: message_id,
                    label: Label::Positional(1),
                    label_span: message.span,
                    value: message,
                    span: expr.span,
                    mode: None,
                    mode_span: None,
                },
            ],
            trailing_block: None,
            desugared_operator: None,
        };
        self.expansions += 1;
        self.changed = true;
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::MacroCall {
            name,
            name_span,
            args,
        } = expr.kind.clone()
        else {
            return;
        };

        if self.expansions >= MAX_EXPANSIONS_PER_FILE {
            self.error(
                expr.id,
                ParserError::MacroExpansionLimit {
                    name,
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        }

        if name == "assert" {
            self.expand_assert(expr, name, args);
            return;
        }

        let key = (self.file_id, name.clone(), args.len());
        let Some(definition) = self.definitions.get(&key).cloned() else {
            let mut expected: Vec<_> = self
                .definitions
                .keys()
                .filter_map(|(file, candidate, arity)| {
                    (*file == self.file_id && candidate == &name).then_some(*arity)
                })
                .collect();
            expected.sort_unstable();
            expected.dedup();
            let kind = if expected.is_empty() {
                ParserError::UndefinedMacro {
                    name,
                    span: name_span,
                }
            } else {
                ParserError::MacroArityMismatch {
                    name,
                    actual: args.len(),
                    expected,
                    span: expr.span,
                }
            };
            self.error(expr.id, kind);
            self.replace_with_unit(expr);
            return;
        };

        self.expansions += 1;
        let mut expanded = definition.template;
        expanded.drive_mut(&mut NodeIdRemapper {
            file_id: self.file_id,
            node_ids: &mut self.node_ids,
        });

        let substitutions = definition
            .params
            .iter()
            .zip(args)
            .map(|(param, arg)| (param.name.clone(), arg))
            .collect();
        expanded.drive_mut(&mut TemplateSubstituter { substitutions });
        *expr = expanded;
        self.changed = true;
    }
}

#[derive(VisitorMut)]
#[visitor(Expr(enter))]
struct TemplateSubstituter {
    substitutions: HashMap<String, Expr>,
}

impl TemplateSubstituter {
    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::Variable(Name::Raw(name)) = &expr.kind else {
            return;
        };
        let Some(param) = name.strip_prefix('$') else {
            return;
        };
        if let Some(replacement) = self.substitutions.get(param) {
            *expr = replacement.clone();
        }
    }
}

#[derive(VisitorMut)]
#[visitor(
    Attribute(enter),
    Block(enter),
    CallArg(enter),
    Decl(enter),
    Expr(enter),
    Func(enter),
    FuncSignature(enter),
    GenericDecl(enter),
    InlineIRInstruction(enter),
    MatchArm(enter),
    Parameter(enter),
    Pattern(enter),
    RecordField(enter),
    Stmt(enter),
    TypeAnnotation(enter)
)]
struct NodeIdRemapper<'a> {
    file_id: FileID,
    node_ids: &'a mut IDGenerator,
}

impl NodeIdRemapper<'_> {
    fn next(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn enter_attribute(&mut self, node: &mut Attribute) {
        node.id = self.next();
    }

    fn enter_block(&mut self, node: &mut Block) {
        node.id = self.next();
    }

    fn enter_call_arg(&mut self, node: &mut CallArg) {
        node.id = self.next();
    }

    fn enter_decl(&mut self, node: &mut Decl) {
        node.id = self.next();
    }

    fn enter_expr(&mut self, node: &mut Expr) {
        node.id = self.next();
    }

    fn enter_func(&mut self, node: &mut Func) {
        node.id = self.next();
    }

    fn enter_func_signature(&mut self, node: &mut FuncSignature) {
        node.id = self.next();
    }

    fn enter_generic_decl(&mut self, node: &mut GenericDecl) {
        node.id = self.next();
    }

    fn enter_inline_ir_instruction(&mut self, node: &mut InlineIRInstruction) {
        node.id = self.next();
    }

    fn enter_match_arm(&mut self, node: &mut MatchArm) {
        node.id = self.next();
    }

    fn enter_parameter(&mut self, node: &mut Parameter) {
        node.id = self.next();
    }

    fn enter_pattern(&mut self, node: &mut Pattern) {
        node.id = self.next();
    }

    fn enter_record_field(&mut self, node: &mut RecordField) {
        node.id = self.next();
    }

    fn enter_stmt(&mut self, node: &mut Stmt) {
        node.id = self.next();
    }

    fn enter_type_annotation(&mut self, node: &mut TypeAnnotation) {
        node.id = self.next();
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        macro_expansion::{expand_macros, expand_macros_with_sources},
        node_kinds::{decl::DeclKind, expr::ExprKind, stmt::StmtKind},
        parser_tests::tests::parse,
    };

    #[test]
    fn assert_expands_with_the_asserted_source_text() {
        let source = "#assert(left == \"right\")";
        let mut ast = parse(source);
        let invocation_id = ast.roots[0].as_stmt().clone().as_expr().id;
        let sources = HashMap::from([(ast.file_id, source.to_string())]);
        let diagnostics =
            expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected assertion function call");
        };
        assert_ne!(expr.id, invocation_id);
        assert!(matches!(
            &callee.kind,
            ExprKind::Variable(crate::name::Name::Raw(name))
                if name == "testing::assert_message"
        ));
        assert!(matches!(
            &args[1].value.kind,
            ExprKind::LiteralString(message)
                if message == "assertion failed: left == \\\"right\\\""
        ));
    }

    #[test]
    fn expands_expression_template_and_removes_definition() {
        let mut ast = parse(
            "macro choose($condition, $yes, $no) = if $condition { $yes } else { $no }\n#choose(true, 1, 2)",
        );
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(ast.roots.len(), 1);
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(expr.kind, ExprKind::If(..)));
    }

    #[test]
    fn selects_rules_by_arity() {
        let mut ast = parse("macro pick($one) = $one\nmacro pick($one, $two) = $two\n#pick(1, 2)");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(&expr.kind, ExprKind::LiteralInt(value) if value == "2"));
    }

    #[test]
    fn recursively_expands_macros_emitted_by_templates() {
        let mut ast =
            parse("macro inner($value) = $value\nmacro outer($value) = #inner($value)\n#outer(7)");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(&expr.kind, ExprKind::LiteralInt(value) if value == "7"));
    }

    #[test]
    fn rejects_type_annotations_nested_in_templates() {
        let mut ast = parse("macro invoke($value) = $value.map<Int>()\n#invoke([1])");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            crate::diagnostic::AnyDiagnostic::Parsing(crate::diagnostic::Diagnostic {
                kind: crate::parser_error::ParserError::InvalidMacroTemplate { reason, .. },
                ..
            }) if reason == "type names in templates require definition-site hygiene"
        )));
    }

    #[test]
    fn rejects_free_template_identifiers() {
        let mut ast = parse("macro bad($value) = helper($value)\n#bad(1)");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert_eq!(diagnostics.len(), 2);
        assert!(matches!(
            diagnostics[0],
            crate::diagnostic::AnyDiagnostic::Parsing(crate::diagnostic::Diagnostic {
                kind: crate::parser_error::ParserError::InvalidMacroTemplate { .. },
                ..
            })
        ));
        assert!(!ast.roots.iter().any(|node| {
            matches!(
                node,
                crate::node::Node::Decl(crate::node_kinds::decl::Decl {
                    kind: DeclKind::Macro { .. },
                    ..
                })
            )
        }));
    }

    #[test]
    fn rejects_exported_macros_until_module_artifacts_exist() {
        let mut ast = parse("public macro identity($value) = $value\n#identity(1)");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            crate::diagnostic::AnyDiagnostic::Parsing(crate::diagnostic::Diagnostic {
                kind: crate::parser_error::ParserError::InvalidMacroTemplate { reason, .. },
                ..
            }) if reason == "exported macros are not implemented"
        )));
    }

    #[test]
    fn reports_arity_mismatch() {
        let mut ast = parse("macro one($value) = $value\n#one(1, 2)");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            crate::diagnostic::AnyDiagnostic::Parsing(crate::diagnostic::Diagnostic {
                kind: crate::parser_error::ParserError::MacroArityMismatch { .. },
                ..
            })
        )));
    }

    #[test]
    fn bounds_recursive_expansion() {
        let mut ast = parse("macro recurse($value) = #recurse($value)\n#recurse(1)");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            crate::diagnostic::AnyDiagnostic::Parsing(crate::diagnostic::Diagnostic {
                kind: crate::parser_error::ParserError::MacroExpansionLimit { .. },
                ..
            })
        )));
    }

    #[test]
    fn expands_before_the_existing_frontend_pipeline() {
        use crate::compiling::driver::{Driver, DriverConfig, Source};

        let driver = Driver::new_bare(
            vec![Source::from(
                "macro choose($condition, $yes, $no) = if $condition { $yes } else { $no }\nlet answer = #choose(true, 1, 2)",
            )],
            DriverConfig::new("MacroTest"),
        );
        let typed = driver
            .parse()
            .expect("parse")
            .resolve_names()
            .expect("resolve")
            .type_check();
        assert!(
            typed.phase.diagnostics.is_empty(),
            "{:?}",
            typed.phase.diagnostics
        );
    }

    #[test]
    fn gives_each_template_node_a_fresh_id() {
        let mut ast = parse("macro one($value) = 1 + $value\n(#one(2), #one(3))");
        let diagnostics = expand_macros(std::slice::from_mut(&mut ast));
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Tuple(items) = &expr.kind else {
            panic!("expected tuple");
        };
        assert_ne!(items[0].id, items[1].id);
    }
}
