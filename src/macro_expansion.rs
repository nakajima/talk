use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Macro-expansion failures (ADR 0026). These were historically
/// `ParserError` variants; the expander is a post-parse pass, so the
/// parser's diagnostic schema does not own them (ADR 0043).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MacroError {
    DuplicateMacroRule {
        name: String,
        arity: usize,
        span: crate::parsing::span::Span,
    },
    UndefinedMacro {
        name: String,
        span: crate::parsing::span::Span,
    },
    AmbiguousProceduralMacro {
        name: String,
        packages: Vec<String>,
        span: crate::parsing::span::Span,
    },
    MacroArityMismatch {
        name: String,
        actual: usize,
        expected: Vec<usize>,
        span: crate::parsing::span::Span,
    },
    InvalidMacroTemplate {
        name: String,
        reason: String,
        span: crate::parsing::span::Span,
    },
    MacroExpansionLimit {
        name: String,
        span: crate::parsing::span::Span,
    },
    ProceduralMacroFailure {
        name: String,
        code: String,
        message: String,
        span: crate::parsing::span::Span,
    },
    InvalidProceduralExpansion {
        name: String,
        reason: String,
        span: crate::parsing::span::Span,
    },
}

impl MacroError {
    pub fn code(&self) -> &'static str {
        match self {
            Self::DuplicateMacroRule { .. } => "macro.duplicate-rule",
            Self::UndefinedMacro { .. } => "macro.undefined",
            Self::AmbiguousProceduralMacro { .. } => "macro.ambiguous-procedural",
            Self::MacroArityMismatch { .. } => "macro.arity-mismatch",
            Self::InvalidMacroTemplate { .. } => "macro.invalid-template",
            Self::MacroExpansionLimit { .. } => "macro.expansion-limit",
            Self::ProceduralMacroFailure { .. } => "macro.procedural-failure",
            Self::InvalidProceduralExpansion { .. } => "macro.invalid-procedural-expansion",
        }
    }
}

impl std::fmt::Display for MacroError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateMacroRule { name, arity, .. } => {
                write!(f, "Duplicate macro rule `@{name}` with {arity} argument(s)")
            }
            Self::UndefinedMacro { name, .. } => write!(f, "Undefined macro `@{name}`"),
            Self::AmbiguousProceduralMacro { name, packages, .. } => write!(
                f,
                "Macro `@{name}` is ambiguous between {}",
                packages.join(", ")
            ),
            Self::MacroArityMismatch {
                name,
                actual,
                expected,
                ..
            } => write!(
                f,
                "Macro `@{name}` received {actual} argument(s); available arities: {}",
                expected
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::InvalidMacroTemplate { name, reason, .. } => {
                write!(f, "Invalid template for macro `{name}`: {reason}")
            }
            Self::MacroExpansionLimit { name, .. } => write!(
                f,
                "Macro expansion exceeded its work limit while expanding `@{name}`"
            ),
            Self::ProceduralMacroFailure {
                name,
                code,
                message,
                ..
            } => write!(f, "Macro `@{name}` failed ({code}): {message}"),
            Self::InvalidProceduralExpansion { name, reason, .. } => {
                write!(f, "Macro `@{name}` returned an invalid expansion: {reason}")
            }
        }
    }
}

impl std::error::Error for MacroError {}

use derive_visitor::{Drive, DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    diagnostic::{AnyDiagnostic, Diagnostic, Severity},
    hygiene::{SyntaxContext, SyntaxScope},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        attribute::Attribute,
        block::Block,
        call_arg::{CallArg, CallArgOrigin},
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
};

const MAX_EXPANSIONS_PER_FILE: usize = 4096;

type MacroKey = (FileID, String, usize);

#[derive(Clone, Debug)]
struct MacroDefinition {
    params: Vec<MacroParameter>,
    template: Expr,
}

/// Expand macros with the original source text available to source-reflecting
/// built-ins such as `@assert` and to declarative token templates, which
/// parse their bodies out of the defining file's source.
pub fn expand_macros_with_sources(
    asts: &mut [AST<Parsed>],
    sources: &HashMap<FileID, Arc<str>>,
) -> Vec<AnyDiagnostic> {
    expand_macros_with_sources_and_service(asts, sources, None)
}

pub fn expand_macros_with_sources_and_service(
    asts: &mut [AST<Parsed>],
    sources: &HashMap<FileID, Arc<str>>,
    procedural: Option<&crate::procedural_macros::ProceduralMacroEnvironment>,
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
                body_span,
                ..
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
                        kind: MacroError::InvalidMacroTemplate {
                            name: name.clone(),
                            reason: "`assert` is a compiler-provided macro".into(),
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
                        kind: MacroError::DuplicateMacroRule {
                            name: name.clone(),
                            arity: params.len(),
                            span: *name_span,
                        },
                    }
                    .into(),
                );
                continue;
            }

            match parse_template(ast.file_id, params, *body_span, sources) {
                Ok(template) => {
                    definitions.insert(
                        key,
                        MacroDefinition {
                            params: params.clone(),
                            template,
                        },
                    );
                }
                Err(reason) => diagnostics.push(
                    Diagnostic {
                        id: decl.id,
                        severity: Severity::Error,
                        kind: MacroError::InvalidMacroTemplate {
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
        let procedural_bindings = procedural
            .map(|environment| environment.bindings_for(ast))
            .unwrap_or_default();
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut expander = MacroExpander {
            file_id: ast.file_id,
            definitions: &definitions,
            diagnostics: Vec::new(),
            node_ids,
            expansions: 0,
            changed: false,
            source: sources.get(&ast.file_id).map(AsRef::as_ref),
            procedural: &procedural_bindings,
            generated_sources: HashMap::new(),
            emitted_metadata: Vec::new(),
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
        ast.syntax.identifiers.extend(expander.emitted_metadata);
        diagnostics.extend(expander.diagnostics);
    }

    diagnostics
}

/// Parse a declarative macro's token template into syntax. The body is
/// parsed in place: blanking the source prefix keeps every byte offset
/// identical to the real file, so the template carries true definition-site
/// spans. The result is still category-agnostic at this point — a single
/// expression stays an expression, anything else becomes a block — and the
/// invocation position's own grammar is the final judge of the expansion.
fn parse_template(
    file_id: FileID,
    params: &[MacroParameter],
    body_span: crate::parsing::span::Span,
    sources: &HashMap<FileID, Arc<str>>,
) -> Result<Expr, String> {
    let mut names = HashSet::new();
    for param in params {
        if !names.insert(param.name.as_str()) {
            return Err(format!(
                "parameter `${}` is declared more than once",
                param.name
            ));
        }
    }

    let Some(source) = sources.get(&file_id) else {
        return Err("template source is unavailable".into());
    };
    let bytes = source.as_bytes();
    let (start, end) = (body_span.start as usize, body_span.end as usize);
    if start > end || end > bytes.len() {
        return Err("template body span is out of range".into());
    }
    let mut virtual_source = Vec::with_capacity(end);
    for &byte in &bytes[..start] {
        virtual_source.push(if byte == b'\n' { b'\n' } else { b' ' });
    }
    virtual_source.extend_from_slice(&bytes[start..end]);
    let virtual_source = String::from_utf8(virtual_source)
        .map_err(|_| "template body is not valid UTF-8".to_string())?;

    let parsed = crate::compiling::frontend::parse_source(&virtual_source, file_id)
        .map_err(|error| format!("template body failed to parse: {error}"))?;
    let failure = parsed.failure.or_else(|| parsed.diags.into_iter().next());
    if let Some(failure) = failure {
        return Err(format!("template body failed to parse: {}", failure.message));
    }

    let template = match parsed.roots.as_slice() {
        [Node::Expr(expr)] => expr.clone(),
        [Node::Stmt(Stmt {
            kind: StmtKind::Expr(expr),
            ..
        })] => expr.clone(),
        roots => Expr {
            id: NodeID(file_id, 0),
            span: body_span,
            kind: ExprKind::Block(crate::node_kinds::block::Block {
                id: NodeID(file_id, 0),
                args: Vec::new(),
                body: roots.to_vec(),
                span: body_span,
            }),
        },
    };

    // Splice sites are the only `$names` a template may reference; check
    // them now so a malformed rule fails at its definition.
    let mut unknown = None;
    template.drive(&mut derive_visitor::visitor_enter_fn(|expr: &Expr| {
        if unknown.is_some() {
            return;
        }
        if let ExprKind::Variable(Name::Raw(name)) = &expr.kind
            && let Some(param) = name.strip_prefix('$')
            && !names.contains(param)
        {
            unknown = Some(format!("unknown template parameter `${param}`"));
        }
    }));
    if let Some(error) = unknown {
        return Err(error);
    }

    Ok(template)
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
    procedural: &'a crate::procedural_macros::ProceduralMacroBindings,
    generated_sources: HashMap<NodeID, String>,
    emitted_metadata: Vec<crate::hygiene::MaterializedIdentifier>,
}

impl MacroExpander<'_> {
    fn error(&mut self, id: NodeID, kind: MacroError) {
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
                MacroError::MacroArityMismatch {
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
                    origin: CallArgOrigin::Synthesized,
                    id: condition_id,
                    label: Label::Positional(0),
                    label_span: condition.span,
                    value: condition,
                    span: expr.span,
                    mode: None,
                    mode_span: None,
                },
                CallArg {
                    origin: CallArgOrigin::Synthesized,
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

    fn expand_procedural(
        &mut self,
        expr: &mut Expr,
        visible_name: String,
        binding: &crate::procedural_macros::ProceduralMacroBinding,
        input_span: crate::parsing::span::Span,
        input_tokens: &[crate::node_kinds::expr::MacroToken],
    ) {
        let source = self
            .generated_sources
            .get(&expr.id)
            .map(String::as_str)
            .or(self.source);
        let Some(source) = source else {
            self.error(
                expr.id,
                MacroError::InvalidProceduralExpansion {
                    name: visible_name,
                    reason: "invocation source is unavailable".into(),
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        };
        let namespace = (u64::from(self.file_id.0) << 32) | u64::from(expr.id.1);
        let ordinal = self.expansions as u64 + 1;
        let expansion = match binding.service.expand(
            &binding.exported_name,
            self.file_id,
            source,
            input_span.start,
            input_span.end,
            input_tokens,
            binding.definition_module,
            namespace,
            ordinal,
        ) {
            Ok(expansion) => expansion,
            Err(message) => {
                self.error(
                    expr.id,
                    MacroError::ProceduralMacroFailure {
                        name: visible_name,
                        code: "macro.execution".into(),
                        message,
                        span: expr.span,
                    },
                );
                self.replace_with_unit(expr);
                return;
            }
        };
        if let Some(failure) = expansion.failure {
            self.error(
                expr.id,
                MacroError::ProceduralMacroFailure {
                    name: visible_name,
                    code: failure.code,
                    message: failure.message,
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        }
        let Some(mut parsed) = expansion.parse else {
            self.error(
                expr.id,
                MacroError::InvalidProceduralExpansion {
                    name: visible_name,
                    reason: "successful result contains no parsed expression".into(),
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        };
        let parse_failure = parsed
            .failure
            .take()
            .or_else(|| parsed.diags.drain(..).next());
        if let Some(failure) = parse_failure {
            self.error(
                expr.id,
                MacroError::ProceduralMacroFailure {
                    name: visible_name,
                    code: failure.code,
                    message: failure.message,
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        }
        expansion.metadata.apply(&mut parsed.roots);
        self.emitted_metadata.extend(expansion.metadata.identifiers);
        if parsed.roots.len() != 1 {
            self.error(
                expr.id,
                MacroError::InvalidProceduralExpansion {
                    name: visible_name,
                    reason: format!("expected one expression, got {} roots", parsed.roots.len()),
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        }
        let root = parsed.roots.remove(0);
        let mut expanded = match root {
            Node::Expr(expanded) => expanded,
            Node::Stmt(Stmt {
                kind: StmtKind::Expr(expanded),
                ..
            }) => expanded,
            _ => {
                self.error(
                    expr.id,
                    MacroError::InvalidProceduralExpansion {
                        name: visible_name,
                        reason: "result root is not an expression".into(),
                        span: expr.span,
                    },
                );
                self.replace_with_unit(expr);
                return;
            }
        };
        expanded.drive_mut(&mut NodeIdRemapper {
            file_id: self.file_id,
            node_ids: &mut self.node_ids,
        });
        let mut nested = Vec::new();
        let mut collector = derive_visitor::visitor_enter_fn(|candidate: &Expr| {
            if matches!(candidate.kind, ExprKind::MacroCall { .. }) {
                nested.push(candidate.id);
            }
        });
        expanded.drive(&mut collector);
        drop(collector);
        for id in nested {
            self.generated_sources.insert(id, expansion.source.clone());
        }
        *expr = expanded;
        self.expansions += 1;
        self.changed = true;
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::MacroCall {
            name,
            name_span,
            input_span,
            input_tokens,
            args,
        } = expr.kind.clone()
        else {
            return;
        };

        if self.expansions >= MAX_EXPANSIONS_PER_FILE {
            self.error(
                expr.id,
                MacroError::MacroExpansionLimit {
                    name,
                    span: expr.span,
                },
            );
            self.replace_with_unit(expr);
            return;
        }

        match self.procedural.resolve(&name) {
            crate::procedural_macros::ProceduralMacroResolution::Found(binding) => {
                self.expand_procedural(expr, name, binding, input_span, &input_tokens);
                return;
            }
            crate::procedural_macros::ProceduralMacroResolution::Ambiguous(packages) => {
                self.error(
                    expr.id,
                    MacroError::AmbiguousProceduralMacro {
                        name,
                        packages,
                        span: name_span,
                    },
                );
                self.replace_with_unit(expr);
                return;
            }
            crate::procedural_macros::ProceduralMacroResolution::Missing => {}
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
                MacroError::UndefinedMacro {
                    name,
                    span: name_span,
                }
            } else {
                MacroError::MacroArityMismatch {
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
        // Template-written names receive the definition-site lexical scope
        // plus one fresh expansion scope shared by this expansion's
        // introduced bindings and their references. Spliced arguments keep
        // their use-site names, so they resolve exactly as written.
        let namespace = (u64::from(self.file_id.0) << 32) | u64::from(expr.id.1);
        let context =
            SyntaxContext::lexical(NodeID(self.file_id, 0)).with_scope(SyntaxScope::Expansion {
                namespace,
                ordinal: self.expansions as u64,
            });
        expanded.drive_mut(&mut crate::hygiene::TemplateContextStamp {
            context: &context,
        });
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
        expanded.drive_mut(&mut TemplateSubstituter {
            substitutions,
            spliced: HashSet::new(),
            file_id: self.file_id,
            node_ids: &mut self.node_ids,
        });
        *expr = expanded;
        self.changed = true;
    }
}

#[derive(VisitorMut)]
#[visitor(Expr(enter))]
struct TemplateSubstituter<'a> {
    substitutions: HashMap<String, Expr>,
    spliced: HashSet<String>,
    file_id: FileID,
    node_ids: &'a mut IDGenerator,
}

impl TemplateSubstituter<'_> {
    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::Variable(Name::Raw(name)) = &expr.kind else {
            return;
        };
        let Some(param) = name.strip_prefix('$') else {
            return;
        };
        let Some(replacement) = self.substitutions.get(param) else {
            return;
        };
        let mut replacement = replacement.clone();
        if !self.spliced.insert(param.to_string()) {
            // A repeated splice re-evaluates the argument. The first splice
            // keeps the source node's identity; later splices are re-stamped
            // with fresh ids so the expansion never contains duplicate NodeIDs.
            replacement.drive_mut(&mut NodeIdRemapper {
                file_id: self.file_id,
                node_ids: self.node_ids,
            });
        }
        *expr = replacement;
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
        macro_expansion::{MacroError, expand_macros_with_sources},
        node::Node,
        node_kinds::{
            expr::ExprKind,
            stmt::{Stmt, StmtKind},
        },
        parser_tests::tests::parse,
    };

    #[test]
    fn parser_captures_non_talk_macro_token_trees() {
        let ast = parse("@html { div class=@card { <not talk> } }");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::MacroCall {
            name,
            input_span,
            args,
            ..
        } = &expr.kind
        else {
            panic!("expected macro call");
        };
        assert_eq!(name, "html");
        assert_eq!(
            &"@html { div class=@card { <not talk> } }"
                [input_span.start as usize..input_span.end as usize],
            "{ div class=@card { <not talk> } }"
        );
        assert!(args.is_empty());
    }

    #[test]
    fn parser_captures_expression_quote_tokens_and_splices() {
        let ast = parse("quote { helper(value: $item) }");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::SyntaxQuote {
            tokens, splices, ..
        } = &expr.kind
        else {
            panic!("expected syntax quote");
        };
        assert_eq!(splices, &["item"]);
        assert_eq!(tokens.first().map(|token| token.span_start), Some(6));
        assert_eq!(tokens.last().map(|token| token.span_end), Some(30));
    }

    #[test]
    fn assert_expands_with_the_asserted_source_text() {
        let source = "@assert(left == \"right\")";
        let mut ast = parse(source);
        let invocation_id = ast.roots[0].as_stmt().clone().as_expr().id;
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
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
        let source =
            "macro choose($condition, $yes, $no) { if $condition { $yes } else { $no } }\n@choose(true, 1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(ast.roots.len(), 1);
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        // A file-level `if` parses as a statement, so the expansion wraps
        // it in a block; either shape is a faithful expansion here.
        match &expr.kind {
            ExprKind::If(..) => {}
            ExprKind::Block(block) => assert!(matches!(
                block.body.first(),
                Some(Node::Stmt(Stmt {
                    kind: StmtKind::If(..),
                    ..
                }))
            )),
            other => panic!("expected an if expansion, got {other:?}"),
        }
    }

    #[test]
    fn selects_rules_by_arity() {
        let source = "macro pick($one) { $one }\nmacro pick($one, $two) { $two }\n@pick(1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(&expr.kind, ExprKind::LiteralInt(value) if value == "2"));
    }

    #[test]
    fn recursively_expands_macros_emitted_by_templates() {
        let source =
            "macro inner($value) { $value }\nmacro outer($value) { @inner($value) }\n@outer(7)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        assert!(matches!(&expr.kind, ExprKind::LiteralInt(value) if value == "7"));
    }

    #[test]
    fn template_bodies_may_contain_binders_and_free_identifiers() {
        // The unified template model: bodies are unparsed token templates, so
        // binders, type names, and definition-site references are all allowed.
        let source = "macro once($value) { let y = $value\ny + y }\n@once(21)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Block(block) = &expr.kind else {
            panic!("expected the template to expand to a block, got {:?}", expr.kind);
        };
        assert_eq!(block.body.len(), 2);
    }

    #[test]
    fn template_names_receive_an_expansion_context() {
        let source = "macro call_it($value) { helper($value) }\n@call_it(1)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let StmtKind::Expr(expr) = &ast.roots[0].as_stmt().kind else {
            panic!("expected expression statement");
        };
        let ExprKind::Call { callee, args, .. } = &expr.kind else {
            panic!("expected a call");
        };
        // The template-written callee carries a hygienic context...
        assert!(matches!(
            &callee.kind,
            ExprKind::Variable(crate::name::Name::Syntax(name, context))
                if name == "helper" && context.has_expansion_scope()
        ));
        // ...while the spliced argument keeps its use-site name.
        assert!(matches!(
            &args[0].value.kind,
            ExprKind::LiteralInt(value) if value == "1"
        ));
    }

    #[test]
    fn reports_arity_mismatch() {
        let source = "macro one($value) { $value }\n@one(1, 2)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            crate::diagnostic::AnyDiagnostic::Macro(crate::diagnostic::Diagnostic {
                kind: MacroError::MacroArityMismatch { .. },
                ..
            })
        )));
    }

    #[test]
    fn bounds_recursive_expansion() {
        let source = "macro recurse($value) { @recurse($value) }\n@recurse(1)";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
        assert!(diagnostics.iter().any(|diagnostic| matches!(
            diagnostic,
            crate::diagnostic::AnyDiagnostic::Macro(crate::diagnostic::Diagnostic {
                kind: MacroError::MacroExpansionLimit { .. },
                ..
            })
        )));
    }

    #[test]
    fn expands_before_the_existing_frontend_pipeline() {
        use crate::compiling::driver::{Driver, DriverConfig, Source};

        let driver = Driver::new_bare(
            vec![Source::from(
                "macro choose($condition, $yes, $no) { if $condition { $yes } else { $no } }\nlet answer = @choose(true, 1, 2)",
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
        let source = "macro one($value) { 1 + $value }\n(@one(2), @one(3))";
        let mut ast = parse(source);
        let sources = HashMap::from([(ast.file_id, std::sync::Arc::from(source))]);
        let diagnostics = expand_macros_with_sources(std::slice::from_mut(&mut ast), &sources);
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
