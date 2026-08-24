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
    UndefinedWrapper {
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
            Self::UndefinedWrapper { .. } => "macro.undefined-wrapper",
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
            Self::UndefinedWrapper { name, .. } => {
                write!(f, "Undefined declaration wrapper `#[{name}]`")
            }
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

use crate::front::macro_host::{
    MacroBindings, MacroHost, MacroResolution, ProceduralMacro, WrapperContext, WrapperResolution,
};
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
        body::Body,
        call_arg::{CallArg, CallArgOrigin},
        decl::{Decl, DeclKind, MacroParameter},
        expr::{Expr, ExprKind, MacroToken},
        func::Func,
        func_signature::FuncSignature,
        generic_decl::GenericDecl,
        inline_ir_instruction::InlineIRInstruction,
        match_arm::MatchArm,
        parameter::Parameter,
        pattern::{Pattern, PatternKind},
        record_field::RecordField,
        stmt::{Stmt, StmtKind},
        type_annotation::{TypeAnnotation, TypeAnnotationKind},
    },
};

const MAX_EXPANSIONS_PER_FILE: usize = 4096;

type MacroKey = (FileID, String, usize);

#[derive(Clone, Debug)]
struct MacroDefinition {
    params: Vec<MacroParameter>,
    /// Canonical template tokens, including the outer braces. The body is
    /// never parsed at definition time; each invocation position substitutes
    /// its arguments and parses the result against its own category.
    tokens: Vec<MacroToken>,
}

/// Canonical TokenKind tags the expander matches on, read from the frontend
/// schema once so Rust never hardcodes the enum's ordering.
#[derive(Debug)]
struct TokenTags {
    identifier: u32,
    effect_name: u32,
    bound_var: u32,
    comma: u32,
    openers: [u32; 3],
    closers: [u32; 3],
}

fn token_tags(host: &dyn MacroHost) -> Result<&'static TokenTags, String> {
    static TAGS: std::sync::OnceLock<Result<TokenTags, String>> = std::sync::OnceLock::new();
    TAGS.get_or_init(|| {
        let tag = |variant: &str| host.token_kind_tag(variant);
        Ok(TokenTags {
            identifier: tag("identifier")?,
            effect_name: tag("effect_name")?,
            bound_var: tag("bound_var")?,
            comma: tag("comma")?,
            openers: [tag("left_paren")?, tag("left_bracket")?, tag("left_brace")?],
            closers: [
                tag("right_paren")?,
                tag("right_bracket")?,
                tag("right_brace")?,
            ],
        })
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// The tokens a template splices in, outer braces stripped.
fn template_inner(tokens: &[MacroToken]) -> &[MacroToken] {
    if tokens.len() >= 2 {
        &tokens[1..tokens.len() - 1]
    } else {
        &[]
    }
}

/// Definition-time checks that need no parse: distinct parameters, and every
/// `$name` in the body naming a declared parameter.
fn validate_definition(
    params: &[MacroParameter],
    tokens: &[MacroToken],
    source: Option<&str>,
    tags: &TokenTags,
) -> Result<(), String> {
    let mut names = HashSet::new();
    for param in params {
        if !names.insert(param.name.as_str()) {
            return Err(format!(
                "parameter `${}` is declared more than once",
                param.name
            ));
        }
    }
    let source = source.ok_or("template source is unavailable")?;
    for token in template_inner(tokens) {
        if token.kind_tag == tags.bound_var {
            let name = &source[token.lexeme_start as usize..token.lexeme_end as usize];
            if !names.contains(name) {
                return Err(format!("unknown template parameter `${name}`"));
            }
        }
    }
    Ok(())
}

/// Split an invocation's canonical tokens (outer delimiters included) into
/// top-level comma-separated argument token groups.
fn split_macro_args(input_tokens: &[MacroToken], tags: &TokenTags) -> Vec<Vec<MacroToken>> {
    let inner = template_inner(input_tokens);
    let mut args: Vec<Vec<MacroToken>> = Vec::new();
    let mut current = Vec::new();
    let mut depth = 0i32;
    for token in inner {
        if token.kind_tag == tags.comma && depth == 0 {
            args.push(std::mem::take(&mut current));
            continue;
        }
        if tags.openers.contains(&token.kind_tag) {
            depth += 1;
        }
        if tags.closers.contains(&token.kind_tag) {
            depth -= 1;
        }
        current.push(*token);
    }
    // A trailing comma leaves an empty final group, which is not an argument.
    if !current.is_empty() || args.is_empty() && !inner.is_empty() {
        args.push(current);
    }
    args
}

/// Expand macros with the original source text available to source-reflecting
/// built-ins such as `@assert` and to declarative token templates, which
/// parse their bodies out of the defining file's source.
pub fn expand_macros_with_sources(
    asts: &mut [AST<Parsed>],
    sources: &HashMap<FileID, Arc<str>>,
    host: &dyn MacroHost,
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
                tokens,
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

            let validated = match token_tags(host) {
                Ok(tags) => validate_definition(
                    params,
                    tokens,
                    sources.get(&ast.file_id).map(AsRef::as_ref),
                    tags,
                ),
                Err(error) => Err(error),
            };
            match validated {
                Ok(()) => {
                    definitions.insert(
                        key,
                        MacroDefinition {
                            params: params.clone(),
                            tokens: tokens.clone(),
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
        let procedural_bindings = host.bindings_for(ast);
        let node_ids = std::mem::take(&mut ast.node_ids);
        let tags = match token_tags(host) {
            Ok(tags) => tags,
            Err(error) => {
                diagnostics.push(
                    Diagnostic {
                        id: NodeID(ast.file_id, 0),
                        severity: Severity::Error,
                        kind: MacroError::InvalidProceduralExpansion {
                            name: "macro".into(),
                            reason: error,
                            span: crate::parsing::span::Span {
                                file_id: ast.file_id,
                                start: 0,
                                end: 0,
                            },
                        },
                    }
                    .into(),
                );
                continue;
            }
        };
        let mut expander = MacroExpander {
            file_id: ast.file_id,
            definitions: &definitions,
            diagnostics: Vec::new(),
            node_ids,
            expansions: 0,
            changed: false,
            source: sources.get(&ast.file_id).map(AsRef::as_ref),
            tags,
            procedural: procedural_bindings.as_ref(),
            host,
            generated_sources: HashMap::new(),
            emitted_metadata: Vec::new(),
            nominal_contexts: Vec::new(),
        };
        loop {
            expander.changed = false;
            expander.expand_decl_items(&mut ast.roots, WrapperContext::TopLevel);
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

#[derive(VisitorMut)]
#[visitor(
    Expr(enter),
    Block(enter),
    Body(enter),
    Decl(enter, exit),
    Pattern(enter),
    TypeAnnotation(enter)
)]
struct MacroExpander<'a> {
    file_id: FileID,
    definitions: &'a HashMap<MacroKey, MacroDefinition>,
    diagnostics: Vec<AnyDiagnostic>,
    node_ids: IDGenerator,
    expansions: usize,
    changed: bool,
    source: Option<&'a str>,
    tags: &'a TokenTags,
    procedural: &'a dyn MacroBindings,
    host: &'a dyn MacroHost,
    generated_sources: HashMap<NodeID, String>,
    emitted_metadata: Vec<crate::hygiene::MaterializedIdentifier>,
    // The nominal bodies the visitor is currently inside, so `enter_body`
    // knows which declaration context a wrapper target occupies.
    nominal_contexts: Vec<WrapperContext>,
}

/// What applying one wrapper did to the declaration it was rooted at.
enum WrapperApplied {
    /// The declaration was rewritten in place; it stays in its container.
    Replaced,
    /// The declaration must be removed: the wrapper returned `Remove`, or
    /// the chain stopped on an error already reported.
    Remove,
}

/// The member context a nominal body assigns to its declarations.
fn nominal_context(kind: &DeclKind) -> Option<WrapperContext> {
    match kind {
        DeclKind::Struct { .. } => Some(WrapperContext::StructBody),
        DeclKind::Enum { .. } => Some(WrapperContext::EnumBody),
        DeclKind::Protocol { .. } => Some(WrapperContext::ProtocolBody),
        DeclKind::Extend { .. } => Some(WrapperContext::ExtendBody),
        _ => None,
    }
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
        binding: &dyn ProceduralMacro,
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
        let expansion = match binding.expand(
            self.file_id,
            source,
            input_span.start,
            input_span.end,
            input_tokens,
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
        expanded.drive_mut(&mut CallSiteSpanRewriter { span: expr.span });
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

    /// Apply the innermost wrapper of the chain rooted at `decl` (ADR 0026):
    /// the marker closest to the declaration runs first, and `Remove` or a
    /// failure stops the chain. One call performs one application; a chain's
    /// remaining markers and any markers quoted into the replacement expand
    /// through the ordinary fixpoint loop.
    fn apply_wrapper(&mut self, decl: &mut Decl, context: WrapperContext) -> WrapperApplied {
        let id = decl.id;
        let span = decl.span;
        let DeclKind::Wrapper {
            name,
            name_span,
            input_span,
            input_tokens,
            target_tokens,
            target,
        } = &mut decl.kind
        else {
            unreachable!("apply_wrapper requires a wrapper declaration");
        };

        if matches!(target.kind, DeclKind::Wrapper { .. }) {
            let applied = self.apply_wrapper(target, context);
            if let WrapperApplied::Replaced = applied {
                // The captured tokens still spell the inner marker; the
                // replacement's canonical text is recorded under the new
                // target id and is re-scanned instead.
                target_tokens.clear();
            }
            return applied;
        }

        let name = name.clone();
        let name_span = *name_span;
        let input_span = *input_span;
        let input_tokens = input_tokens.clone();
        let target_tokens = target_tokens.clone();
        let target_id = target.id;

        if self.expansions >= MAX_EXPANSIONS_PER_FILE {
            self.error(id, MacroError::MacroExpansionLimit { name, span });
            return WrapperApplied::Remove;
        }

        let binding = match self.procedural.resolve_wrapper(&name) {
            WrapperResolution::Found(binding) => binding,
            WrapperResolution::Ambiguous(packages) => {
                self.error(
                    id,
                    MacroError::AmbiguousProceduralMacro {
                        name,
                        packages,
                        span: name_span,
                    },
                );
                return WrapperApplied::Remove;
            }
            WrapperResolution::Missing => {
                self.error(
                    id,
                    MacroError::UndefinedWrapper {
                        name,
                        span: name_span,
                    },
                );
                return WrapperApplied::Remove;
            }
        };

        let args_source = self
            .generated_sources
            .get(&id)
            .cloned()
            .or_else(|| self.source.map(str::to_string));
        let Some(args_source) = args_source else {
            self.error(
                id,
                MacroError::InvalidProceduralExpansion {
                    name,
                    reason: "invocation source is unavailable".into(),
                    span,
                },
            );
            return WrapperApplied::Remove;
        };
        let (target_source, target_tokens) = if target_tokens.is_empty() {
            match self.generated_sources.get(&target_id).cloned() {
                Some(generated) => (generated, Vec::new()),
                None => {
                    self.error(
                        id,
                        MacroError::InvalidProceduralExpansion {
                            name,
                            reason: "wrapper target tokens are unavailable".into(),
                            span,
                        },
                    );
                    return WrapperApplied::Remove;
                }
            }
        } else {
            (args_source.clone(), target_tokens)
        };

        let namespace = (u64::from(self.file_id.0) << 32) | u64::from(id.1);
        let ordinal = self.expansions as u64 + 1;
        let expansion = match binding.expand_wrapper(
            self.file_id,
            &args_source,
            input_span.start,
            input_span.end,
            &input_tokens,
            &target_source,
            &target_tokens,
            context,
            namespace,
            ordinal,
        ) {
            Ok(expansion) => expansion,
            Err(message) => {
                self.error(
                    id,
                    MacroError::ProceduralMacroFailure {
                        name,
                        code: "macro.execution".into(),
                        message,
                        span,
                    },
                );
                return WrapperApplied::Remove;
            }
        };
        if let Some(failure) = expansion.failure {
            self.error(
                id,
                MacroError::ProceduralMacroFailure {
                    name,
                    code: failure.code,
                    message: failure.message,
                    span,
                },
            );
            return WrapperApplied::Remove;
        }
        if expansion.removed {
            self.expansions += 1;
            self.changed = true;
            return WrapperApplied::Remove;
        }
        let Some(mut parsed) = expansion.parse else {
            self.error(
                id,
                MacroError::InvalidProceduralExpansion {
                    name,
                    reason: "successful result contains no parsed declaration".into(),
                    span,
                },
            );
            return WrapperApplied::Remove;
        };
        let parse_failure = parsed
            .failure
            .take()
            .or_else(|| parsed.diags.drain(..).next());
        if let Some(failure) = parse_failure {
            self.error(
                id,
                MacroError::ProceduralMacroFailure {
                    name,
                    code: failure.code,
                    message: failure.message,
                    span,
                },
            );
            return WrapperApplied::Remove;
        }
        expansion.metadata.apply(&mut parsed.roots);
        self.emitted_metadata.extend(expansion.metadata.identifiers);
        if parsed.roots.len() != 1 {
            self.error(
                id,
                MacroError::InvalidProceduralExpansion {
                    name,
                    reason: format!("expected one declaration, got {} roots", parsed.roots.len()),
                    span,
                },
            );
            return WrapperApplied::Remove;
        }
        let Node::Decl(mut replacement) = parsed.roots.remove(0) else {
            self.error(
                id,
                MacroError::InvalidProceduralExpansion {
                    name,
                    reason: "result root is not a declaration".into(),
                    span,
                },
            );
            return WrapperApplied::Remove;
        };
        // Imports and macro definitions establish the macro namespace itself
        // and are collected before expansion, so a replacement cannot
        // introduce them (ADR 0026).
        if matches!(
            replacement.kind,
            DeclKind::Macro { .. } | DeclKind::Import(_)
        ) {
            self.error(
                id,
                MacroError::InvalidProceduralExpansion {
                    name,
                    reason: "wrappers cannot produce imports or macro definitions".into(),
                    span,
                },
            );
            return WrapperApplied::Remove;
        }
        replacement.drive_mut(&mut NodeIdRemapper {
            file_id: self.file_id,
            node_ids: &mut self.node_ids,
        });
        replacement.drive_mut(&mut CallSiteSpanRewriter { span });
        let mut nested = vec![replacement.id];
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &Expr| {
                if matches!(candidate.kind, ExprKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            replacement.drive(&mut collect);
        }
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &Pattern| {
                if matches!(candidate.kind, PatternKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            replacement.drive(&mut collect);
        }
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &TypeAnnotation| {
                if matches!(candidate.kind, TypeAnnotationKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            replacement.drive(&mut collect);
        }
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &Decl| {
                if matches!(
                    candidate.kind,
                    DeclKind::MacroCall { .. } | DeclKind::Wrapper { .. }
                ) {
                    nested.push(candidate.id);
                }
            });
            replacement.drive(&mut collect);
        }
        for nested_id in nested {
            self.generated_sources
                .insert(nested_id, expansion.source.clone());
        }
        *decl = replacement;
        self.expansions += 1;
        self.changed = true;
        WrapperApplied::Replaced
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
            MacroResolution::Found(binding) => {
                self.expand_procedural(expr, name, binding, input_span, &input_tokens);
                return;
            }
            MacroResolution::Ambiguous(packages) => {
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
            MacroResolution::Missing => {}
        }

        if name == "assert" {
            self.expand_assert(expr, name, args);
            return;
        }

        let id = expr.id;
        let span = expr.span;
        let Some(roots) = self.expand_token_template(
            id,
            span,
            &name,
            name_span,
            input_span,
            &input_tokens,
            Category::Expr,
        ) else {
            self.replace_with_unit(expr);
            return;
        };
        *expr = match roots.as_slice() {
            [Node::Expr(single)] => single.clone(),
            [
                Node::Stmt(Stmt {
                    kind: StmtKind::Expr(single),
                    ..
                }),
            ] => single.clone(),
            _ => Expr {
                id: self.next_id(),
                span,
                kind: ExprKind::Block(Block {
                    id: self.next_id(),
                    args: Vec::new(),
                    body: roots,
                    span,
                }),
            },
        };
    }

    fn expr_statement(&mut self, expr: Expr) -> Node {
        let span = expr.span;
        Node::Stmt(Stmt {
            id: self.next_id(),
            span,
            kind: StmtKind::Expr(expr),
        })
    }

    /// Expand declaration-position invocations inside one item list,
    /// splicing each expansion in where its invocation stood. Newly spliced
    /// items are left for the next fixpoint pass, so nested declaration
    /// macros expand in order. Invocations of expression-producing macros
    /// (the compiler-provided `@assert`, procedural macros) expand to an
    /// expression statement.
    fn expand_decl_items(&mut self, items: &mut Vec<Node>, context: WrapperContext) {
        let mut index = 0;
        while index < items.len() {
            if let Node::Decl(decl) = &mut items[index]
                && matches!(decl.kind, DeclKind::Wrapper { .. })
            {
                match self.apply_wrapper(decl, context) {
                    WrapperApplied::Replaced => index += 1,
                    WrapperApplied::Remove => {
                        items.remove(index);
                    }
                }
                continue;
            }
            let (id, span, name, name_span, input_span, input_tokens, args) = match &items[index] {
                Node::Decl(Decl {
                    id,
                    span,
                    kind:
                        DeclKind::MacroCall {
                            name,
                            name_span,
                            input_span,
                            input_tokens,
                            args,
                        },
                    ..
                }) => (
                    *id,
                    *span,
                    name.clone(),
                    *name_span,
                    *input_span,
                    input_tokens.clone(),
                    args.clone(),
                ),
                _ => {
                    index += 1;
                    continue;
                }
            };

            if name == "assert" {
                let mut expr = Expr {
                    id,
                    span,
                    kind: ExprKind::MacroCall {
                        name: name.clone(),
                        name_span,
                        input_span,
                        input_tokens,
                        args: args.clone(),
                    },
                };
                self.expand_assert(&mut expr, name, args);
                items.splice(index..index + 1, [self.expr_statement(expr)]);
                index += 1;
                continue;
            }

            match self.procedural.resolve(&name) {
                MacroResolution::Found(binding) => {
                    let mut expr = Expr {
                        id,
                        span,
                        kind: ExprKind::MacroCall {
                            name: name.clone(),
                            name_span,
                            input_span,
                            input_tokens: input_tokens.clone(),
                            args,
                        },
                    };
                    self.expand_procedural(&mut expr, name, binding, input_span, &input_tokens);
                    items.splice(index..index + 1, [self.expr_statement(expr)]);
                    index += 1;
                    continue;
                }
                MacroResolution::Ambiguous(packages) => {
                    self.error(
                        id,
                        MacroError::AmbiguousProceduralMacro {
                            name,
                            packages,
                            span: name_span,
                        },
                    );
                    items.remove(index);
                    index += 1;
                    continue;
                }
                MacroResolution::Missing => {}
            }

            match self.expand_token_template(
                id,
                span,
                &name,
                name_span,
                input_span,
                &input_tokens,
                Category::BlockItems,
            ) {
                Some(nodes) => {
                    let inserted = nodes.len();
                    items.splice(index..index + 1, nodes);
                    index += inserted.max(1);
                }
                None => {
                    items.remove(index);
                    index += 1;
                }
            }
        }
    }

    fn enter_block(&mut self, block: &mut Block) {
        self.expand_decl_items(&mut block.body, WrapperContext::Block);
    }

    fn enter_decl(&mut self, decl: &mut Decl) {
        if let Some(context) = nominal_context(&decl.kind) {
            self.nominal_contexts.push(context);
        }
    }

    fn exit_decl(&mut self, decl: &mut Decl) {
        if nominal_context(&decl.kind).is_some() {
            self.nominal_contexts.pop();
        }
    }

    fn enter_body(&mut self, body: &mut crate::node_kinds::body::Body) {
        let member_context = self
            .nominal_contexts
            .last()
            .copied()
            .unwrap_or(WrapperContext::StructBody);
        let mut index = 0;
        while index < body.decls.len() {
            if matches!(body.decls[index].kind, DeclKind::Wrapper { .. }) {
                match self.apply_wrapper(&mut body.decls[index], member_context) {
                    WrapperApplied::Replaced => index += 1,
                    WrapperApplied::Remove => {
                        body.decls.remove(index);
                    }
                }
                continue;
            }
            let (id, span, name, name_span, input_span, input_tokens) =
                match &body.decls[index].kind {
                    DeclKind::MacroCall {
                        name,
                        name_span,
                        input_span,
                        input_tokens,
                        ..
                    } => (
                        body.decls[index].id,
                        body.decls[index].span,
                        name.clone(),
                        *name_span,
                        *input_span,
                        input_tokens.clone(),
                    ),
                    _ => {
                        index += 1;
                        continue;
                    }
                };
            match self.expand_token_template(
                id,
                span,
                &name,
                name_span,
                input_span,
                &input_tokens,
                Category::Members,
            ) {
                Some(nodes) => {
                    let mut decls = Vec::with_capacity(nodes.len());
                    let mut nondecl = false;
                    for node in nodes {
                        match node {
                            Node::Decl(decl) => decls.push(decl),
                            _ => nondecl = true,
                        }
                    }
                    if nondecl {
                        self.error(
                            id,
                            MacroError::InvalidProceduralExpansion {
                                name,
                                reason:
                                    "expansion in a declaration body must produce only declarations"
                                        .into(),
                                span,
                            },
                        );
                        body.decls.remove(index);
                        index += 1;
                    } else {
                        let inserted = decls.len();
                        body.decls.splice(index..index + 1, decls);
                        index += inserted.max(1);
                    }
                }
                None => {
                    body.decls.remove(index);
                    index += 1;
                }
            }
        }
    }

    fn enter_pattern(&mut self, pattern: &mut Pattern) {
        let PatternKind::MacroCall {
            name,
            name_span,
            input_span,
            input_tokens,
        } = pattern.kind.clone()
        else {
            return;
        };
        let id = pattern.id;
        let span = pattern.span;
        let Some(roots) = self.expand_token_template(
            id,
            span,
            &name,
            name_span,
            input_span,
            &input_tokens,
            Category::Pattern,
        ) else {
            pattern.kind = PatternKind::Wildcard;
            return;
        };
        match roots.as_slice() {
            [Node::Pattern(single)] => *pattern = single.clone(),
            _ => {
                self.error(
                    id,
                    MacroError::InvalidProceduralExpansion {
                        name,
                        reason: format!("expected one pattern, got {} items", roots.len()),
                        span,
                    },
                );
                pattern.kind = PatternKind::Wildcard;
            }
        }
    }

    fn enter_type_annotation(&mut self, annotation: &mut TypeAnnotation) {
        let TypeAnnotationKind::MacroCall {
            name,
            name_span,
            input_span,
            input_tokens,
        } = annotation.kind.clone()
        else {
            return;
        };
        let id = annotation.id;
        let span = annotation.span;
        let Some(roots) = self.expand_token_template(
            id,
            span,
            &name,
            name_span,
            input_span,
            &input_tokens,
            Category::Type,
        ) else {
            annotation.kind = TypeAnnotationKind::Tuple(Vec::new());
            return;
        };
        match roots.as_slice() {
            [Node::TypeAnnotation(single)] => *annotation = single.clone(),
            _ => {
                self.error(
                    id,
                    MacroError::InvalidProceduralExpansion {
                        name,
                        reason: format!("expected one type, got {} items", roots.len()),
                        span,
                    },
                );
                annotation.kind = TypeAnnotationKind::Tuple(Vec::new());
            }
        }
    }

    /// Substitute a declarative macro's arguments into its token template
    /// and parse the result against the invocation position's category.
    /// Returns the expansion's roots with hygiene contexts applied and fresh
    /// node identities; diagnostics are reported internally.
    fn expand_token_template(
        &mut self,
        invocation_id: NodeID,
        invocation_span: crate::parsing::span::Span,
        name: &str,
        name_span: crate::parsing::span::Span,
        _input_span: crate::parsing::span::Span,
        input_tokens: &[MacroToken],
        category: Category,
    ) -> Option<Vec<Node>> {
        if self.expansions >= MAX_EXPANSIONS_PER_FILE {
            self.error(
                invocation_id,
                MacroError::MacroExpansionLimit {
                    name: name.into(),
                    span: invocation_span,
                },
            );
            return None;
        }

        let args = split_macro_args(input_tokens, self.tags);
        let key = (self.file_id, name.to_string(), args.len());
        let Some(definition) = self.definitions.get(&key).cloned() else {
            let mut expected: Vec<_> = self
                .definitions
                .keys()
                .filter_map(|(file, candidate, arity)| {
                    (*file == self.file_id && candidate == name).then_some(*arity)
                })
                .collect();
            expected.sort_unstable();
            expected.dedup();
            let kind = if expected.is_empty() {
                MacroError::UndefinedMacro {
                    name: name.into(),
                    span: name_span,
                }
            } else {
                MacroError::MacroArityMismatch {
                    name: name.into(),
                    actual: args.len(),
                    expected,
                    span: invocation_span,
                }
            };
            self.error(invocation_id, kind);
            return None;
        };

        let Some(invocation_source) = self
            .generated_sources
            .get(&invocation_id)
            .cloned()
            .or_else(|| self.source.map(str::to_string))
        else {
            self.error(
                invocation_id,
                MacroError::InvalidProceduralExpansion {
                    name: name.into(),
                    reason: "invocation source is unavailable".into(),
                    span: invocation_span,
                },
            );
            return None;
        };
        let materialized = self.materialize(
            invocation_id,
            &definition,
            &args,
            &invocation_source,
            matches!(category, Category::Expr),
        );

        let export = match category {
            Category::Expr | Category::BlockItems => "parse_block_items_source",
            Category::Pattern => "parse_pattern_source",
            Category::Type => "parse_type_source",
            Category::Members => "parse_members_source",
        };
        let mut parsed = match self.host.parse_category(
            export,
            &materialized.source,
            self.file_id,
        ) {
            Ok(parsed) => parsed,
            Err(error) => {
                self.error(
                    invocation_id,
                    MacroError::ProceduralMacroFailure {
                        name: name.into(),
                        code: "macro.expansion-parse".into(),
                        message: error,
                        span: invocation_span,
                    },
                );
                return None;
            }
        };
        let parse_failure = parsed
            .failure
            .take()
            .or_else(|| parsed.diags.drain(..).next());
        if let Some(failure) = parse_failure {
            self.error(
                invocation_id,
                MacroError::ProceduralMacroFailure {
                    name: name.into(),
                    code: failure.code,
                    message: failure.message,
                    span: invocation_span,
                },
            );
            return None;
        }

        materialized.metadata.apply(&mut parsed.roots);
        self.emitted_metadata
            .extend(materialized.metadata.identifiers);
        for root in &mut parsed.roots {
            root.drive_mut(&mut NodeIdRemapper {
                file_id: self.file_id,
                node_ids: &mut self.node_ids,
            });
            root.drive_mut(&mut CallSiteSpanRewriter {
                span: invocation_span,
            });
        }

        // Invocations nested in the expansion carry tokens that index the
        // materialized source; record it so their own expansion can slice
        // arguments out of it.
        let mut nested = Vec::new();
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &Expr| {
                if matches!(candidate.kind, ExprKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            for root in &parsed.roots {
                root.drive(&mut collect);
            }
        }
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &Pattern| {
                if matches!(candidate.kind, PatternKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            for root in &parsed.roots {
                root.drive(&mut collect);
            }
        }
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &TypeAnnotation| {
                if matches!(candidate.kind, TypeAnnotationKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            for root in &parsed.roots {
                root.drive(&mut collect);
            }
        }
        {
            let mut collect = derive_visitor::visitor_enter_fn(|candidate: &Decl| {
                if matches!(candidate.kind, DeclKind::MacroCall { .. }) {
                    nested.push(candidate.id);
                }
            });
            for root in &parsed.roots {
                root.drive(&mut collect);
            }
        }
        for id in nested {
            self.generated_sources
                .insert(id, materialized.source.clone());
        }

        self.expansions += 1;
        self.changed = true;
        Some(parsed.roots)
    }

    /// Build an expansion's virtual source: the template's tokens with each
    /// `$param` replaced by its argument's tokens inside synthetic grouping
    /// parentheses, so a splice stays one syntax node instead of becoming
    /// textual precedence-sensitive substitution. Trivia between template
    /// tokens (and between an argument's own tokens) is copied from the
    /// original source, keeping newlines — and therefore statement breaks —
    /// intact. Template-written identifiers are recorded with their virtual
    /// spans and the expansion's hygiene context; argument tokens keep their
    /// use-site names.
    fn materialize(
        &mut self,
        invocation_id: NodeID,
        definition: &MacroDefinition,
        args: &[Vec<MacroToken>],
        invocation_source: &str,
        group_args: bool,
    ) -> Materialized {
        let definition_source = self.source.unwrap_or_default();
        let context =
            SyntaxContext::lexical(NodeID(self.file_id, 0)).with_scope(SyntaxScope::Expansion {
                namespace: (u64::from(self.file_id.0) << 32) | u64::from(invocation_id.1),
                ordinal: self.expansions as u64 + 1,
            });
        let file_id = self.file_id;
        let mut out = String::new();
        let mut identifiers = Vec::new();
        let mut prev_end: Option<u32> = None;
        for token in template_inner(&definition.tokens) {
            if let Some(prev) = prev_end {
                if prev <= token.span_start {
                    out.push_str(&definition_source[prev as usize..token.span_start as usize]);
                } else {
                    out.push(' ');
                }
            }
            if token.kind_tag == self.tags.bound_var {
                let param =
                    &definition_source[token.lexeme_start as usize..token.lexeme_end as usize];
                if let Some(index) = definition.params.iter().position(|p| p.name == param) {
                    // Synthetic grouping keeps a multi-token argument one
                    // syntax node rather than textual precedence-sensitive
                    // substitution. Grouping is only valid where a
                    // parenthesized expression is; declaration, pattern, and
                    // type splices stay ungrouped, as do single-token
                    // arguments, which have no internal structure to protect.
                    let group = group_args && args[index].len() > 1;
                    if group {
                        out.push('(');
                    }
                    let mut arg_prev: Option<u32> = None;
                    for arg_token in &args[index] {
                        if let Some(prev) = arg_prev {
                            if prev <= arg_token.span_start {
                                out.push_str(
                                    &invocation_source
                                        [prev as usize..arg_token.span_start as usize],
                                );
                            } else {
                                out.push(' ');
                            }
                        }
                        out.push_str(
                            &invocation_source
                                [arg_token.span_start as usize..arg_token.span_end as usize],
                        );
                        arg_prev = Some(arg_token.span_end);
                    }
                    if group {
                        out.push(')');
                    }
                    prev_end = Some(token.span_end);
                    continue;
                }
            }
            let start = out.len() as u32;
            out.push_str(&definition_source[token.span_start as usize..token.span_end as usize]);
            if token.kind_tag == self.tags.identifier || token.kind_tag == self.tags.effect_name {
                let lexeme_offset = token.lexeme_start - token.span_start;
                identifiers.push(crate::hygiene::MaterializedIdentifier {
                    text: definition_source[token.lexeme_start as usize..token.lexeme_end as usize]
                        .to_string(),
                    span: crate::parsing::span::Span {
                        file_id,
                        start,
                        end: out.len() as u32,
                    },
                    lexeme: crate::parsing::span::Span {
                        file_id,
                        start: start + lexeme_offset,
                        end: start + lexeme_offset + (token.lexeme_end - token.lexeme_start),
                    },
                    context: context.clone(),
                    origin: crate::hygiene::SyntaxOrigin::DefinitionSite,
                    source_span: crate::parsing::span::Span {
                        file_id,
                        start: token.span_start,
                        end: token.span_end,
                    },
                    source_lexeme: crate::parsing::span::Span {
                        file_id,
                        start: token.lexeme_start,
                        end: token.lexeme_end,
                    },
                });
            }
            prev_end = Some(token.span_end);
        }
        Materialized {
            source: out,
            metadata: crate::hygiene::SyntaxMetadata::new(identifiers),
        }
    }
}

/// The grammar category an expansion is parsed against: the invocation
/// position's own category.
#[derive(Clone, Copy)]
enum Category {
    /// Expression position: parses as block items, then unwraps a single
    /// expression or wraps the rest in a block. Arguments are grouped.
    Expr,
    /// Declaration position: expansion items splice into the item list.
    BlockItems,
    /// Nominal-body position (struct/extension bodies): member grammar, so
    /// generated functions become methods.
    Members,
    Pattern,
    Type,
}

/// An expansion's virtual source plus the hygiene metadata for its
/// template-written identifiers.
struct Materialized {
    source: String,
    metadata: crate::hygiene::SyntaxMetadata,
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

/// Rewrites the spans of an expansion's freshly parsed nodes. Expansions
/// parse a virtual source string, so their nodes point into that string
/// while carrying the invocation's file id; rendered against the real
/// source, those offsets are nonsense. Diagnostics resolve a node's range
/// from its span, so expanded nodes borrow the invocation's span: an error
/// inside an expansion points at the macro call that produced it. Only
/// node spans are rewritten — MacroCall `input_span`/`input_tokens` keep
/// their virtual coordinates because nested invocations still slice their
/// arguments out of the virtual source with them.
#[derive(VisitorMut)]
#[visitor(
    Attribute(enter),
    Block(enter),
    Body(enter),
    CallArg(enter),
    Decl(enter),
    Expr(enter),
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
struct CallSiteSpanRewriter {
    span: crate::parsing::span::Span,
}

impl CallSiteSpanRewriter {
    fn enter_attribute(&mut self, node: &mut Attribute) {
        node.span = self.span;
    }

    fn enter_block(&mut self, node: &mut Block) {
        node.span = self.span;
    }

    fn enter_body(&mut self, node: &mut Body) {
        node.span = self.span;
    }

    fn enter_call_arg(&mut self, node: &mut CallArg) {
        node.span = self.span;
    }

    fn enter_decl(&mut self, node: &mut Decl) {
        node.span = self.span;
    }

    fn enter_expr(&mut self, node: &mut Expr) {
        node.span = self.span;
    }

    fn enter_func_signature(&mut self, node: &mut FuncSignature) {
        node.span = self.span;
    }

    fn enter_generic_decl(&mut self, node: &mut GenericDecl) {
        node.span = self.span;
    }

    fn enter_inline_ir_instruction(&mut self, node: &mut InlineIRInstruction) {
        node.span = self.span;
    }

    fn enter_match_arm(&mut self, node: &mut MatchArm) {
        node.span = self.span;
    }

    fn enter_parameter(&mut self, node: &mut Parameter) {
        node.span = self.span;
    }

    fn enter_pattern(&mut self, node: &mut Pattern) {
        node.span = self.span;
    }

    fn enter_record_field(&mut self, node: &mut RecordField) {
        node.span = self.span;
    }

    fn enter_stmt(&mut self, node: &mut Stmt) {
        node.span = self.span;
    }

    fn enter_type_annotation(&mut self, node: &mut TypeAnnotation) {
        node.span = self.span;
    }
}

