use async_lsp::lsp_types::{
    CodeAction, CodeActionKind, CodeActionOrCommand, CodeActionResponse, Diagnostic,
    DiagnosticSeverity, NumberOrString, Range, TextEdit, Url, WorkspaceEdit,
};
use derive_visitor::Drive;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::{
    Diagnostic as AnalysisDiagnostic, DiagnosticKind as AnalysisDiagnosticKind,
    DiagnosticSeverity as AnalysisSeverity, DocumentId, Workspace as AnalysisWorkspace,
    completion as analysis_completion,
};
use crate::lsp::rename::rename_at;
use crate::name_resolution::name_resolver::NameResolverError;
use crate::parser_error::ParserError;
use crate::types::TypeError;

use super::server::byte_span_to_range_utf16;

fn ranges_overlap(left: Range, right: Range) -> bool {
    let left_end_before_right_start =
        (left.end.line, left.end.character) < (right.start.line, right.start.character);
    let right_end_before_left_start =
        (right.end.line, right.end.character) < (left.start.line, left.start.character);
    !left_end_before_right_start && !right_end_before_left_start
}

struct DiagnosticActionSite<'a> {
    workspace: &'a AnalysisWorkspace,
    document_id: &'a DocumentId,
    text: &'a str,
    uri: &'a Url,
    file_id: crate::node_id::FileID,
    diagnostic: &'a AnalysisDiagnostic,
    diag_range: Range,
}

/// Compute code actions for a document, including auto-import suggestions
fn is_import(node: &crate::node::Node) -> bool {
    matches!(
        node,
        crate::node::Node::Decl(crate::node_kinds::decl::Decl {
            kind: crate::node_kinds::decl::DeclKind::Import(_),
            ..
        })
    )
}

fn auto_import_edit(
    text: &str,
    roots: &[crate::node::Node],
    import_statement: &str,
) -> Option<TextEdit> {
    let import_count = roots.iter().take_while(|root| is_import(root)).count();
    let next_root_exists = import_count < roots.len();

    let (insert_offset, mut new_text) = if let Some(last_import) = import_count
        .checked_sub(1)
        .and_then(|index| roots.get(index))
    {
        let import_end = last_import.span().end as usize;
        let line_end = text[import_end..]
            .find('\n')
            .map(|offset| import_end + offset + 1)
            .unwrap_or(text.len());
        let suffix = text.get(line_end..)?;
        let mut new_text = import_statement.to_string();
        if next_root_exists {
            new_text.push('\n');
            if !suffix.starts_with('\n') {
                new_text.push('\n');
            }
        } else if text.ends_with('\n') {
            new_text.push('\n');
        }
        (line_end, new_text)
    } else {
        let no_core_end = if text.starts_with("// no-core") {
            text.find('\n')
                .map(|offset| offset + 1)
                .unwrap_or(text.len())
        } else {
            0
        };
        let suffix = text.get(no_core_end..)?;
        let mut new_text = String::new();
        if no_core_end > 0 && !text[..no_core_end].ends_with('\n') {
            new_text.push('\n');
        }
        new_text.push_str(import_statement);
        if !suffix.is_empty() {
            new_text.push('\n');
            if !suffix.starts_with('\n') {
                new_text.push('\n');
            }
        }
        (no_core_end, new_text)
    };

    let range = byte_span_to_range_utf16(text, insert_offset as u32, insert_offset as u32)?;
    Some(TextEdit::new(range, std::mem::take(&mut new_text)))
}

pub(super) fn compute_code_actions(
    workspace: &AnalysisWorkspace,
    document_id: &DocumentId,
    uri: &Url,
    range: Range,
) -> CodeActionResponse {
    let mut actions: Vec<CodeActionOrCommand> = Vec::new();

    // Get diagnostics for this document
    let Some(diagnostics) = workspace.diagnostics.get(document_id) else {
        return actions;
    };

    // Get the file ID for this document
    let Some(&file_id) = workspace.document_to_file_id.get(document_id) else {
        return actions;
    };

    // Get the text for this document
    let Some(text) = workspace.texts.get(file_id.0 as usize) else {
        return actions;
    };

    // Build an index of public symbols from all other files
    // Map from symbol name -> (source file path, symbol)
    let mut public_exports: FxHashMap<
        String,
        Vec<(String, crate::name_resolution::symbol::Symbol)>,
    > = FxHashMap::default();

    for (idx, doc_id) in workspace.file_id_to_document.iter().enumerate() {
        if doc_id == document_id {
            continue; // Skip current file
        }
        let Some(source_path) = workspace
            .asts
            .get(idx)
            .and_then(|ast| ast.as_ref())
            .map(|ast| ast.path.clone())
        else {
            continue;
        };

        let target_file_id = crate::node_id::FileID(idx as u32);
        let scope_id = crate::node_id::NodeID(target_file_id, 0);

        if let Some(scope) = workspace.resolved_names.scopes.get(&scope_id) {
            for (name, &symbol) in &scope.values {
                if workspace.resolved_names.public_symbols.contains(&symbol) {
                    public_exports
                        .entry(name.clone())
                        .or_default()
                        .push((source_path.clone(), symbol));
                }
            }
            for (name, &symbol) in &scope.types {
                if workspace.resolved_names.public_symbols.contains(&symbol) {
                    public_exports
                        .entry(name.clone())
                        .or_default()
                        .push((source_path.clone(), symbol));
                }
            }
        }
    }

    for diagnostic in diagnostics {
        let Some(diag_range) =
            byte_span_to_range_utf16(text, diagnostic.range.start, diagnostic.range.end)
        else {
            continue;
        };
        if !ranges_overlap(diag_range, range) {
            continue;
        }
        let Some(kind) = diagnostic.kind.as_ref() else {
            continue;
        };
        let site = DiagnosticActionSite {
            workspace,
            document_id,
            text,
            uri,
            file_id,
            diagnostic,
            diag_range,
        };

        match kind {
            AnalysisDiagnosticKind::Parsing(error) => actions.extend(parser_quick_fixes(
                workspace, text, uri, file_id, error, diagnostic, diag_range,
            )),
            AnalysisDiagnosticKind::Types(TypeError::ArityMismatch { expected, found }) => {
                actions.extend(arity_mismatch_quick_fixes(&site, *expected, *found));
            }
            AnalysisDiagnosticKind::Types(TypeError::MissingWitness {
                protocol,
                requirement,
            }) => actions.extend(missing_witness_quick_fixes(
                &site,
                diagnostic.range.start,
                requirement,
                protocol,
            )),
            AnalysisDiagnosticKind::Types(TypeError::NonExhaustiveMatch { missing }) => {
                actions.extend(non_exhaustive_match_quick_fixes(
                    &site,
                    diagnostic.range.start,
                    missing,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::AmbiguousMember {
                label, candidates, ..
            }) => actions.extend(ambiguous_member_quick_fixes(
                &site,
                diagnostic.range.start as usize,
                diagnostic.range.end as usize,
                label,
                candidates,
            )),
            AnalysisDiagnosticKind::Types(TypeError::UnknownMember { label, .. }) => {
                actions.extend(unknown_member_quick_fixes(&site, label));
            }
            AnalysisDiagnosticKind::Types(TypeError::UnresolvedVariant { label }) => {
                actions.extend(unresolved_variant_quick_fixes(
                    workspace, text, uri, file_id, label, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::DuplicatePredicate { .. }) => {
                actions.extend(duplicate_predicate_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::RedundantVariantResultType { .. }) => {
                actions.extend(redundant_variant_result_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::InvalidVariantResultType { .. }) => {
                actions.extend(invalid_variant_result_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::InvalidVariantPayloadLabels { variant }) => {
                actions.extend(invalid_variant_payload_labels_quick_fixes(
                    workspace, text, uri, file_id, variant, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::IncompatibleOrPatternRefinements) => {
                actions.extend(incompatible_or_pattern_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::UnreachableMatchArm) => {
                actions.extend(unreachable_match_arm_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::UnreachableCode) => {
                actions.extend(unreachable_code_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::DuplicateAssociatedTypeBinding { .. }) => {
                actions.extend(duplicate_associated_binding_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::UnknownAssociatedTypeBinding { .. }) => {
                actions.extend(unknown_associated_binding_quick_fixes(
                    workspace, text, uri, file_id, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::GenericShadowing { name }) => {
                actions.extend(generic_shadowing_quick_fixes(
                    workspace, uri, file_id, name, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::Types(TypeError::UndeclaredEffect { effect }) => {
                actions.extend(undeclared_effect_quick_fixes(
                    workspace, text, uri, file_id, effect, diagnostic, diag_range,
                ));
            }
            AnalysisDiagnosticKind::NameResolution(NameResolverError::UndefinedName(name)) => {
                if let Some(sources) = public_exports.get(name) {
                    for (source_path, _symbol) in sources {
                        let source_path = std::path::Path::new(source_path);
                        let Some(relative_path) =
                            source_path.strip_prefix(&workspace.source_root).ok()
                        else {
                            continue;
                        };
                        let relative_module = relative_path.with_extension("");
                        let segments: Vec<_> = relative_module
                            .components()
                            .filter_map(|component| match component {
                                std::path::Component::Normal(segment) => segment.to_str(),
                                _ => None,
                            })
                            .collect();
                        if segments.is_empty() {
                            continue;
                        }
                        let module_path = format!("package::{}", segments.join("::"));
                        let Some(roots) = workspace
                            .asts
                            .get(file_id.0 as usize)
                            .and_then(|ast| ast.as_ref())
                            .map(|ast| ast.roots.as_slice())
                        else {
                            continue;
                        };
                        let import_stmt = format!("use {module_path}::{{ {name} }}");
                        let Some(edit) = auto_import_edit(text, roots, &import_stmt) else {
                            continue;
                        };
                        actions.push(quick_fix_action(
                            uri,
                            format!("Import '{}' from {}", name, module_path),
                            vec![edit],
                            diagnostic,
                            diag_range,
                            Some(sources.len() == 1),
                        ));
                    }
                }
            }
            _ => {}
        }
    }

    actions
}

fn parser_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    error: &ParserError,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    match error {
        ParserError::UnexpectedToken { expected, .. } => {
            let Some(expected) = expected.token() else {
                return vec![];
            };
            let recovered_ast = workspace
                .asts
                .get(file_id.0 as usize)
                .and_then(|ast| ast.as_ref())
                .is_some_and(|ast| !ast.roots.is_empty());
            if !recovered_ast {
                return vec![];
            }
            let (title, syntax) = match expected {
                crate::token_kind::TokenKind::RightParen => ("Insert ')'", ")"),
                crate::token_kind::TokenKind::RightBracket => ("Insert ']'", "]"),
                crate::token_kind::TokenKind::RightBrace => ("Insert '}'", "}"),
                crate::token_kind::TokenKind::Else => {
                    let Some(edit) = insertion_before_diagnostic_line(
                        text,
                        diagnostic.range.start as usize,
                        "else {}",
                    ) else {
                        return vec![];
                    };
                    return vec![quick_fix_action(
                        uri,
                        "Add required else branch".to_string(),
                        vec![edit],
                        diagnostic,
                        diag_range,
                        Some(true),
                    )];
                }
                _ => return vec![],
            };
            let Some(edit) =
                insertion_before_diagnostic_line(text, diagnostic.range.start as usize, syntax)
            else {
                return vec![];
            };
            vec![quick_fix_action(
                uri,
                title.to_string(),
                vec![edit],
                diagnostic,
                diag_range,
                Some(true),
            )]
        }
        ParserError::ExplicitSelfParameterNotAllowed { parameter } => {
            let Some((start, end)) = comma_list_item_removal_range(
                text,
                parameter.start as usize,
                parameter.end as usize,
            ) else {
                return vec![];
            };
            let Some(range) = byte_span_to_range_utf16(text, start as u32, end as u32) else {
                return vec![];
            };
            vec![quick_fix_action(
                uri,
                "Remove explicit self parameter".to_string(),
                vec![TextEdit::new(range, String::new())],
                diagnostic,
                diag_range,
                Some(true),
            )]
        }
        _ => vec![],
    }
}

fn insertion_before_diagnostic_line(text: &str, offset: usize, syntax: &str) -> Option<TextEdit> {
    let offset = offset.min(text.len());
    let line_start = text[..offset]
        .rfind('\n')
        .map(|index| index + 1)
        .unwrap_or(0);
    let prefix = text.get(line_start..offset)?;
    let (insert_offset, new_text) = if !prefix.is_empty()
        && prefix
            .chars()
            .all(|character| matches!(character, ' ' | '\t' | '\r'))
    {
        (line_start, format!("{prefix}{syntax}\n"))
    } else if prefix.is_empty() && offset < text.len() {
        (line_start, format!("{syntax}\n"))
    } else {
        let new_text = if syntax.starts_with("else") {
            format!(" {syntax}")
        } else {
            syntax.to_string()
        };
        (offset, new_text)
    };
    let range = byte_span_to_range_utf16(text, insert_offset as u32, insert_offset as u32)?;
    Some(TextEdit::new(range, new_text))
}

fn comma_list_item_removal_range(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    text.get(start..end)?;
    let bytes = text.as_bytes();
    let mut after = end;
    while after < bytes.len() && matches!(bytes[after], b' ' | b'\t' | b'\r') {
        after += 1;
    }
    if bytes.get(after) == Some(&b',') {
        after += 1;
        while after < bytes.len() && matches!(bytes[after], b' ' | b'\t' | b'\r') {
            after += 1;
        }
        return Some((start, after));
    }

    let mut before = start;
    while before > 0 && matches!(bytes[before - 1], b' ' | b'\t' | b'\r') {
        before -= 1;
    }
    if before > 0 && bytes[before - 1] == b',' {
        before -= 1;
    }
    Some((before, end))
}

fn arity_mismatch_quick_fixes(
    site: &DiagnosticActionSite<'_>,
    expected: usize,
    found: usize,
) -> Vec<CodeActionOrCommand> {
    use crate::node::Node;
    use crate::node_kinds::expr::ExprKind;

    if expected == found {
        return vec![];
    }
    let Some(node_id) = site.diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = site
        .workspace
        .asts
        .get(site.file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let expression = match ast.find(node_id) {
        Some(Node::Expr(expression)) => Some(expression),
        Some(Node::Stmt(crate::node_kinds::stmt::Stmt {
            kind: crate::node_kinds::stmt::StmtKind::Expr(expression),
            ..
        })) => Some(expression),
        _ => None,
    };
    let Some(expression) = expression else {
        return vec![];
    };

    match &expression.kind {
        ExprKind::Call {
            callee,
            args,
            trailing_block,
            ..
        } if found == args.len() + usize::from(trailing_block.is_some()) => {
            let content_start = args
                .first()
                .map(argument_source_start)
                .into_iter()
                .chain(trailing_block.iter().map(|block| block.span.start as usize))
                .min()
                .unwrap_or(expression.span.end as usize);
            let parentheses = call_parentheses(
                site.text,
                callee.span.end as usize,
                content_start,
                expression.span.end as usize,
            );
            let Some((_, close)) = parentheses else {
                return omitted_call_arity_quick_fixes(
                    site,
                    callee,
                    args,
                    trailing_block.as_ref(),
                    expected,
                    found,
                );
            };
            if found < expected {
                add_missing_arguments(
                    site,
                    &expression,
                    callee,
                    args,
                    trailing_block.as_ref(),
                    close,
                    expected - found,
                )
            } else {
                remove_excess_arguments(
                    site,
                    args,
                    trailing_block.as_ref(),
                    close,
                    expected,
                    found - expected,
                )
            }
        }
        ExprKind::CallEffect {
            effect_name_span,
            args,
            ..
        } if found == args.len() => {
            let content_start = args
                .first()
                .map(argument_source_start)
                .unwrap_or(expression.span.end as usize);
            let Some((_, close)) = call_parentheses(
                site.text,
                effect_name_span.end as usize,
                content_start,
                expression.span.end as usize,
            ) else {
                return vec![];
            };
            if found < expected {
                let placeholders = vec!["{}".to_string(); expected - found];
                missing_argument_action(site, close, !args.is_empty(), placeholders)
            } else {
                remove_excess_arguments(site, args, None, close, expected, found - expected)
            }
        }
        _ => vec![],
    }
}

fn omitted_call_arity_quick_fixes(
    site: &DiagnosticActionSite<'_>,
    callee: &crate::node_kinds::expr::Expr,
    arguments: &[crate::node_kinds::call_arg::CallArg],
    trailing_block: Option<&crate::node_kinds::block::Block>,
    expected: usize,
    found: usize,
) -> Vec<CodeActionOrCommand> {
    if found < expected {
        let missing = expected - found;
        let placeholders = vec!["{}"; missing].join(", ");
        let start = callee.span.end as usize;
        let (end, contents) =
            if let (Some(first), Some(last)) = (arguments.first(), arguments.last()) {
                let source = site
                    .text
                    .get(argument_source_start(first)..argument_source_end(last));
                let Some(source) = source else {
                    return vec![];
                };
                (
                    argument_source_end(last),
                    format!("{}, {placeholders}", source.trim()),
                )
            } else {
                (start, placeholders)
            };
        let Some(range) = byte_span_to_range_utf16(site.text, start as u32, end as u32) else {
            return vec![];
        };
        let title = if missing == 1 {
            "Add missing argument".to_string()
        } else {
            format!("Add {missing} missing arguments")
        };
        return vec![quick_fix_action(
            site.uri,
            title,
            vec![TextEdit::new(range, format!("({contents})"))],
            site.diagnostic,
            site.diag_range,
            Some(true),
        )];
    }

    let excess = found - expected;
    if expected == 0 {
        let start = callee.span.end as usize;
        let end = arguments.last().map(argument_source_end).unwrap_or(start);
        let Some(call_range) = byte_span_to_range_utf16(site.text, start as u32, end as u32) else {
            return vec![];
        };
        let mut edits = vec![TextEdit::new(call_range, "()".to_string())];
        if let Some(block) = trailing_block {
            let Some((block_start, block_end)) =
                block_source_range(site.text, block, site.text.len())
            else {
                return vec![];
            };
            let mut block_start = block_start;
            while block_start > 0
                && matches!(site.text.as_bytes()[block_start - 1], b' ' | b'\t' | b'\r')
            {
                block_start -= 1;
            }
            let Some(range) =
                byte_span_to_range_utf16(site.text, block_start as u32, block_end as u32)
            else {
                return vec![];
            };
            edits.push(TextEdit::new(range, String::new()));
        }
        let title = if excess == 1 {
            "Remove extra argument".to_string()
        } else {
            format!("Remove {excess} extra arguments")
        };
        return vec![quick_fix_action(
            site.uri,
            title,
            edits,
            site.diagnostic,
            site.diag_range,
            Some(true),
        )];
    }

    remove_excess_arguments(site, arguments, trailing_block, 0, expected, excess)
}

fn call_parentheses(
    text: &str,
    callee_end: usize,
    content_start: usize,
    expression_end: usize,
) -> Option<(usize, usize)> {
    let search_end = content_start.min(expression_end).min(text.len());
    let open = callee_end + text.get(callee_end..search_end)?.rfind('(')?;
    let mut lexer = crate::lexer::Lexer::new(text.get(open..expression_end.min(text.len()))?);
    let mut depth = 0usize;
    loop {
        let token = lexer.next().ok()?;
        match token.kind {
            crate::token_kind::TokenKind::LeftParen => depth += 1,
            crate::token_kind::TokenKind::RightParen => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some((open, open + token.start as usize));
                }
            }
            crate::token_kind::TokenKind::EOF => return None,
            _ => {}
        }
    }
}

fn argument_source_start(argument: &crate::node_kinds::call_arg::CallArg) -> usize {
    match &argument.label {
        crate::label::Label::Named(_) => argument.label_span.start as usize,
        _ => argument.span.start as usize,
    }
}

fn argument_source_end(argument: &crate::node_kinds::call_arg::CallArg) -> usize {
    (argument.span.end as usize)
        .max(argument.label_span.end as usize)
        .max(argument.value.span.end as usize)
}

fn add_missing_arguments(
    site: &DiagnosticActionSite<'_>,
    expression: &crate::node_kinds::expr::Expr,
    callee: &crate::node_kinds::expr::Expr,
    arguments: &[crate::node_kinds::call_arg::CallArg],
    trailing_block: Option<&crate::node_kinds::block::Block>,
    close: usize,
    missing: usize,
) -> Vec<CodeActionOrCommand> {
    let parenthesized_block = trailing_block.filter(|block| block.span.end as usize <= close);
    let labels = call_argument_labels(site.workspace, expression, callee);
    let first_missing = arguments.len();
    let placeholders: Vec<String> = (first_missing..first_missing + missing)
        .map(|index| {
            labels
                .as_ref()
                .and_then(|labels| labels.get(index))
                .and_then(Clone::clone)
                .map(|label| format!("{label}: {{}}"))
                .unwrap_or_else(|| "{}".to_string())
        })
        .collect();
    if let Some(block) = parenthesized_block {
        let count = placeholders.len();
        let Some((block_start, _)) = block_source_range(site.text, block, close) else {
            return vec![];
        };
        let Some(range) =
            byte_span_to_range_utf16(site.text, block_start as u32, block_start as u32)
        else {
            return vec![];
        };
        let title = if count == 1 {
            "Add missing argument".to_string()
        } else {
            format!("Add {count} missing arguments")
        };
        return vec![quick_fix_action(
            site.uri,
            title,
            vec![TextEdit::new(
                range,
                format!("{}, ", placeholders.join(", ")),
            )],
            site.diagnostic,
            site.diag_range,
            Some(true),
        )];
    }
    missing_argument_action(site, close, !arguments.is_empty(), placeholders)
}

fn call_argument_labels(
    workspace: &AnalysisWorkspace,
    expression: &crate::node_kinds::expr::Expr,
    callee: &crate::node_kinds::expr::Expr,
) -> Option<Vec<Option<String>>> {
    use crate::node_kinds::expr::ExprKind;
    use crate::types::output::MemberResolution;

    let resolved = [expression.id, callee.id].into_iter().find_map(|id| {
        match workspace.types.member_resolutions.get(&id) {
            Some(MemberResolution::Direct(symbol)) => Some(*symbol),
            _ => None,
        }
    });
    if let Some(resolved) = resolved {
        for info in workspace.types.catalog.enums.values() {
            if let Some(variant) = info
                .variants
                .values()
                .find(|variant| variant.symbol == resolved)
            {
                return Some(variant.payload_labels.clone());
            }
        }
    }
    let ExprKind::Constructor(name) = &callee.kind else {
        return None;
    };
    let symbol = name.symbol().ok()?;
    workspace.types.catalog.structs.get(&symbol).map(|info| {
        info.fields
            .keys()
            .map(|label| Some(label.clone()))
            .collect()
    })
}

fn missing_argument_action(
    site: &DiagnosticActionSite<'_>,
    close: usize,
    has_arguments: bool,
    placeholders: Vec<String>,
) -> Vec<CodeActionOrCommand> {
    if placeholders.is_empty() {
        return vec![];
    }
    let count = placeholders.len();
    let insertion = format!(
        "{}{}",
        if has_arguments { ", " } else { "" },
        placeholders.join(", ")
    );
    let Some(range) = byte_span_to_range_utf16(site.text, close as u32, close as u32) else {
        return vec![];
    };
    let title = if count == 1 {
        "Add missing argument".to_string()
    } else {
        format!("Add {count} missing arguments")
    };
    vec![quick_fix_action(
        site.uri,
        title,
        vec![TextEdit::new(range, insertion)],
        site.diagnostic,
        site.diag_range,
        Some(true),
    )]
}

fn remove_excess_arguments(
    site: &DiagnosticActionSite<'_>,
    arguments: &[crate::node_kinds::call_arg::CallArg],
    trailing_block: Option<&crate::node_kinds::block::Block>,
    close: usize,
    expected: usize,
    excess: usize,
) -> Vec<CodeActionOrCommand> {
    let mut edits = vec![];
    if expected < arguments.len() {
        let first = &arguments[expected];
        let last = arguments.last().unwrap_or(first);
        let mut start = argument_source_start(first);
        if expected > 0 {
            while start > 0
                && matches!(
                    site.text.as_bytes()[start - 1],
                    b' ' | b'\t' | b'\r' | b'\n'
                )
            {
                start -= 1;
            }
            if start > 0 && site.text.as_bytes()[start - 1] == b',' {
                start -= 1;
            }
        }
        let end = argument_source_end(last);
        let Some(range) = byte_span_to_range_utf16(site.text, start as u32, end as u32) else {
            return vec![];
        };
        edits.push(TextEdit::new(range, String::new()));
    }

    if expected <= arguments.len()
        && let Some(block) = trailing_block
    {
        let Some((block_start, block_end)) = block_source_range(site.text, block, site.text.len())
        else {
            return vec![];
        };
        let (start, end) = if block_end <= close {
            let Some(range) =
                separator_list_item_removal_range(site.text, block_start, block_end, ",")
            else {
                return vec![];
            };
            range
        } else {
            let mut start = block_start;
            while start > 0 && matches!(site.text.as_bytes()[start - 1], b' ' | b'\t' | b'\r') {
                start -= 1;
            }
            (start, block_end)
        };
        let Some(range) = byte_span_to_range_utf16(site.text, start as u32, end as u32) else {
            return vec![];
        };
        edits.push(TextEdit::new(range, String::new()));
    }

    if edits.is_empty() {
        return vec![];
    }
    let title = if excess == 1 {
        "Remove extra argument".to_string()
    } else {
        format!("Remove {excess} extra arguments")
    };
    vec![quick_fix_action(
        site.uri,
        title,
        edits,
        site.diagnostic,
        site.diag_range,
        Some(true),
    )]
}

fn block_source_range(
    text: &str,
    block: &crate::node_kinds::block::Block,
    limit: usize,
) -> Option<(usize, usize)> {
    let anchor = (block.span.start as usize).min(text.len());
    let start = if text.as_bytes().get(anchor) == Some(&b'{') {
        anchor
    } else {
        text.get(..anchor)?.rfind('{')?
    };
    let mut lexer = crate::lexer::Lexer::new(text.get(start..limit.min(text.len()))?);
    let mut depth = 0usize;
    loop {
        let token = lexer.next().ok()?;
        match token.kind {
            crate::token_kind::TokenKind::LeftBrace => depth += 1,
            crate::token_kind::TokenKind::RightBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some((start, start + token.end as usize));
                }
            }
            crate::token_kind::TokenKind::EOF => return None,
            _ => {}
        }
    }
}

fn unknown_member_quick_fixes(
    site: &DiagnosticActionSite<'_>,
    label: &str,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = site.diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = site
        .workspace
        .asts
        .get(site.file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(label_span) = member_label_span(ast, node_id) else {
        return vec![];
    };
    let mut candidates: Vec<String> = analysis_completion::complete_in_workspace(
        site.workspace,
        site.document_id,
        label_span.end,
    )
    .into_iter()
    .map(|item| item.label)
    .filter(|candidate| candidate != label && plausible_spelling(label, candidate))
    .collect();
    candidates.sort();
    candidates.dedup();
    let preferred = candidates.len() == 1;
    let Some(range) = byte_span_to_range_utf16(site.text, label_span.start, label_span.end) else {
        return vec![];
    };
    candidates
        .into_iter()
        .map(|candidate| {
            quick_fix_action(
                site.uri,
                format!("Change member to '{candidate}'"),
                vec![TextEdit::new(range, candidate)],
                site.diagnostic,
                site.diag_range,
                Some(preferred),
            )
        })
        .collect()
}

fn member_label_span(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<crate::span::Span> {
    use crate::node::Node;
    use crate::node_kinds::expr::ExprKind;
    use crate::node_kinds::pattern::PatternKind;

    match ast.find(node_id)? {
        Node::Expr(expr) => match &expr.kind {
            ExprKind::Member(_, _, span) => Some(*span),
            ExprKind::Call { callee, .. } => match &callee.kind {
                ExprKind::Member(_, _, span) => Some(*span),
                _ => None,
            },
            _ => None,
        },
        Node::Pattern(pattern) => match &pattern.kind {
            PatternKind::Variant {
                variant_name_span, ..
            } => Some(*variant_name_span),
            _ => None,
        },
        Node::Stmt(crate::node_kinds::stmt::Stmt {
            kind: crate::node_kinds::stmt::StmtKind::Expr(expr),
            ..
        }) => match &expr.kind {
            ExprKind::Member(_, _, span) => Some(*span),
            ExprKind::Call { callee, .. } => match &callee.kind {
                ExprKind::Member(_, _, span) => Some(*span),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn plausible_spelling(actual: &str, candidate: &str) -> bool {
    let distance = edit_distance(actual, candidate);
    let allowance = if actual.len().max(candidate.len()) <= 4 {
        1
    } else {
        2
    };
    distance <= allowance
}

fn edit_distance(left: &str, right: &str) -> usize {
    let right: Vec<char> = right.chars().collect();
    let mut previous: Vec<usize> = (0..=right.len()).collect();
    for (left_index, left_char) in left.chars().enumerate() {
        let mut current = vec![left_index + 1];
        for (right_index, right_char) in right.iter().enumerate() {
            current.push(if left_char == *right_char {
                previous[right_index]
            } else {
                1 + previous[right_index]
                    .min(previous[right_index + 1])
                    .min(current[right_index])
            });
        }
        previous = current;
    }
    previous[right.len()]
}

fn unresolved_variant_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    label: &str,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(label_span) = member_label_span(ast, node_id) else {
        return vec![];
    };
    let dot_start = label_span
        .start
        .checked_sub(1)
        .filter(|start| text.as_bytes().get(*start as usize) == Some(&b'.'));
    let Some(dot_start) = dot_start else {
        return vec![];
    };
    let Some(range) = byte_span_to_range_utf16(text, dot_start, label_span.end) else {
        return vec![];
    };

    let _names =
        crate::name_resolution::symbol::set_symbol_names(workspace.types.display_names.clone());
    let mut owners: Vec<String> = workspace
        .types
        .catalog
        .enums
        .iter()
        .filter(|(_, info)| info.variants.contains_key(label))
        .map(|(symbol, _)| symbol.to_string())
        .collect();
    owners.sort();
    owners.dedup();
    let preferred = owners.len() == 1;
    owners
        .into_iter()
        .map(|owner| {
            let qualified = format!("{owner}.{label}");
            quick_fix_action(
                uri,
                format!("Qualify as '{qualified}'"),
                vec![TextEdit::new(range, qualified)],
                diagnostic,
                diag_range,
                Some(preferred),
            )
        })
        .collect()
}

fn duplicate_predicate_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some((clause, predicate_index)) = where_predicate_location(ast, node_id) else {
        return vec![];
    };
    let Some(predicate) = clause.predicates.get(predicate_index) else {
        return vec![];
    };
    let removal = if clause.predicates.len() == 1 {
        clause.span.start as usize..clause.span.end as usize
    } else {
        let Some((start, end)) = separator_list_item_removal_range(
            text,
            predicate.span.start as usize,
            predicate.span.end as usize,
            "&&",
        ) else {
            return vec![];
        };
        start..end
    };
    let Some(range) = byte_span_to_range_utf16(text, removal.start as u32, removal.end as u32)
    else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        "Remove duplicate where predicate".to_string(),
        vec![TextEdit::new(range, String::new())],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn where_predicate_location(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<(crate::node_kinds::where_clause::WhereClause, usize)> {
    let mut result = None;
    let mut visitor = derive_visitor::visitor_enter_fn(
        |clause: &crate::node_kinds::where_clause::WhereClause| {
            if result.is_none()
                && let Some(index) = clause
                    .predicates
                    .iter()
                    .position(|predicate| predicate.id == node_id)
            {
                result = Some((clause.clone(), index));
            }
        },
    );
    for root in &ast.roots {
        root.drive(&mut visitor);
    }
    drop(visitor);
    result
}

fn redundant_variant_result_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(crate::node::Node::TypeAnnotation(annotation)) = ast.find(node_id) else {
        return vec![];
    };
    let Some((start, end)) = arrow_prefixed_range(
        text,
        annotation.span.start as usize,
        annotation.span.end as usize,
    ) else {
        return vec![];
    };
    let Some(range) = byte_span_to_range_utf16(text, start as u32, end as u32) else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        "Remove redundant variant result type".to_string(),
        vec![TextEdit::new(range, String::new())],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn invalid_variant_result_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(crate::node::Node::TypeAnnotation(annotation)) = ast.find(node_id) else {
        return vec![];
    };
    let crate::node_kinds::type_annotation::TypeAnnotationKind::Nominal {
        name,
        name_span,
        generics,
    } = &annotation.kind
    else {
        return vec![];
    };
    let Some((owner, arity)) = variant_result_owner(ast, node_id) else {
        return vec![];
    };
    if generics.len() != arity || name.name_str() == owner {
        return vec![];
    }
    let Some(range) = byte_span_to_range_utf16(text, name_span.start, name_span.end) else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        format!("Change variant result to '{owner}'"),
        vec![TextEdit::new(range, owner)],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn variant_result_owner(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    result_id: crate::node_id::NodeID,
) -> Option<(String, usize)> {
    let mut result = None;
    let mut visitor = derive_visitor::visitor_enter_fn(|decl: &crate::node_kinds::decl::Decl| {
        if result.is_some() {
            return;
        }
        let crate::node_kinds::decl::DeclKind::Enum {
            name,
            generics,
            body,
            ..
        } = &decl.kind
        else {
            return;
        };
        if body.decls.iter().any(|member| {
            matches!(
                &member.kind,
                crate::node_kinds::decl::DeclKind::EnumVariant {
                    result: Some(annotation),
                    ..
                } if annotation.id == result_id
            )
        }) {
            result = Some((name.name_str(), generics.len()));
        }
    });
    for root in &ast.roots {
        root.drive(&mut visitor);
    }
    drop(visitor);
    result
}

fn invalid_variant_payload_labels_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    variant_name: &str,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    use crate::label::Label;
    use crate::node::Node;
    use crate::node_kinds::{expr::ExprKind, pattern::PatternKind};
    use crate::types::output::MemberResolution;

    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(node) = ast.find(node_id) else {
        return vec![];
    };
    let resolved_variant = match &node {
        Node::Expr(expr) => {
            let callee = match &expr.kind {
                ExprKind::Call { callee, .. } => Some(callee.id),
                _ => None,
            };
            std::iter::once(expr.id).chain(callee).find_map(|id| {
                match workspace.types.member_resolutions.get(&id) {
                    Some(MemberResolution::Direct(symbol)) => Some(*symbol),
                    _ => None,
                }
            })
        }
        Node::Pattern(pattern) => match workspace.types.member_resolutions.get(&pattern.id) {
            Some(MemberResolution::Direct(symbol)) => Some(*symbol),
            _ => None,
        },
        _ => None,
    };
    let mut matching_labels: Vec<Vec<Option<String>>> = workspace
        .types
        .catalog
        .enums
        .values()
        .flat_map(|info| info.variants.iter())
        .filter(|(name, variant)| {
            *name == variant_name && resolved_variant.is_none_or(|symbol| symbol == variant.symbol)
        })
        .map(|(_, variant)| variant.payload_labels.clone())
        .collect();
    matching_labels.dedup();
    let [expected_labels] = matching_labels.as_slice() else {
        return vec![];
    };

    let mut edits = vec![];
    match node {
        Node::Expr(expr) => {
            let ExprKind::Call { args, .. } = &expr.kind else {
                return vec![];
            };
            if expected_labels.len() != args.len() {
                return vec![];
            }
            for (arg, expected) in args.iter().zip(expected_labels) {
                match (&arg.label, expected) {
                    (Label::Named(actual), Some(expected)) if actual != expected => {
                        let Some(range) = byte_span_to_range_utf16(
                            text,
                            arg.label_span.start,
                            arg.label_span.end,
                        ) else {
                            return vec![];
                        };
                        edits.push(TextEdit::new(range, expected.clone()));
                    }
                    (Label::Positional(_), Some(expected)) => {
                        let Some(range) =
                            byte_span_to_range_utf16(text, arg.span.start, arg.span.start)
                        else {
                            return vec![];
                        };
                        edits.push(TextEdit::new(range, format!("{expected}: ")));
                    }
                    (Label::Named(_), None) => {
                        let Some(colon_end) = text
                            .get(arg.label_span.end as usize..arg.value.span.start as usize)
                            .and_then(|source| source.find(':'))
                            .map(|offset| arg.label_span.end as usize + offset + 1)
                        else {
                            return vec![];
                        };
                        let mut end = colon_end;
                        while matches!(text.as_bytes().get(end), Some(b' ' | b'\t' | b'\r')) {
                            end += 1;
                        }
                        let Some(range) =
                            byte_span_to_range_utf16(text, arg.label_span.start, end as u32)
                        else {
                            return vec![];
                        };
                        edits.push(TextEdit::new(range, String::new()));
                    }
                    _ => {}
                }
            }
        }
        Node::Pattern(pattern) => {
            let PatternKind::Variant {
                fields,
                field_labels,
                ..
            } = &pattern.kind
            else {
                return vec![];
            };
            if expected_labels.len() != fields.len() || field_labels.len() != fields.len() {
                return vec![];
            }
            for ((field, actual), expected) in fields.iter().zip(field_labels).zip(expected_labels)
            {
                match (actual, expected) {
                    (Some(actual), Some(expected)) if actual.name_str() != *expected => {
                        let Some((start, end)) = pattern_payload_label_span(
                            text,
                            pattern.span,
                            field.span.start,
                            &actual.name_str(),
                        ) else {
                            return vec![];
                        };
                        let Some(range) = byte_span_to_range_utf16(text, start, end) else {
                            return vec![];
                        };
                        edits.push(TextEdit::new(range, expected.clone()));
                    }
                    (None, Some(expected)) => {
                        let Some(range) =
                            byte_span_to_range_utf16(text, field.span.start, field.span.start)
                        else {
                            return vec![];
                        };
                        edits.push(TextEdit::new(range, format!("{expected}: ")));
                    }
                    (Some(actual), None) => {
                        let Some((start, _)) = pattern_payload_label_span(
                            text,
                            pattern.span,
                            field.span.start,
                            &actual.name_str(),
                        ) else {
                            return vec![];
                        };
                        let Some(range) = byte_span_to_range_utf16(text, start, field.span.start)
                        else {
                            return vec![];
                        };
                        edits.push(TextEdit::new(range, String::new()));
                    }
                    _ => {}
                }
            }
        }
        _ => return vec![],
    }
    if edits.is_empty() {
        return vec![];
    }
    vec![quick_fix_action(
        uri,
        "Use declared variant payload labels".to_string(),
        edits,
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn pattern_payload_label_span(
    text: &str,
    pattern_span: crate::span::Span,
    field_start: u32,
    label: &str,
) -> Option<(u32, u32)> {
    let prefix = text.get(pattern_span.start as usize..field_start as usize)?;
    let relative_start = prefix.rfind(label)?;
    let start = pattern_span.start as usize + relative_start;
    let end = start + label.len();
    text.get(end..field_start as usize)?
        .contains(':')
        .then_some((start as u32, end as u32))
}

fn incompatible_or_pattern_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    use crate::node::Node;
    use crate::node_kinds::pattern::PatternKind;

    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(Node::Pattern(pattern)) = ast.find(node_id) else {
        return vec![];
    };
    let PatternKind::Or(alternatives) = &pattern.kind else {
        return vec![];
    };
    if alternatives.len() < 2 {
        return vec![];
    }
    let Some(arm) = enclosing_match_arm_for_span(ast, pattern.span) else {
        return vec![];
    };
    let arm_source = text.get(arm.span.start as usize..arm.span.end as usize);
    let Some(arm_source) = arm_source else {
        return vec![];
    };
    let pattern_start = pattern
        .span
        .start
        .checked_sub(arm.span.start)
        .map(|v| v as usize);
    let pattern_end = pattern
        .span
        .end
        .checked_sub(arm.span.start)
        .map(|v| v as usize);
    let (Some(pattern_start), Some(pattern_end)) = (pattern_start, pattern_end) else {
        return vec![];
    };
    let line_start = text[..arm.span.start as usize]
        .rfind('\n')
        .map(|index| index + 1)
        .unwrap_or(0);
    let indent = text
        .get(line_start..arm.span.start as usize)
        .filter(|prefix| {
            prefix
                .chars()
                .all(|character| matches!(character, ' ' | '\t'))
        })
        .unwrap_or("");
    let mut replacements = vec![];
    for alternative in alternatives {
        let Some(alternative_source) =
            text.get(alternative.span.start as usize..alternative.span.end as usize)
        else {
            return vec![];
        };
        replacements.push(format!(
            "{}{}{}",
            &arm_source[..pattern_start],
            alternative_source,
            &arm_source[pattern_end..]
        ));
    }
    let replacement = replacements.join(&format!(",\n{indent}"));
    let Some(range) = byte_span_to_range_utf16(text, arm.span.start, arm.span.end) else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        "Split or-pattern into separate match arms".to_string(),
        vec![TextEdit::new(range, replacement)],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn enclosing_match_arm_for_span(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    span: crate::span::Span,
) -> Option<crate::node_kinds::match_arm::MatchArm> {
    let mut candidates = vec![];
    let mut visitor =
        derive_visitor::visitor_enter_fn(|arm: &crate::node_kinds::match_arm::MatchArm| {
            if arm.pattern.span.start <= span.start && span.end <= arm.pattern.span.end {
                candidates.push(arm.clone());
            }
        });
    for root in &ast.roots {
        root.drive(&mut visitor);
    }
    drop(visitor);
    candidates
        .into_iter()
        .min_by_key(|arm| arm.span.end - arm.span.start)
}

fn unreachable_match_arm_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let arm = match ast.find(node_id) {
        Some(crate::node::Node::MatchArm(arm)) => Some(arm),
        Some(crate::node::Node::Pattern(pattern)) => {
            enclosing_match_arm_for_span(ast, pattern.span)
        }
        _ => None,
    };
    let Some(arm) = arm else {
        return vec![];
    };
    let Some((start, end)) = match_arm_removal_range(text, arm.span) else {
        return vec![];
    };
    let Some(range) = byte_span_to_range_utf16(text, start as u32, end as u32) else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        "Remove unreachable match arm".to_string(),
        vec![TextEdit::new(range, String::new())],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn match_arm_removal_range(text: &str, span: crate::span::Span) -> Option<(usize, usize)> {
    text.get(span.start as usize..span.end as usize)?;
    let line_start = text[..span.start as usize]
        .rfind('\n')
        .map(|index| index + 1)
        .unwrap_or(0);
    let prefix = text.get(line_start..span.start as usize)?;
    let starts_line = prefix
        .chars()
        .all(|character| matches!(character, ' ' | '\t'));
    let mut end = span.end as usize;
    while matches!(text.as_bytes().get(end), Some(b' ' | b'\t' | b'\r')) {
        end += 1;
    }
    if text.as_bytes().get(end) == Some(&b',') {
        end += 1;
    }
    while matches!(text.as_bytes().get(end), Some(b' ' | b'\t' | b'\r')) {
        end += 1;
    }
    if starts_line && text.as_bytes().get(end) == Some(&b'\n') {
        end += 1;
        Some((line_start, end))
    } else {
        Some((span.start as usize, end))
    }
}

fn unreachable_code_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some((block, index)) = block_body_location(ast, node_id) else {
        return vec![];
    };
    let Some(first) = block.body.get(index) else {
        return vec![];
    };
    let Some(last) = block.body.last() else {
        return vec![];
    };
    let first_span = first.span();
    let last_span = last.span();
    let line_start = text[..first_span.start as usize]
        .rfind('\n')
        .map(|position| position + 1)
        .unwrap_or(first_span.start as usize);
    let start = text
        .get(line_start..first_span.start as usize)
        .filter(|prefix| {
            prefix
                .chars()
                .all(|character| matches!(character, ' ' | '\t'))
        })
        .map(|_| line_start)
        .unwrap_or(first_span.start as usize);
    let mut end = last_span.end as usize;
    if let Some(close) = text
        .get(last_span.end as usize..block.span.end as usize)
        .and_then(|suffix| suffix.rfind('}'))
        .map(|offset| last_span.end as usize + offset)
        && text
            .get(last_span.end as usize..close)
            .is_some_and(|suffix| suffix.chars().all(char::is_whitespace))
    {
        end = text[..close]
            .rfind('\n')
            .map(|position| position + 1)
            .unwrap_or(end);
    }
    let Some(range) = byte_span_to_range_utf16(text, start as u32, end as u32) else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        "Remove unreachable code".to_string(),
        vec![TextEdit::new(range, String::new())],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn block_body_location(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<(crate::node_kinds::block::Block, usize)> {
    let mut result = None;
    let mut visitor =
        derive_visitor::visitor_enter_fn(|block: &crate::node_kinds::block::Block| {
            if result.is_none()
                && let Some(index) = block.body.iter().position(|node| node.node_id() == node_id)
            {
                result = Some((block.clone(), index));
            }
        });
    for root in &ast.roots {
        root.drive(&mut visitor);
    }
    drop(visitor);
    result
}

fn arrow_prefixed_range(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    text.get(start..end)?;
    let bytes = text.as_bytes();
    let mut arrow_end = start;
    while arrow_end > 0 && bytes[arrow_end - 1].is_ascii_whitespace() {
        arrow_end -= 1;
    }
    if arrow_end < 2 || text.get(arrow_end - 2..arrow_end)? != "->" {
        return None;
    }
    let mut removal_start = arrow_end - 2;
    while removal_start > 0 && matches!(bytes[removal_start - 1], b' ' | b'\t' | b'\r') {
        removal_start -= 1;
    }
    Some((removal_start, end))
}

fn duplicate_associated_binding_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some((annotation, binding_index)) = associated_binding_location(ast, node_id) else {
        return vec![];
    };
    let crate::node_kinds::type_annotation::TypeAnnotationKind::Any {
        protocol,
        assoc_bindings,
    } = &annotation.kind
    else {
        return vec![];
    };
    let Some(binding) = assoc_bindings.get(binding_index) else {
        return vec![];
    };
    let removal = if assoc_bindings.len() == 1 {
        protocol.span.end as usize..annotation.span.end as usize
    } else {
        let Some((start, end)) = separator_list_item_removal_range(
            text,
            binding.span.start as usize,
            binding.span.end as usize,
            ",",
        ) else {
            return vec![];
        };
        start..end
    };
    let Some(range) = byte_span_to_range_utf16(text, removal.start as u32, removal.end as u32)
    else {
        return vec![];
    };
    vec![quick_fix_action(
        uri,
        "Remove duplicate associated type binding".to_string(),
        vec![TextEdit::new(range, String::new())],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn unknown_associated_binding_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some((annotation, binding_index)) = associated_binding_location(ast, node_id) else {
        return vec![];
    };
    let crate::node_kinds::type_annotation::TypeAnnotationKind::Any {
        protocol,
        assoc_bindings,
    } = &annotation.kind
    else {
        return vec![];
    };
    let Some(binding) = assoc_bindings.get(binding_index) else {
        return vec![];
    };
    let Ok(protocol) = protocol.symbol() else {
        return vec![];
    };
    let mut candidates: Vec<String> = workspace
        .types
        .catalog
        .associated_types_in(protocol)
        .into_iter()
        .map(|(name, _)| name)
        .filter(|name| name != &binding.name.name_str())
        .collect();
    candidates.sort();
    candidates.dedup();
    let preferred = candidates.len() == 1;
    let Some(range) =
        byte_span_to_range_utf16(text, binding.name_span.start, binding.name_span.end)
    else {
        return vec![];
    };
    candidates
        .into_iter()
        .map(|candidate| {
            quick_fix_action(
                uri,
                format!("Change associated type binding to '{candidate}'"),
                vec![TextEdit::new(range, candidate)],
                diagnostic,
                diag_range,
                Some(preferred),
            )
        })
        .collect()
}

fn associated_binding_location(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    node_id: crate::node_id::NodeID,
) -> Option<(crate::node_kinds::type_annotation::TypeAnnotation, usize)> {
    let mut result = None;
    let mut visitor = derive_visitor::visitor_enter_fn(
        |annotation: &crate::node_kinds::type_annotation::TypeAnnotation| {
            if result.is_some() {
                return;
            }
            let crate::node_kinds::type_annotation::TypeAnnotationKind::Any {
                assoc_bindings, ..
            } = &annotation.kind
            else {
                return;
            };
            if let Some(index) = assoc_bindings
                .iter()
                .position(|binding| binding.id == node_id)
            {
                result = Some((annotation.clone(), index));
            }
        },
    );
    for root in &ast.roots {
        root.drive(&mut visitor);
    }
    drop(visitor);
    result
}

fn generic_shadowing_quick_fixes(
    workspace: &AnalysisWorkspace,
    uri: &Url,
    file_id: crate::node_id::FileID,
    name: &str,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(crate::node::Node::GenericDecl(generic)) = ast.find(node_id) else {
        return vec![];
    };
    let used_names: FxHashSet<&str> = workspace
        .resolved_names
        .symbol_names
        .values()
        .map(String::as_str)
        .collect();
    let new_name = (1..)
        .map(|suffix| format!("{name}{suffix}"))
        .find(|candidate| !used_names.contains(candidate.as_str()));
    let Some(new_name) = new_name else {
        return vec![];
    };
    let Some(edit) = rename_at(workspace, uri, generic.name_span.start, &new_name) else {
        return vec![];
    };
    vec![quick_fix_workspace_action(
        format!("Rename inner generic to '{new_name}'"),
        edit,
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn undeclared_effect_quick_fixes(
    workspace: &AnalysisWorkspace,
    text: &str,
    uri: &Url,
    file_id: crate::node_id::FileID,
    effect: &str,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
) -> Vec<CodeActionOrCommand> {
    let Some(node_id) = diagnostic.node_id else {
        return vec![];
    };
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(crate::node::Node::Func(func)) = ast.find(node_id) else {
        return vec![];
    };
    if func.effects.is_open {
        return vec![];
    }
    let effect = effect.trim_start_matches('\'');
    let edit = if let (Some(first), Some(last)) =
        (func.effects.spans.first(), func.effects.spans.last())
    {
        let quote_start = first.start.checked_sub(1);
        if quote_start.is_some_and(|start| text.as_bytes().get(start as usize) == Some(&b'\'')) {
            let quote_start = quote_start.unwrap_or(first.start);
            let Some(existing) = text.get(first.start as usize..last.end as usize) else {
                return vec![];
            };
            let Some(range) = byte_span_to_range_utf16(text, quote_start, last.end) else {
                return vec![];
            };
            TextEdit::new(range, format!("'[{existing}, {effect}]"))
        } else {
            let Some(close) = text
                .get(last.end as usize..func.body.span.start as usize)
                .and_then(|suffix| suffix.find(']'))
                .map(|offset| last.end as usize + offset)
            else {
                return vec![];
            };
            let Some(range) = byte_span_to_range_utf16(text, close as u32, close as u32) else {
                return vec![];
            };
            TextEdit::new(range, format!(", {effect}"))
        }
    } else {
        let Some(annotation_start) = text
            .get(func.name_span.end as usize..func.body.span.start as usize)
            .and_then(|source| source.rfind("'["))
            .map(|offset| func.name_span.end as usize + offset + 2)
        else {
            return vec![];
        };
        let Some(range) =
            byte_span_to_range_utf16(text, annotation_start as u32, annotation_start as u32)
        else {
            return vec![];
        };
        TextEdit::new(range, effect.to_string())
    };

    vec![quick_fix_action(
        uri,
        format!("Add '{effect} to effect annotation"),
        vec![edit],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

pub(super) fn separator_list_item_removal_range(
    text: &str,
    start: usize,
    end: usize,
    separator: &str,
) -> Option<(usize, usize)> {
    text.get(start..end)?;
    let bytes = text.as_bytes();
    let mut after = end;
    while after < bytes.len() && bytes[after].is_ascii_whitespace() {
        after += 1;
    }
    if text.get(after..)?.starts_with(separator) {
        after += separator.len();
        while after < bytes.len() && bytes[after].is_ascii_whitespace() {
            after += 1;
        }
        return Some((start, after));
    }

    let mut before = start;
    while before > 0 && bytes[before - 1].is_ascii_whitespace() {
        before -= 1;
    }
    let separator_start = before.checked_sub(separator.len())?;
    if text.get(separator_start..before)? == separator {
        let mut removal_start = separator_start;
        while removal_start > 0 && matches!(bytes[removal_start - 1], b' ' | b'\t' | b'\r') {
            removal_start -= 1;
        }
        Some((removal_start, end))
    } else {
        None
    }
}

/// Build one quick fix per compiler-provided protocol candidate. The
/// diagnostic span covers the member use, whose text ends in `.label`
/// followed by the argument list. Each fix rewrites the receiver-dot form
/// into a protocol-static call with the receiver as first argument.
fn ambiguous_member_quick_fixes(
    site: &DiagnosticActionSite<'_>,
    diag_start: usize,
    diag_end: usize,
    label: &str,
    candidates: &[String],
) -> Vec<CodeActionOrCommand> {
    let text = site.text;
    let uri = site.uri;
    let diagnostic = site.diagnostic;
    let diag_range = site.diag_range;
    let Some(snippet) = text.get(diag_start..diag_end) else {
        return vec![];
    };
    // The span must actually be a `receiver.label(...)` use: a discharge
    // site for a scheme-carried constraint points at the caller instead,
    // where no textual rewrite applies (the diagnostic alone serves there).
    let needle = format!(".{label}");
    let Some(dot) = snippet.rfind(&needle) else {
        return vec![];
    };
    let receiver = snippet[..dot].trim();
    if receiver.is_empty() {
        return vec![];
    }
    let receiver_start = diag_start + snippet[..dot].len() - snippet[..dot].trim_start().len();
    let label_end = diag_start + dot + needle.len();
    if text.as_bytes().get(label_end) != Some(&b'(') {
        return vec![];
    }
    let after_paren = label_end + 1;
    let empty_args = text[after_paren..].trim_start().starts_with(')');
    let insertion = if empty_args {
        receiver.to_string()
    } else {
        format!("{receiver}, ")
    };

    let mut actions = vec![];
    for candidate in candidates {
        let Some(callee_range) =
            byte_span_to_range_utf16(text, receiver_start as u32, label_end as u32)
        else {
            continue;
        };
        let Some(insert_range) =
            byte_span_to_range_utf16(text, after_paren as u32, after_paren as u32)
        else {
            continue;
        };
        let edits = vec![
            TextEdit::new(callee_range, format!("{candidate}.{label}")),
            TextEdit::new(insert_range, insertion.clone()),
        ];
        let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> =
            std::collections::HashMap::new();
        changes.insert(uri.clone(), edits);
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: format!("Use '{candidate}.{label}({receiver}...)'"),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: Some(vec![code_action_diagnostic(diagnostic, diag_range)]),
            edit: Some(WorkspaceEdit {
                changes: Some(changes),
                document_changes: None,
                change_annotations: None,
            }),
            command: None,
            is_preferred: None,
            disabled: None,
            data: None,
        }));
    }
    actions
}

fn missing_witness_quick_fixes(
    site: &DiagnosticActionSite<'_>,
    diag_start: u32,
    requirement: &str,
    protocol: &str,
) -> Vec<CodeActionOrCommand> {
    let workspace = site.workspace;
    let text = site.text;
    let uri = site.uri;
    let file_id = site.file_id;
    let diagnostic = site.diagnostic;
    let diag_range = site.diag_range;
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(extend) = enclosing_extend_at(ast, diag_start) else {
        return vec![];
    };
    let crate::node_kinds::decl::DeclKind::Extend { body, .. } = &extend.kind else {
        return vec![];
    };
    let signature = source_requirement_signature(workspace, requirement, protocol)
        .or_else(|| catalog_requirement_signature(workspace, requirement, protocol))
        .unwrap_or_else(|| format!("func {requirement}()"));
    let stub = method_stub(&signature);
    let Some((insert_offset, insert_text)) = insertion_before_closing_brace(text, body.span, &stub)
    else {
        return vec![];
    };
    let Some(range) = byte_span_to_range_utf16(text, insert_offset as u32, insert_offset as u32)
    else {
        return vec![];
    };

    vec![quick_fix_action(
        uri,
        format!("Add requirement '{requirement}'"),
        vec![TextEdit::new(range, insert_text)],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn non_exhaustive_match_quick_fixes(
    site: &DiagnosticActionSite<'_>,
    diag_start: u32,
    diagnostic_missing: &[String],
) -> Vec<CodeActionOrCommand> {
    let workspace = site.workspace;
    let text = site.text;
    let uri = site.uri;
    let file_id = site.file_id;
    let diagnostic = site.diagnostic;
    let diag_range = site.diag_range;
    let Some(ast) = workspace
        .asts
        .get(file_id.0 as usize)
        .and_then(|ast| ast.as_ref())
    else {
        return vec![];
    };
    let Some(expr) = enclosing_match_at(ast, diag_start) else {
        return vec![];
    };
    let patterns = missing_patterns_for_match(workspace, &expr)
        .filter(|patterns| !patterns.is_empty())
        .unwrap_or_else(|| diagnostic_missing.to_vec());
    if patterns.is_empty() {
        return vec![];
    }
    let arms = patterns
        .iter()
        .map(|pattern| format!("{pattern} -> {{}}"))
        .collect::<Vec<_>>()
        .join("\n");
    let Some((insert_offset, insert_text)) = insertion_before_closing_brace(text, expr.span, &arms)
    else {
        return vec![];
    };
    let Some(range) = byte_span_to_range_utf16(text, insert_offset as u32, insert_offset as u32)
    else {
        return vec![];
    };
    let title = if patterns.len() == 1 {
        format!("Add missing match arm '{}'", patterns[0])
    } else {
        "Add missing match arms".to_string()
    };

    vec![quick_fix_action(
        uri,
        title,
        vec![TextEdit::new(range, insert_text)],
        diagnostic,
        diag_range,
        Some(true),
    )]
}

fn quick_fix_action(
    uri: &Url,
    title: String,
    edits: Vec<TextEdit>,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
    is_preferred: Option<bool>,
) -> CodeActionOrCommand {
    let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> =
        std::collections::HashMap::new();
    changes.insert(uri.clone(), edits);
    CodeActionOrCommand::CodeAction(CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![code_action_diagnostic(diagnostic, diag_range)]),
        edit: Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        }),
        command: None,
        is_preferred,
        disabled: None,
        data: None,
    })
}

fn quick_fix_workspace_action(
    title: String,
    edit: WorkspaceEdit,
    diagnostic: &AnalysisDiagnostic,
    diag_range: Range,
    is_preferred: Option<bool>,
) -> CodeActionOrCommand {
    CodeActionOrCommand::CodeAction(CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![code_action_diagnostic(diagnostic, diag_range)]),
        edit: Some(edit),
        command: None,
        is_preferred,
        disabled: None,
        data: None,
    })
}

pub(super) fn code_action_diagnostic(diagnostic: &AnalysisDiagnostic, range: Range) -> Diagnostic {
    let severity = match diagnostic.severity {
        AnalysisSeverity::Error => DiagnosticSeverity::ERROR,
        AnalysisSeverity::Warning => DiagnosticSeverity::WARNING,
        AnalysisSeverity::Info => DiagnosticSeverity::INFORMATION,
    };
    Diagnostic {
        range,
        severity: Some(severity),
        code: diagnostic
            .kind
            .as_ref()
            .map(|kind| NumberOrString::String(kind.code().to_string())),
        source: Some("talk".to_string()),
        message: diagnostic.message.clone(),
        ..Default::default()
    }
}

fn enclosing_extend_at(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    byte_offset: u32,
) -> Option<crate::node_kinds::decl::Decl> {
    crate::analysis::node_ids_at_offset(ast, byte_offset)
        .into_iter()
        .filter_map(|node_id| match ast.find(node_id) {
            Some(crate::node::Node::Decl(
                decl @ crate::node_kinds::decl::Decl {
                    kind: crate::node_kinds::decl::DeclKind::Extend { .. },
                    ..
                },
            )) => Some(decl),
            _ => None,
        })
        .find(|decl| decl.span.start <= byte_offset && byte_offset <= decl.span.end)
}

fn enclosing_match_at(
    ast: &crate::ast::AST<crate::ast::NameResolved>,
    byte_offset: u32,
) -> Option<crate::node_kinds::expr::Expr> {
    crate::analysis::node_ids_at_offset(ast, byte_offset)
        .into_iter()
        .filter_map(|node_id| match ast.find(node_id) {
            Some(crate::node::Node::Expr(expr)) => Some(expr),
            _ => None,
        })
        .find(|expr| match &expr.kind {
            crate::node_kinds::expr::ExprKind::Match(scrutinee, _) => {
                scrutinee.span.start <= byte_offset && byte_offset <= scrutinee.span.end
            }
            _ => false,
        })
}

fn source_requirement_signature(
    workspace: &AnalysisWorkspace,
    requirement: &str,
    protocol: &str,
) -> Option<String> {
    let protocol_name = protocol.split('<').next().unwrap_or(protocol);
    for ast in workspace.asts.iter().flatten() {
        let mut result = None;
        let mut visitor =
            derive_visitor::visitor_enter_fn(|decl: &crate::node_kinds::decl::Decl| {
                if result.is_some() {
                    return;
                }
                let crate::node_kinds::decl::DeclKind::Protocol { name, body, .. } = &decl.kind
                else {
                    return;
                };
                if name.name_str() != protocol_name {
                    return;
                }
                for member in &body.decls {
                    match &member.kind {
                        crate::node_kinds::decl::DeclKind::MethodRequirement {
                            signature, ..
                        }
                        | crate::node_kinds::decl::DeclKind::FuncSignature(signature)
                            if signature.name.name_str() == requirement =>
                        {
                            result = Some(crate::parsing::formatter::format_node(
                                &crate::node::Node::Decl(member.clone()),
                                &ast.meta,
                            ));
                            return;
                        }
                        _ => {}
                    }
                }
            });
        for root in &ast.roots {
            root.drive(&mut visitor);
        }
        drop(visitor);
        if let Some(result) = result {
            return Some(strip_implicit_self_param(result.trim()));
        }
    }
    None
}

fn catalog_requirement_signature(
    workspace: &AnalysisWorkspace,
    requirement: &str,
    protocol: &str,
) -> Option<String> {
    let _names =
        crate::name_resolution::symbol::set_symbol_names(workspace.types.display_names.clone());
    let mut refs: Vec<crate::types::ty::ProtocolRef> = workspace
        .types
        .catalog
        .protocols
        .keys()
        .copied()
        .map(crate::types::ty::ProtocolRef::bare)
        .collect();
    for (_, protocol_ref) in workspace.types.catalog.conformances.keys() {
        if !refs.contains(protocol_ref) {
            refs.push(protocol_ref.clone());
        }
    }

    for protocol_ref in refs {
        for (owner, label, req) in workspace
            .types
            .catalog
            .requirements_for_conformance(&protocol_ref)
        {
            if label == requirement && owner.to_string() == protocol {
                return signature_from_requirement_scheme(&workspace.types, &label, req.symbol);
            }
        }
    }
    None
}

fn signature_from_requirement_scheme(
    types: &crate::types::TypeOutput,
    label: &str,
    symbol: crate::name_resolution::symbol::Symbol,
) -> Option<String> {
    let scheme = types.schemes.get(&symbol)?;
    let crate::types::ty::Ty::Func(params, ret, _) = &scheme.ty else {
        return None;
    };
    let params = params
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("arg{index}: {}", ty.render_mono()))
        .collect::<Vec<_>>()
        .join(", ");
    Some(strip_implicit_self_param(&format!(
        "func {label}({params}) -> {}",
        ret.render_mono()
    )))
}

fn strip_implicit_self_param(signature: &str) -> String {
    let Some(open) = signature.find('(') else {
        return signature.to_string();
    };
    let after_open = &signature[open + 1..];
    let leading = after_open.len() - after_open.trim_start().len();
    let params = &after_open[leading..];
    if !params.starts_with("self:") {
        return signature.to_string();
    }
    if let Some(comma) = params.find(',') {
        return format!(
            "{}{}",
            &signature[..open + 1],
            params[comma + 1..].trim_start()
        );
    }
    if let Some(close) = params.find(')') {
        return format!("{}{}", &signature[..open + 1], &params[close..]);
    }
    signature.to_string()
}

fn method_stub(signature: &str) -> String {
    format!("{} {{\n\t{{}}\n}}", signature.trim())
}

fn missing_patterns_for_match(
    workspace: &AnalysisWorkspace,
    expr: &crate::node_kinds::expr::Expr,
) -> Option<Vec<String>> {
    let crate::node_kinds::expr::ExprKind::Match(scrutinee, arms) = &expr.kind else {
        return None;
    };
    let mut ty = workspace.types.node_types.get(&scrutinee.id)?.clone();
    if let crate::types::ty::Ty::Borrow(_, inner) = ty {
        ty = *inner;
    }
    let arms: Vec<&crate::node_kinds::pattern::Pattern> =
        arms.iter().map(|arm| &arm.pattern).collect();
    Some(crate::types::exhaustiveness::check_match(&workspace.types.catalog, &ty, &arms).missing)
}

fn insertion_before_closing_brace(
    text: &str,
    span: crate::span::Span,
    block: &str,
) -> Option<(usize, String)> {
    let span_text = text.get(span.start as usize..span.end as usize)?;
    let close = span.start as usize + span_text.rfind('}')?;
    let line_start = text[..close].rfind('\n').map(|idx| idx + 1).unwrap_or(0);
    let before_close_on_line = text.get(line_start..close)?;
    let base_indent = if before_close_on_line.trim().is_empty() {
        before_close_on_line
    } else {
        text.get(line_start..line_start + leading_whitespace_len(before_close_on_line))?
    };
    let child_indent = format!("{base_indent}\t");
    let indented = indent_block(block, &child_indent);

    if before_close_on_line.trim().is_empty() {
        Some((line_start, format!("{indented}\n")))
    } else {
        Some((close, format!("\n{indented}\n{base_indent}")))
    }
}

fn leading_whitespace_len(text: &str) -> usize {
    text.char_indices()
        .find_map(|(idx, ch)| (!matches!(ch, ' ' | '\t')).then_some(idx))
        .unwrap_or(text.len())
}

fn indent_block(block: &str, indent: &str) -> String {
    let mut result = String::new();
    for (index, line) in block.lines().enumerate() {
        if index > 0 {
            result.push('\n');
        }
        result.push_str(indent);
        result.push_str(line);
    }
    result
}
