//! Shared requirement suggestions (CLEAN-06): a protocol requirement
//! rendered for editor insertion, keyed by symbol. Completion and code
//! actions consume `RequirementSuggestion` and only decide snippet
//! syntax and edit placement; the signature lookup (source text first,
//! scheme fallback) and implicit-`self` stripping live here.

use derive_visitor::Drive;

use crate::analysis::workspace::Workspace;
use crate::ast::{AST, NameResolved};
use crate::name_resolution::symbol::{Symbol, set_symbol_names};
use crate::node::Node;
use crate::node_kinds::decl::{Decl, DeclKind};
use crate::types::TypeOutput;
use crate::types::catalog::Requirement;
use crate::types::ty::{ProtocolRef, Ty};

pub struct RequirementSuggestion {
    pub label: String,
    pub owner: String,
    /// The canonical signature with the implicit `self` parameter
    /// stripped.
    pub signature: String,
}

impl RequirementSuggestion {
    /// The last-resort suggestion when neither source nor scheme can
    /// describe the requirement.
    pub fn fallback(owner: &str, label: &str) -> Self {
        Self {
            label: label.to_string(),
            owner: owner.to_string(),
            signature: format!("func {label}()"),
        }
    }

    /// The conformance-witness stub. Snippet form leaves a `$0` tab
    /// stop for the body; the plain form leaves an empty body.
    pub fn stub(&self, snippet: bool) -> String {
        let body = if snippet { "$0" } else { "{}" };
        format!("{} {{\n\t{}\n}}", self.signature.trim(), body)
    }
}

/// The canonical suggestion for a catalog requirement: the declared
/// source text when one of `asts` holds it, the scheme otherwise, and a
/// bare `func label()` when neither can say more.
pub fn requirement_suggestion<'a>(
    asts: impl IntoIterator<Item = &'a AST<NameResolved>>,
    types: &TypeOutput,
    owner: String,
    label: String,
    requirement: &Requirement,
) -> RequirementSuggestion {
    let signature = source_requirement_signature(asts, requirement.symbol)
        .or_else(|| requirement_signature_from_scheme(types, &label, requirement));
    match signature {
        Some(signature) => RequirementSuggestion {
            label,
            owner,
            signature,
        },
        None => RequirementSuggestion::fallback(&owner, &label),
    }
}

/// The name-keyed entry for diagnostics that only carry rendered names
/// (`TypeError::MissingWitness`): resolves the protocol and requirement
/// names back to the catalog requirement, then builds the symbol-keyed
/// suggestion.
pub fn requirement_suggestion_by_name(
    workspace: &Workspace,
    protocol: &str,
    requirement: &str,
) -> Option<RequirementSuggestion> {
    let _names = set_symbol_names(workspace.types.display_names.clone());
    let catalog = &workspace.types.catalog;
    let mut refs: Vec<ProtocolRef> = catalog
        .protocols
        .keys()
        .copied()
        .map(ProtocolRef::bare)
        .collect();
    for row in catalog.conformances.values() {
        if !refs.contains(&row.protocol) {
            refs.push(row.protocol.clone());
        }
    }

    for protocol_ref in refs {
        for (owner, label, req) in catalog.requirements_for_conformance(&protocol_ref) {
            if label == requirement && owner.to_string() == protocol {
                return Some(requirement_suggestion(
                    workspace.asts.iter().flatten(),
                    &workspace.types,
                    owner.to_string(),
                    label,
                    &req,
                ));
            }
        }
    }
    None
}

fn source_requirement_signature<'a>(
    asts: impl IntoIterator<Item = &'a AST<NameResolved>>,
    symbol: Symbol,
) -> Option<String> {
    asts
        .into_iter()
        .find_map(|ast| source_requirement_signature_in_ast(ast, symbol))
}

fn source_requirement_signature_in_ast(ast: &AST<NameResolved>, symbol: Symbol) -> Option<String> {
    let mut result = None;
    let mut visitor = derive_visitor::visitor_enter_fn(|decl: &Decl| {
        if result.is_some() {
            return;
        }
        match &decl.kind {
            DeclKind::MethodRequirement { signature, .. } | DeclKind::FuncSignature(signature)
                if signature.name.symbol().ok() == Some(symbol) =>
            {
                result = Some(crate::parsing::formatter::format_node(
                    &Node::Decl(decl.clone()),
                    &ast.meta,
                ));
            }
            _ => {}
        }
    });
    for root in &ast.roots {
        root.drive(&mut visitor);
    }
    drop(visitor);
    result.map(|signature: String| strip_implicit_self_param(signature.trim()))
}

fn requirement_signature_from_scheme(
    types: &TypeOutput,
    label: &str,
    requirement: &Requirement,
) -> Option<String> {
    let scheme = types.schemes.get(&requirement.symbol)?;
    let Ty::Func(params, ret, _) = &scheme.ty else {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::DocumentInput;

    fn workspace(code: &str) -> Workspace {
        let doc = DocumentInput {
            id: "main.tlk".to_string(),
            path: "main.tlk".to_string(),
            version: 0,
            text: code.into(),
        };
        Workspace::new(vec![doc]).expect("workspace")
    }

    #[test]
    fn suggestion_by_name_finds_the_source_signature() {
        let code = "protocol P {\n\tfunc required(count: Int) -> Bool\n}\nstruct S {}\nextend S: P {}\n";
        let ws = workspace(code);
        let suggestion = requirement_suggestion_by_name(&ws, "P", "required")
            .expect("suggestion for the missing witness");
        assert_eq!(suggestion.signature, "func required(count: Int) -> Bool");
        assert_eq!(suggestion.owner, "P");
        assert_eq!(
            suggestion.stub(false),
            "func required(count: Int) -> Bool {\n\t{}\n}"
        );
        assert_eq!(
            suggestion.stub(true),
            "func required(count: Int) -> Bool {\n\t$0\n}"
        );
    }

    #[test]
    fn suggestion_by_name_falls_back_to_the_scheme() {
        // A requirement from a bundled module has no source in the
        // workspace ASTs; the scheme still describes it.
        let code = "struct S {}\nextend S: Showable {}\n";
        let ws = workspace(code);
        let suggestion = requirement_suggestion_by_name(&ws, "Showable", "show")
            .expect("suggestion for the missing witness");
        assert!(
            suggestion.signature.starts_with("func show("),
            "{}",
            suggestion.signature
        );
    }
}
