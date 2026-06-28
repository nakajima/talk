//! Editor-facing ownership facts. This module keeps LSP protocol types out
//! of the analysis layer: callers get byte offsets, rendered labels, and
//! tooltips derived from the ownership pass.

use rustc_hash::FxHashSet;

use crate::analysis::{DocumentId, TextRange, workspace::Workspace};
use crate::mir::DropElaboration;
use crate::name_resolution::symbol::{Symbol, set_symbol_names};
use crate::node_id::NodeID;
use crate::ownership::{DropObligation, KeyPath, LoanFact, MoveFact, OwnershipOutput};
use crate::types::ty::{BorrowKind, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipInlayHintKind {
    Move,
    Borrow,
    Drop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnershipInlayHint {
    pub position: u32,
    pub label: String,
    pub tooltip: String,
    pub kind: OwnershipInlayHintKind,
}

pub fn hover_details_for_node(workspace: &Workspace, node: NodeID, ty: Option<&Ty>) -> Vec<String> {
    let _names = set_symbol_names(workspace.types.display_names.clone());
    let mut details = Vec::new();
    if let Some(ty) = ty {
        details.extend(type_details(&workspace.ownership, ty));
    }
    details.extend(fact_details_for_node(&workspace.ownership, node));
    dedup(details)
}

pub fn ownership_inlay_hints(
    workspace: &Workspace,
    document_id: &DocumentId,
    range: TextRange,
) -> Vec<OwnershipInlayHint> {
    let _names = set_symbol_names(workspace.types.display_names.clone());
    let mut hints = Vec::new();

    for fact in &workspace.ownership.facts.moves {
        let Some(position) = fact_position(workspace, document_id, range, fact.node) else {
            continue;
        };
        hints.push(OwnershipInlayHint {
            position,
            label: " move".to_string(),
            tooltip: format!(
                "Moves {} of type {}",
                render_key_path(&fact.source),
                fact.ty.render_mono()
            ),
            kind: OwnershipInlayHintKind::Move,
        });
    }

    for fact in &workspace.ownership.facts.borrows {
        let Some(position) = fact_position(workspace, document_id, range, fact.node) else {
            continue;
        };
        hints.push(OwnershipInlayHint {
            position,
            label: format!(" {}", borrow_prefix(fact.kind)),
            tooltip: render_loan_tooltip(fact),
            kind: OwnershipInlayHintKind::Borrow,
        });
    }

    for obligation in &workspace.ownership.drop_plan.obligations {
        let Some(position) = fact_position(workspace, document_id, range, obligation.node) else {
            continue;
        };
        let label = match obligation.kind {
            DropElaboration::Static => " drop",
            DropElaboration::Dead => " drop(dead)",
            DropElaboration::Conditional => " drop?",
            DropElaboration::Open => " drop(open)",
        };
        hints.push(OwnershipInlayHint {
            position,
            label: label.to_string(),
            tooltip: render_drop_tooltip(obligation),
            kind: OwnershipInlayHintKind::Drop,
        });
    }

    dedup_hints(hints)
}

fn fact_position(
    workspace: &Workspace,
    document_id: &DocumentId,
    requested: TextRange,
    node: Option<NodeID>,
) -> Option<u32> {
    let node = node?;
    let (fact_document, range) = workspace.range_for_node(node, false)?;
    if &fact_document != document_id {
        return None;
    }
    let position = range.end;
    if position < requested.start || position > requested.end {
        return None;
    }
    Some(position)
}

fn type_details(output: &OwnershipOutput, ty: &Ty) -> Vec<String> {
    let mut details = Vec::new();
    match ty {
        Ty::Borrow(kind, inner) => {
            details.push(format!(
                "{} borrow of {}",
                borrow_kind_name(*kind),
                inner.render_mono()
            ));
        }
        Ty::Nominal(symbol, _) => {
            if output.borrowed_types.contains(symbol) {
                details.push("borrowed view".to_string());
            }
            if output.owned_types.contains(symbol) {
                details.push("owned".to_string());
            }
            if output.copyable_types.contains(symbol) {
                details.push("copy".to_string());
            }
        }
        _ => {}
    }
    if output.type_has_needs_drop_fact(ty) {
        details.push("needs drop".to_string());
    }
    details
}

fn fact_details_for_node(output: &OwnershipOutput, node: NodeID) -> Vec<String> {
    let mut details = Vec::new();
    for fact in output
        .facts
        .moves
        .iter()
        .filter(|fact| fact.node == Some(node))
    {
        details.push(render_move_fact(fact));
    }
    for fact in output
        .facts
        .borrows
        .iter()
        .filter(|fact| fact.node == Some(node))
    {
        details.push(render_loan_fact(fact));
    }
    for fact in output
        .facts
        .assignments
        .iter()
        .filter(|fact| fact.node == Some(node))
    {
        details.push(format!("assigns {}", render_key_path(&fact.target)));
    }
    for fact in output
        .facts
        .candidate_drops
        .iter()
        .filter(|fact| fact.node == Some(node))
    {
        details.push(format!(
            "drop candidate: {} ({:?})",
            render_key_path(&fact.target),
            fact.reason
        ));
    }
    for obligation in output
        .drop_plan
        .obligations
        .iter()
        .filter(|obligation| obligation.node == Some(node))
    {
        details.push(render_drop_obligation(obligation));
    }
    details
}

fn render_move_fact(fact: &MoveFact) -> String {
    format!(
        "moves {}: {}",
        render_key_path(&fact.source),
        fact.ty.render_mono()
    )
}

fn render_loan_fact(fact: &LoanFact) -> String {
    let owner = fact
        .owner
        .as_ref()
        .map(render_key_path)
        .unwrap_or_else(|| "unknown owner".to_string());
    format!(
        "creates {} borrow {} from {}",
        borrow_kind_name(fact.kind),
        render_key_path(&fact.borrower),
        owner
    )
}

fn render_loan_tooltip(fact: &LoanFact) -> String {
    let owner = fact
        .owner
        .as_ref()
        .map(render_key_path)
        .unwrap_or_else(|| "unknown owner".to_string());
    format!(
        "Creates a {} borrow of {} as {}",
        borrow_kind_name(fact.kind),
        owner,
        render_key_path(&fact.borrower)
    )
}

fn render_drop_obligation(obligation: &DropObligation) -> String {
    format!(
        "drop: {} as {:?} ({:?})",
        render_key_path(&obligation.key_path),
        obligation.kind,
        obligation.reason
    )
}

fn render_drop_tooltip(obligation: &DropObligation) -> String {
    format!(
        "Drop {} of type {} ({:?}, {:?})",
        render_key_path(&obligation.key_path),
        obligation.ty.render_mono(),
        obligation.kind,
        obligation.reason
    )
}

fn borrow_prefix(kind: BorrowKind) -> &'static str {
    match kind {
        BorrowKind::Shared => "&",
        BorrowKind::Mutable => "&mut",
    }
}

fn borrow_kind_name(kind: BorrowKind) -> &'static str {
    match kind {
        BorrowKind::Shared => "shared",
        BorrowKind::Mutable => "mutable",
    }
}

fn render_key_path(key_path: &KeyPath) -> String {
    let mut out = render_symbol(key_path.root);
    for field in &key_path.fields {
        out.push('.');
        out.push_str(&render_symbol(*field));
    }
    out
}

fn render_symbol(symbol: Symbol) -> String {
    symbol.to_string()
}

fn dedup(items: Vec<String>) -> Vec<String> {
    let mut seen = FxHashSet::default();
    let mut result = Vec::new();
    for item in items {
        if seen.insert(item.clone()) {
            result.push(item);
        }
    }
    result
}

fn dedup_hints(hints: Vec<OwnershipInlayHint>) -> Vec<OwnershipInlayHint> {
    let mut seen = FxHashSet::default();
    let mut result = Vec::new();
    for hint in hints {
        let key = (hint.position, hint.label.clone(), hint.tooltip.clone());
        if seen.insert(key) {
            result.push(hint);
        }
    }
    result.sort_by_key(|hint| (hint.position, hint.label.clone()));
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::DocumentInput;

    fn workspace(source: &str) -> Workspace {
        let doc = DocumentInput {
            id: "<test>".to_string(),
            path: "test.tlk".to_string(),
            version: 0,
            text: source.to_string(),
        };
        Workspace::new(vec![doc]).expect("workspace")
    }

    #[test]
    fn inlay_hints_include_borrows_moves_and_drops() {
        let source = "func f() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet b: &String = s\n\tlet t = s\n\t0\n}\nf()";
        let workspace = workspace(source);
        assert!(
            workspace
                .diagnostics
                .get("<test>")
                .map(Vec::is_empty)
                .unwrap_or(true),
            "unexpected diagnostics: {:?}",
            workspace.diagnostics
        );

        let hints = ownership_inlay_hints(
            &workspace,
            &"<test>".to_string(),
            TextRange::new(0, source.len() as u32),
        );
        let labels: Vec<_> = hints.iter().map(|hint| hint.label.as_str()).collect();
        assert!(labels.iter().any(|label| label.contains("&")), "{hints:?}");
        assert!(
            labels.iter().any(|label| label.contains("move")),
            "{hints:?}"
        );
        assert!(
            labels.iter().any(|label| label.contains("drop")),
            "{hints:?}"
        );
    }

    #[test]
    fn hover_details_include_owned_classification() {
        let source = "let s = \"a\" + \"b\"\ns.length";
        let workspace = workspace(source);
        let offset = source.find("s.length").expect("s use") as u32;
        let hover =
            crate::analysis::hover_at(&workspace, &"<test>".to_string(), offset).expect("hover");
        assert!(
            hover.contents.contains("ownership:") && hover.contents.contains("owned"),
            "{}",
            hover.contents
        );
    }
}
