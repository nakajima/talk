//! Editor-facing ownership facts. This module keeps LSP protocol types out
//! of the analysis layer: callers get byte offsets, rendered labels, and
//! tooltips derived from the flow checker's facts (`FlowFacts`) and the type
//! catalog.

use rustc_hash::FxHashSet;

use crate::analysis::{DocumentId, TextRange, workspace::Workspace};
use crate::flow::drops::DropElaboration;
use crate::flow::{FlowBorrowFact, FlowCloneFact, FlowDropFact, FlowMoveFact};
use crate::name_resolution::symbol::set_symbol_names;
use crate::node_id::NodeID;
use crate::types::ty::{Perm, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipInlayHintKind {
    Move,
    Borrow,
    Drop,
    Clone,
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
        details.extend(type_details(workspace, ty));
    }
    details.extend(fact_details_for_node(workspace, node));
    dedup(details)
}

pub fn ownership_inlay_hints(
    workspace: &Workspace,
    document_id: &DocumentId,
    range: TextRange,
) -> Vec<OwnershipInlayHint> {
    let _names = set_symbol_names(workspace.types.display_names.clone());
    let mut hints = Vec::new();

    for fact in &workspace.flow.moves {
        let Some(position) = fact_position(workspace, document_id, range, fact.node) else {
            continue;
        };
        hints.push(OwnershipInlayHint {
            position,
            label: " move".to_string(),
            tooltip: render_move_tooltip(fact),
            kind: OwnershipInlayHintKind::Move,
        });
    }

    for fact in &workspace.flow.borrows {
        let Some(position) = fact_position(workspace, document_id, range, fact.node) else {
            continue;
        };
        let label = if fact.exclusive { " &mut" } else { " &" };
        hints.push(OwnershipInlayHint {
            position,
            label: label.to_string(),
            tooltip: render_borrow_tooltip(fact),
            kind: OwnershipInlayHintKind::Borrow,
        });
    }

    for fact in &workspace.flow.clones {
        let Some(position) = fact_position(workspace, document_id, range, fact.node) else {
            continue;
        };
        hints.push(OwnershipInlayHint {
            position,
            label: " clone".to_string(),
            tooltip: render_clone_tooltip(fact),
            kind: OwnershipInlayHintKind::Clone,
        });
    }

    for fact in &workspace.flow.drops {
        let Some(position) = fact_position(workspace, document_id, range, fact.node) else {
            continue;
        };
        let label = match fact.kind {
            DropElaboration::Static => " drop",
            DropElaboration::Dead => " drop(dead)",
            DropElaboration::Conditional => " drop?",
            DropElaboration::Open => " drop(open)",
        };
        hints.push(OwnershipInlayHint {
            position,
            label: label.to_string(),
            tooltip: render_drop_tooltip(fact),
            kind: OwnershipInlayHintKind::Drop,
        });
    }

    dedup_hints(hints)
}

fn fact_position(
    workspace: &Workspace,
    document_id: &DocumentId,
    requested: TextRange,
    node: NodeID,
) -> Option<u32> {
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

/// Type-level ownership classifications, from the catalog: borrow kinds,
/// the `Borrowed` marker, needs-drop ("owned"), and copyability.
fn type_details(workspace: &Workspace, ty: &Ty) -> Vec<String> {
    let grades = crate::flow::grades::GradeView::new(&workspace.types);
    let mut details = Vec::new();
    match ty {
        Ty::Borrow(kind, inner) => {
            details.push(format!(
                "{} borrow of {}",
                perm_name(*kind),
                inner.render_mono()
            ));
        }
        Ty::Nominal(symbol, _) => {
            // Classify declared nominals only (scalars hover bare, matching
            // the legacy fact sets, which held struct/enum symbols).
            let declared = workspace.types.catalog.structs.contains_key(symbol)
                || workspace.types.catalog.enums.contains_key(symbol);
            if declared {
                if grades.is_object(ty) {
                    details.push("heap — reference semantics, region-allocated".to_string());
                } else if grades.is_borrowed_value(ty) {
                    details.push("borrowed view".to_string());
                } else if workspace.types.catalog.grade_of(*symbol)
                    == crate::types::catalog::Grade::Linear
                {
                    details.push("linear (must be consumed)".to_string());
                } else if grades.needs_drop(ty) {
                    details.push("owned".to_string());
                }
                if grades.is_copy(ty) && !grades.is_object(ty) {
                    details.push("copy".to_string());
                }
                if grades.is_cheap_clone(ty) {
                    details.push("cheap to clone (buffer retain)".to_string());
                }
            }
        }
        _ => {}
    }
    if grades.needs_drop(ty) {
        details.push("needs drop".to_string());
    }
    details
}

fn fact_details_for_node(workspace: &Workspace, node: NodeID) -> Vec<String> {
    let mut details = Vec::new();
    for fact in workspace.flow.moves.iter().filter(|fact| fact.node == node) {
        details.push(format!("moves {}: {}", fact.place, fact.ty));
    }
    for fact in workspace
        .flow
        .borrows
        .iter()
        .filter(|fact| fact.node == node)
    {
        details.push(render_borrow_tooltip(fact));
    }
    for fact in workspace
        .flow
        .clones
        .iter()
        .filter(|fact| fact.node == node)
    {
        details.push(render_clone_tooltip(fact));
    }
    for fact in workspace.flow.drops.iter().filter(|fact| fact.node == node) {
        details.push(format!(
            "drop: {} as {:?} ({:?})",
            fact.place, fact.kind, fact.reason
        ));
    }
    details
}

fn render_move_tooltip(fact: &FlowMoveFact) -> String {
    format!("Moves {} of type {}", fact.place, fact.ty)
}

fn render_clone_tooltip(fact: &FlowCloneFact) -> String {
    format!("Clones {} (an O(1) buffer retain)", fact.ty)
}

fn render_borrow_tooltip(fact: &FlowBorrowFact) -> String {
    format!(
        "Creates a {} borrow of {} as {}",
        if fact.exclusive { "mutable" } else { "shared" },
        fact.owner,
        fact.borrower
    )
}

fn render_drop_tooltip(fact: &FlowDropFact) -> String {
    format!(
        "Drop {} of type {} ({:?}, {:?})",
        fact.place, fact.ty, fact.kind, fact.reason
    )
}

fn perm_name(kind: Perm) -> &'static str {
    if kind.is_exclusive() {
        "mutable"
    } else {
        "shared"
    }
}

fn dedup(details: Vec<String>) -> Vec<String> {
    let mut seen = FxHashSet::default();
    details
        .into_iter()
        .filter(|detail| seen.insert(detail.clone()))
        .collect()
}

fn dedup_hints(hints: Vec<OwnershipInlayHint>) -> Vec<OwnershipInlayHint> {
    let mut seen = FxHashSet::default();
    let mut out: Vec<OwnershipInlayHint> = hints
        .into_iter()
        .filter(|hint| seen.insert((hint.position, hint.label.clone())))
        .collect();
    out.sort_by_key(|hint| hint.position);
    out
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
    fn inlay_hints_include_silent_clones() {
        let source = "struct Person {\n\tlet name: String\n}\nfunc f(person: &Person) -> String {\n\tperson.name\n}\nlet p = Person(name: \"a\" + \"b\")\nf(p).length";
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
        assert!(
            hints.iter().any(|hint| hint.label.contains("clone")),
            "a silent CheapClone extraction should surface as a hint: {hints:?}"
        );
    }

    #[test]
    fn hover_details_include_linear_classification() {
        let source = "struct Token 'linear {\n\tlet id: Int\n\tconsuming func close() -> Int {\n\t\tself.id\n\t}\n}\nfunc make() -> Int {\n\tlet token = Token(id: 1)\n\ttoken.close()\n}\nmake()";
        let workspace = workspace(source);
        let offset = source.find("token.close").expect("token use") as u32;
        let hover =
            crate::analysis::hover_at(&workspace, &"<test>".to_string(), offset).expect("hover");
        assert!(hover.contents.contains("linear"), "{}", hover.contents);
    }

    #[test]
    fn hover_details_include_heap_classification() {
        let source = "struct Node 'heap {\n\tlet value: Int\n}\nfunc read(n: Node) -> Int {\n\tn.value\n}\nlet n = Node(value: 1)\nread(n)";
        let workspace = workspace(source);
        let offset = source.rfind("read(n)").expect("use") as u32 + "read(".len() as u32;
        let hover =
            crate::analysis::hover_at(&workspace, &"<test>".to_string(), offset).expect("hover");
        assert!(hover.contents.contains("heap"), "{}", hover.contents);
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
        assert!(
            hover.contents.contains("cheap to clone"),
            "String is CheapClone: {}",
            hover.contents
        );
    }
}
