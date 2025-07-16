//! ascii_dump.rs — no Graphviz, no colours, no excuses.
//!
//!  • Every *event* (Create / Instantiated / Unify) is printed in log order.
//!  • After the log we print the **equivalence classes** that remain once all
//!    Unify edges have been processed.
//!  • For every `TypeVar` we try to append the first line of its source snippet
//!    (useful when you’re staring at 40 nearly‑identical placeholders).
//!
//! Compile‑time requirements on the surrounding crate:
//!   * `Ty: Clone + Eq + Hash + Debug`
//!   * `TypeVarID: Copy + Eq + Hash + Debug`
//!   * `Span { start: usize, end: usize }` points into a `&str`
//!
//! Nothing here allocates megabytes or uses unsafe.

use std::collections::{BTreeMap, HashMap};

use crate::{ExprMetaStorage, ty::Ty, type_var_context::UnificationEntry, type_var_id::TypeVarID};

/* ---------- tiny union–find ---------- */

#[derive(Default)]
struct UF {
    parent: Vec<usize>,
}
impl UF {
    fn make(&mut self) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        id
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            let p = self.parent[x];
            self.parent[x] = self.parent[p];
            x = p;
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            if ra < rb {
                self.parent[rb] = ra;
            } else {
                self.parent[ra] = rb;
            }
        }
    }
}

/* ---------- public API ---------- */

/// Returns a ready‑to‑print ASCII string.
pub fn dump_unification_ascii(
    log: &[UnificationEntry],
    span_of_var: &ExprMetaStorage,
    src: &str,
) -> String {
    // Stable numeric handle for every Ty (needed by union–find)
    let mut handles = HashMap::<Ty, usize>::new();
    let mut uf = UF::default();
    let next_handle = |ty: &Ty, handles: &mut HashMap<Ty, usize>, uf: &mut UF| -> usize {
        *handles.entry(ty.clone()).or_insert_with(|| uf.make())
    };

    // The output we are building
    let mut out = String::new();

    /* ---------------- phase 1: dump the event list, build UF ---------------- */

    for (step, ev) in log.iter().enumerate() {
        match ev {
            UnificationEntry::Create {
                expr_id,
                ty,
                generation,
            } => {
                let _ = next_handle(ty, &mut handles, &mut uf);
                out.push_str(&format!(
                    "[{:04}] create      e{}  g{} : {}\n",
                    step,
                    expr_id.0,
                    generation,
                    fmt_ty(ty, span_of_var, src)
                ));
            }

            UnificationEntry::Instantiated {
                expr_id,
                canonical,
                instantiated,
                generation,
            } => {
                let _ = next_handle(&Ty::TypeVar(canonical.clone()), &mut handles, &mut uf);
                let _ = next_handle(instantiated, &mut handles, &mut uf);

                out.push_str(&format!(
                    "[{:04}] instantiate e{}  g{} : {}  ==>  {}\n",
                    step,
                    expr_id.0,
                    generation,
                    fmt_ty(&Ty::TypeVar(canonical.clone()), span_of_var, src),
                    fmt_ty(instantiated, span_of_var, src),
                ));
            }

            UnificationEntry::Unify {
                expr_id,
                before,
                after,
                generation,
            } => {
                let h_before = next_handle(before, &mut handles, &mut uf);
                let h_after = next_handle(after, &mut handles, &mut uf);

                out.push_str(&format!(
                    "[{:04}] unify       e{}  g{} : {}  ->  {}\n",
                    step,
                    expr_id.0,
                    generation,
                    fmt_ty(before, span_of_var, src),
                    fmt_ty(after, span_of_var, src),
                ));

                uf.union(h_before, h_after);
            }
        }
    }

    /* ---------------- phase 2: dump equivalence classes ---------------- */

    // Collect members per root; BTreeMap gives deterministic ordering.
    let mut classes: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    for (ty, &h) in &handles {
        classes.entry(uf.find(h)).or_default().push(ty);
    }

    out.push_str("\n=== equivalence classes ===\n");
    for (i, (_root, members)) in classes.into_iter().enumerate() {
        out.push_str(&format!("class #{:02}:\n", i));
        for ty in members {
            out.push_str(&format!("    {}\n", fmt_ty(ty, span_of_var, src)));
        }
        out.push('\n');
    }

    out
}

/* ---------- helpers ---------- */

/// Span into the source file (byte offsets).
#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// Pretty‑print Ty, optionally adding a snippet comment.
fn fmt_ty(ty: &Ty, span_of_var: &ExprMetaStorage, src: &str) -> String {
    match ty {
        Ty::TypeVar(id) => {
            if let Some(span) = span_of_var.get(&id.expr_id) {
                let snippet = span.excerpt(format!("{id:?}"), &src.to_string());
                let first_line = snippet.lines().next().unwrap_or("").trim();
                if first_line.is_empty() {
                    format!("{:?}", ty)
                } else {
                    format!("{:?} /* {} */", ty, truncate(first_line, 40))
                }
            } else {
                format!("{:?}", ty)
            }
        }
        _ => format!("{:?}", ty),
    }
}

/// Cut overly long snippets.
fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_owned()
    } else {
        format!("{}…", &s[..max - 1])
    }
}
