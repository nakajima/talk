//! dumb_dot.rs – v3  (Create · Instantiated · Unify)
//! -------------------------------------------------
//! Works with the user’s latest `UnificationEntry` enum.
//
//!  · Create        → just makes the node exist
//!  · Instantiated  → blue dashed edge  canonical ──▶ instantiated
//!  · Unify         → solid edge         before    ──▶ after
//!
//!  Render:  dot -Tpng unification.dot -o unification.png
//! -----------------------------------------------------------------

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::ExprMetaStorage;
use crate::ty::Ty;
use crate::type_var_context::UnificationEntry;

/* ───────────────────────── Union–Find (unchanged) ────────────────────────── */

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

/* ───────────────────────────── DOT dumper ────────────────────────────────── */

/// Call this from a test or a failing compilation path.
pub fn dump_unification_dot<P>(
    log: &[UnificationEntry],
    out: P,
    meta: &ExprMetaStorage,
    source: &str,
) -> std::io::Result<()>
where
    P: AsRef<Path>,
{
    /* 1. Assign a numeric handle to every distinct Ty. */
    let mut handles = HashMap::<Ty, (usize, String)>::new();
    let mut uf = UF::default();

    let h_of = |ty: &Ty,
                label: String,
                handles: &mut HashMap<Ty, (usize, String)>,
                uf: &mut UF|
     -> usize {
        if let Some((h, _label)) = handles.get(ty) {
            *h
        } else {
            let h = uf.make();
            handles.insert(ty.clone(), (h, label));
            h
        }
    };

    /* 2. Collect edges with per‑edge attributes */
    struct Edge {
        from: usize,
        to: usize,
        label: String,
        extra_attrs: String, // e.g. "style=dashed,color=blue"
    }
    let mut edges = Vec::<Edge>::new();

    for ev in log.iter() {
        match ev {
            /* 2.a  Create – node already registered by h_of side‑effect */
            UnificationEntry::Create {
                ty,
                expr_id,
                generation,
            } => {
                let label = if let Some(meta) = meta.get(expr_id) {
                    meta.excerpt(format!("Instantiated\n{ty:?}\n",), source)
                } else {
                    format!("Instantiated {generation:?}")
                };

                h_of(ty, label, &mut handles, &mut uf);
            }

            /* 2.b  Instantiated – dashed blue arrow, *no* union */
            UnificationEntry::Instantiated {
                expr_id,
                canonical,
                instantiated,
                generation,
            } => {
                let label = if let Some(meta) = meta.get(expr_id) {
                    meta.excerpt(format!("Instantiated\n{instantiated:?}",), source)
                } else {
                    format!("Instantiated {generation:?}")
                };

                let canonical_ty = Ty::TypeVar(canonical.clone());
                let h_canon = h_of(&canonical_ty, label.clone(), &mut handles, &mut uf);
                let h_inst = h_of(instantiated, label.clone(), &mut handles, &mut uf);

                edges.push(Edge {
                    from: h_canon,
                    to: h_inst,
                    label: dot_escape(&label),
                    extra_attrs: "style=dashed,color=blue".into(),
                });
                //  ⸺ no uf.union() – instantiation is *not* equality
            }

            /* 2.c  Unify – solid arrow + union‑find merge */
            UnificationEntry::Unify {
                expr_id,
                before,
                after,
                generation,
            } => {
                let label = if let Some(meta) = meta.get(expr_id) {
                    meta.excerpt(format!("Unified {before:?}",), source)
                } else {
                    format!("Unified {generation:?}")
                };

                let h_before = h_of(before, label.clone(), &mut handles, &mut uf);
                let h_after = h_of(after, label.clone(), &mut handles, &mut uf);

                edges.push(Edge {
                    from: h_before,
                    to: h_after,
                    label: dot_escape(&label),
                    extra_attrs: String::new(),
                });
                uf.union(h_before, h_after);
            }
        }
    }

    /* 3.  What is the final representative for each handle? */
    let mut root_of = HashMap::<usize, (usize, String)>::new();
    for (h, label) in handles.values() {
        root_of.insert(*h, (uf.find(*h), label.clone()));
    }

    /* 4.  Emit DOT */
    let mut w = BufWriter::new(File::create(out)?);
    writeln!(w, "digraph Unification {{")?;
    writeln!(
        w,
        "    rankdir=LR; node[fontname=\"Fira Code\",fontsize=10];"
    )?;

    /* 4.a  Nodes (double border for roots) */
    for (ty, (h, label)) in &handles {
        let shape = if matches!(ty, Ty::TypeVar(_)) {
            "ellipse"
        } else {
            "box"
        };
        let periph = if root_of.get(h).map(|h| h.0) == Some(*h) {
            "peripheries=2,"
        } else {
            ""
        };
        writeln!(
            w,
            "    n{h} [label=\"{}\", {}shape={shape}];",
            dot_escape(&format!("{label:?}\n{ty:?}")),
            periph
        )?;
    }

    /* 4.b  Edges */
    for e in edges {
        let extras = if e.extra_attrs.is_empty() {
            String::new()
        } else {
            format!(",{}", e.extra_attrs)
        };
        writeln!(
            w,
            "    n{} -> n{} [label=\"{}\"{extras}];",
            e.from,
            e.to,
            dot_escape(&e.label)
        )?;
    }

    writeln!(w, "}}")?;
    Ok(())
}

/* 5.  Helper – escape quotes/backslashes so DOT stays valid */
fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('\"', "\\\"")
}
