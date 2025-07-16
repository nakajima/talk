//! dumb_dot.rs
//! ---------------------------------------
//! Requirements on the surrounding crate:
//!
//! Usage (inside a test or debug build):
//!
//!     dump_unification_dot(&log, "unification.dot").unwrap();
//!     // then: dot -Tpng unification.dot -o unification.png
//!

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::ty::Ty;
use crate::type_var_context::UnificationEntry;

/// ------------------------------------------------------------
///  Tiny union–find – *only* for visualising final representatives
/// ------------------------------------------------------------
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
            // deterministic parent: smaller handle wins
            if ra < rb {
                self.parent[rb] = ra;
            } else {
                self.parent[ra] = rb;
            }
        }
    }
}

/// ------------------------------------------------------------
///  Public API – call from your failing test
/// ------------------------------------------------------------
pub fn dump_unification_dot<P>(log: &[UnificationEntry], out_path: P) -> std::io::Result<()>
where
    P: AsRef<Path>,
{
    // 1.  Map every distinct Ty to a numeric handle.
    let mut handles = HashMap::<Ty, usize>::new();
    let mut uf = UF::default();

    let mut handle_of = |ty: &Ty, handles: &mut HashMap<Ty, usize>, uf: &mut UF| -> usize {
        if let Some(&h) = handles.get(ty) {
            h
        } else {
            let h = uf.make();
            handles.insert(ty.clone(), h);
            h
        }
    };

    // 2.  Collect DOT edges.
    struct Edge {
        from: usize,
        to: usize,
        label: String,
    }
    let mut edges = Vec::<Edge>::new();

    for (step, event) in log.iter().enumerate() {
        match event {
            UnificationEntry::Create {
                ty, // just ensure node exists
                ..
            } => {
                handle_of(ty, &mut handles, &mut uf);
            }
            UnificationEntry::Unify {
                expr_id,
                before,
                after,
                generation,
            } => {
                let h_before = handle_of(before, &mut handles, &mut uf);
                let h_after = handle_of(after, &mut handles, &mut uf);

                edges.push(Edge {
                    from: h_before,
                    to: h_after,
                    label: format!("e{}·g{}·s{}", expr_id.0, generation, step),
                });

                uf.union(h_before, h_after);
            }
        }
    }

    // 3.  Representative lookup
    let mut root_of = HashMap::<usize, usize>::new();
    for &h in handles.values() {
        root_of.insert(h, uf.find(h));
    }

    // 4.  Emit DOT
    let mut w = BufWriter::new(File::create(out_path)?);

    writeln!(w, "digraph Unification {{")?;
    writeln!(w, "    rankdir = LR;")?;
    writeln!(w, "    node [fontname = \"Fira Code\", fontsize = 10];")?;

    // 4.a  Nodes
    for (ty, &h) in &handles {
        let shape = if matches!(ty, Ty::TypeVar(_)) {
            "ellipse"
        } else {
            "box"
        };
        let mut attrs = format!("shape = {}", shape);

        if root_of[&h] == h {
            attrs.push_str(", peripheries = 2"); // double border
        }

        writeln!(
            w,
            "    n{} [label = \"{}\", {}];",
            h,
            dot_escape(&format!("{:?}", ty)),
            attrs
        )?;
    }

    // 4.b  Edges
    for e in edges {
        writeln!(
            w,
            "    n{} -> n{} [label = \"{}\", arrowsize = 0.8];",
            e.from,
            e.to,
            dot_escape(&e.label)
        )?;
    }

    writeln!(w, "}}")?;
    Ok(())
}

/// Escape quotes/backslashes for DOT labels.
fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}
