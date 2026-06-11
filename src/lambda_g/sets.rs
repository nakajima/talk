//! Hash-consed, ordered label sets — the small-set representation of Leißa
//! & Griebler §5.1: immutable sorted arrays, interned globally, so equality
//! and sharing are pointer (id) comparisons and copying is an id copy. The
//! indexed trie of §5.3 (splay/link-cut: Sleator & Tarjan 1983/1985) is the
//! documented scaling path if set sizes ever warrant it; the paper found
//! ordered arrays fastest below ~16 elements, which covers free-variable
//! sets in real programs.

use rustc_hash::FxHashMap;

use crate::lambda_g::program::Label;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SetId(pub u32);

impl SetId {
    pub const EMPTY: SetId = SetId(0);
}

#[derive(Default, Debug)]
pub struct SetArena {
    sets: Vec<Box<[Label]>>,
    intern: FxHashMap<Box<[Label]>, SetId>,
}

impl SetArena {
    pub fn new() -> Self {
        let mut arena = SetArena {
            sets: vec![],
            intern: FxHashMap::default(),
        };
        let empty: Box<[Label]> = Box::new([]);
        arena.sets.push(empty.clone());
        arena.intern.insert(empty, SetId::EMPTY);
        arena
    }

    fn intern(&mut self, sorted: Vec<Label>) -> SetId {
        debug_assert!(sorted.windows(2).all(|w| w[0] < w[1]), "sorted + deduped");
        let boxed: Box<[Label]> = sorted.into_boxed_slice();
        if let Some(&id) = self.intern.get(&boxed) {
            return id;
        }
        let id = SetId(self.sets.len() as u32);
        self.sets.push(boxed.clone());
        self.intern.insert(boxed, id);
        id
    }

    pub fn labels(&self, id: SetId) -> &[Label] {
        &self.sets[id.0 as usize]
    }

    pub fn singleton(&mut self, label: Label) -> SetId {
        self.intern(vec![label])
    }

    /// Linear-time ordered merge (§5.1).
    pub fn union(&mut self, a: SetId, b: SetId) -> SetId {
        if a == b || b == SetId::EMPTY {
            return a;
        }
        if a == SetId::EMPTY {
            return b;
        }
        let (xs, ys) = (&self.sets[a.0 as usize], &self.sets[b.0 as usize]);
        let mut merged = Vec::with_capacity(xs.len() + ys.len());
        let (mut i, mut j) = (0, 0);
        while i < xs.len() && j < ys.len() {
            match xs[i].cmp(&ys[j]) {
                std::cmp::Ordering::Less => {
                    merged.push(xs[i]);
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    merged.push(ys[j]);
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    merged.push(xs[i]);
                    i += 1;
                    j += 1;
                }
            }
        }
        merged.extend_from_slice(&xs[i..]);
        merged.extend_from_slice(&ys[j..]);
        self.intern(merged)
    }

    pub fn remove(&mut self, a: SetId, label: Label) -> SetId {
        if !self.contains(a, label) {
            return a;
        }
        let remaining: Vec<Label> = self.sets[a.0 as usize]
            .iter()
            .copied()
            .filter(|l| *l != label)
            .collect();
        self.intern(remaining)
    }

    pub fn contains(&self, a: SetId, label: Label) -> bool {
        self.sets[a.0 as usize].binary_search(&label).is_ok()
    }

    /// Simultaneous ordered traversal, stopping at the first shared element
    /// (§5.1's intersection test).
    pub fn intersects(&self, a: SetId, b: SetId) -> bool {
        if a == SetId::EMPTY || b == SetId::EMPTY {
            return false;
        }
        let (xs, ys) = (&self.sets[a.0 as usize], &self.sets[b.0 as usize]);
        let (mut i, mut j) = (0, 0);
        while i < xs.len() && j < ys.len() {
            match xs[i].cmp(&ys[j]) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Equal => return true,
            }
        }
        false
    }
}
