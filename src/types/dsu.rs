use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct DSU<Id: Copy + Eq + std::hash::Hash + Ord> {
    parent: FxHashMap<Id, Id>,
}

impl<Id> std::fmt::Debug for DSU<Id>
where
    Id: Copy + Eq + std::hash::Hash + Ord + std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // build reverse map: rep -> {members}
        let mut classes: FxHashMap<Id, Vec<Id>> = FxHashMap::default();
        let mut tmp = self.clone(); // so we can call find
        for &id in self.parent.keys() {
            let rep = tmp.find(id);
            classes.entry(rep).or_default().push(id);
        }
        f.debug_map()
            .entries(classes.into_iter().map(|(rep, mut members)| {
                members.sort();
                (rep, members)
            }))
            .finish()
    }
}

impl<Id: Copy + Eq + std::hash::Hash + Ord> Default for DSU<Id> {
    fn default() -> Self {
        Self {
            parent: Default::default(),
        }
    }
}

impl<Id: Copy + Eq + std::hash::Hash + Ord> DSU<Id> {
    pub fn find(&mut self, x: Id) -> Id {
        let p = *self.parent.entry(x).or_insert(x);
        if p == x {
            x
        } else {
            let r = self.find(p);
            self.parent.insert(x, r);
            r
        }
    }

    pub fn union(&mut self, a: Id, b: Id) -> Id {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return ra;
        }
        if ra > rb {
            std::mem::swap(&mut ra, &mut rb);
        } // keep min
        self.parent.insert(rb, ra);
        ra
    }
}
