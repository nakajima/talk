//! Aggregate layout (ADR 0045): MIR computes, per aggregate type, a total
//! width, per-field offsets, and an inline/boxed classification. Backends
//! read these facts; they do not infer them.
//!
//! Widths and offsets are in abstract slot units — one slot holds one
//! scalar or one reference. Slot-to-byte mapping is a target detail.
//!
//! Classification is deterministic and declaration-level: whether a
//! nominal is recursive is decided on the graph of nominal mentions in
//! declared field and payload types (ADR 0045 rule 2 — "a property of the
//! declaration, not of a site"), so the answer cannot depend on query
//! order. Recursion also cannot diverge the computation: a cyclic nominal
//! is a one-slot reference wherever it appears, so expansion never
//! re-enters it — which covers non-uniform recursion like
//! `struct A<T> { x: A<Pair<T>> }` as well.

use rustc_hash::FxHashMap;

use super::visit::{Slot, visit_inst};
use super::{
    Function, Inst, LocalId, Operand, Term, executable as executable_identity,
    mir_inline_array,
};
use crate::name_resolution::symbol::Symbol;
use crate::types::catalog::{Enum, StructInfo, TypeCatalog};
use crate::types::ty::{StaticValue, Ty};

/// The boxing threshold, in slots (ADR 0045 rule 3): a finite aggregate
/// wider than this is boxed, because copying it by value costs more than
/// an indirection. A tuning constant consulted only by this classifier;
/// typing never reads it, which is what keeps it unobservable.
pub(crate) const INLINE_WIDTH_LIMIT: u32 = 4;

pub(crate) use talk_mir::layout::{FieldRepr, Layout, LayoutId, ParamRepr, Shape, SlotKind};

/// The layout table: computes and caches one layout per type against the
/// program's nominal declarations.
pub(crate) struct Layouts<'a> {
    structs: FxHashMap<Symbol, &'a StructInfo>,
    enums: FxHashMap<Symbol, &'a Enum>,
    /// The merged conformance table: instantiated field types can carry
    /// associated-type projections (`T.Item` under `T := Concrete`), and
    /// classification needs them reduced.
    catalog: TypeCatalog,
    cache: FxHashMap<Ty, Layout>,
    cyclic: FxHashMap<Symbol, bool>,
    /// Per-declaration parameter expandability, shared with the
    /// checker's recursion rule (`types::catalog::expandable_params`) —
    /// the two must agree exactly.
    expands: FxHashMap<Symbol, Vec<bool>>,
    /// Distinct layouts in first-interned order; `LayoutId` indexes here.
    interned: indexmap::IndexSet<Layout>,
}

impl<'a> Layouts<'a> {
    pub(crate) fn new(
        structs: FxHashMap<Symbol, &'a StructInfo>,
        enums: FxHashMap<Symbol, &'a Enum>,
        catalog: TypeCatalog,
    ) -> Self {
        let expands = crate::types::catalog::expandable_params(&structs, &enums);
        Layouts {
            structs,
            enums,
            catalog,
            cache: FxHashMap::default(),
            cyclic: FxHashMap::default(),
            expands,
            interned: indexmap::IndexSet::new(),
        }
    }

    /// Whether an interned layout is shaped (owns member placement) —
    /// the boundary between offset-addressed and logical member access
    /// (ADR 0046).
    pub(crate) fn is_shaped(&self, layout: LayoutId) -> bool {
        matches!(
            self.interned.get_index(usize::try_from(layout).unwrap_or(usize::MAX)),
            Some(Layout::Inline(_, _) | Layout::Boxed(_, _))
        )
    }

    /// A member's slot placement in an interned layout; see
    /// [`field_site`].
    pub(crate) fn site(
        &self,
        layout: LayoutId,
        index: u16,
        of_variant: Option<u16>,
    ) -> Option<(u16, Option<LayoutId>)> {
        match self.interned.get_index(usize::try_from(layout).ok()?)? {
            Layout::Inline(_, shape) | Layout::Boxed(_, shape) => {
                shape_site(shape, index, of_variant)
            }
            Layout::Slot | Layout::Opaque => None,
        }
    }

    /// Intern the layout of a type and return its table id.
    pub(crate) fn id_of(&mut self, ty: &Ty) -> LayoutId {
        let layout = self.of(ty);
        let (index, _) = self.interned.insert_full(layout);
        u32::try_from(index).unwrap_or_default()
    }

    /// The shaped layout governing a value's construction and field
    /// access, interned under the given display identity.
    ///
    /// This differs from the embedding view (`id_of`) in two ways. A
    /// `'heap` enum embeds as one reference slot, but the value built and
    /// read through that reference still has its sum shape — construction
    /// and payload reads need it. And identity comes from the site's
    /// declaration rather than the type: an `InlineArray` built by a
    /// `Record` instruction keeps its symbol even though the type-level
    /// layout is anonymous, so a rendered value displays what the program
    /// declared. Interning is identity-separated, so both views coexist
    /// in the table and agree on every offset.
    pub(crate) fn shaped_id(&mut self, ty: &Ty, identity: Option<Symbol>) -> LayoutId {
        let identity = identity.map(executable_identity);
        let layout = match self.shaped(ty) {
            Layout::Inline(_, shape) => Layout::Inline(identity, shape),
            Layout::Boxed(_, shape) => Layout::Boxed(identity, shape),
            other => other,
        };
        let (index, _) = self.interned.insert_full(layout);
        u32::try_from(index).unwrap_or_default()
    }

    /// The layout for field access on a value of this type: the site's
    /// own identity is the type's nominal.
    pub(crate) fn container_id(&mut self, ty: &Ty) -> LayoutId {
        let ty = peel(ty);
        let identity = match ty {
            Ty::Nominal(symbol, _) => Some(*symbol),
            _ => None,
        };
        self.shaped_id(ty, identity)
    }

    /// The shape view of a type: like `of`, except a `'heap` enum
    /// produces its boxed sum shape instead of the one-slot reference
    /// its embedding uses.
    fn shaped(&mut self, ty: &Ty) -> Layout {
        let ty = peel(ty);
        if let Ty::Nominal(symbol, args) = ty
            && let Some(def) = self.enums.get(symbol).copied()
            && def.heap
        {
            let symbol = *symbol;
            let mut payloads = Vec::with_capacity(def.variants.len());
            for variant in def.variants.values() {
                let declared: Vec<&Ty> = match &variant.constructor_scheme.ty {
                    Ty::Func(params, _, _) => params.iter().collect(),
                    _ => Vec::new(),
                };
                payloads.push(instantiate(&def.params, args, declared.into_iter()));
            }
            return match self.sum_shape(&payloads) {
                Some(shape) => Layout::Boxed(Some(executable_identity(symbol)), shape),
                None => Layout::Opaque,
            };
        }
        self.of(ty)
    }

    /// The interned table in id order, for publication on the program.
    pub(crate) fn table(&self) -> Vec<Layout> {
        self.interned.iter().cloned().collect()
    }

    pub(crate) fn of(&mut self, ty: &Ty) -> Layout {
        if let Some(known) = self.cache.get(ty) {
            return known.clone();
        }
        // Instantiated field types can carry ground projections
        // (`T.Item` under `T := Concrete`): classification happens on
        // the reduced form so `Optional<T.Item>` and `Optional<Int>`
        // intern one layout.
        let layout = if super::ty_has_projection(ty) {
            let reduced = self.reduce(ty);
            self.compute(&reduced)
        } else {
            self.compute(ty)
        };
        self.cache.insert(ty.clone(), layout.clone());
        layout
    }

    fn compute(&mut self, ty: &Ty) -> Layout {
        match ty {
            Ty::Unique(inner) => self.of(inner),
            // Typing erases `&T` to `T` for Copy-grade nominals ("the same
            // type up to representation" — they unify in any position), so
            // the two spellings must intern one layout: a borrow of an
            // inline Copy pointee is the same flat value the owned
            // spelling splices, never a one-slot reference. Every other
            // pointee is one slot under both spellings.
            Ty::Borrow(_, inner)
                if matches!(&**inner, Ty::Nominal(symbol, args)
                    if self.catalog.grade_of_application(*symbol, args)
                        == crate::types::catalog::Grade::Copy) =>
            {
                match self.of(inner) {
                    inline @ Layout::Inline(_, _) => inline,
                    _ => Layout::Slot,
                }
            }
            // A borrow is a reference regardless of its pointee's shape.
            Ty::Borrow(_, _) => Layout::Slot,
            Ty::Func(_, _, _) | Ty::Any { .. } => Layout::Slot,
            // A projection that survives reduction is check-only, like a
            // rigid parameter (`of` reduces ground ones first).
            Ty::Param(_) | Ty::Proj(_, _, _) => Layout::Opaque,
            // Inference leftovers, poison, and kind-restricted argument
            // forms are never emitted value types.
            Ty::Var(_) | Ty::Error | Ty::Eff(_) | Ty::Static(_) => Layout::Opaque,
            Ty::Tuple(items) => self.product(items),
            Ty::Record(row) => {
                if row.tail.is_some() {
                    return Layout::Opaque;
                }
                let fields: Vec<Ty> = row.fields.iter().map(|(_, ty)| ty.clone()).collect();
                self.product(&fields)
            }
            Ty::Nominal(symbol, args) => self.nominal(*symbol, args),
        }
    }

    fn nominal(&mut self, symbol: Symbol, args: &[Ty]) -> Layout {
        if symbol == Symbol::InlineArray {
            return self.inline_array(args);
        }
        if let Some(def) = self.structs.get(&symbol) {
            if def.heap {
                return Layout::Slot;
            }
            let fields = instantiate(&def.params, args, def.fields.values().map(|(_, ty)| ty));
            let shape = self.product_shape(&fields);
            return self.aggregate(symbol, shape);
        }
        if let Some(def) = self.enums.get(&symbol) {
            if def.heap {
                return Layout::Slot;
            }
            let mut payloads = Vec::with_capacity(def.variants.len());
            for variant in def.variants.values() {
                let declared: Vec<&Ty> = match &variant.constructor_scheme.ty {
                    Ty::Func(params, _, _) => params.iter().collect(),
                    _ => Vec::new(),
                };
                payloads.push(instantiate(&def.params, args, declared.into_iter()));
            }
            let shape = self.sum_shape(&payloads);
            return self.aggregate(symbol, shape);
        }
        // A nominal without a declaration is a builtin scalar.
        Layout::Slot
    }

    /// Classify a computed aggregate shape: recursion and width force
    /// boxing (rules 2 and 3); everything else is inline.
    fn aggregate(&mut self, symbol: Symbol, shape: Option<Shape>) -> Layout {
        let Some(shape) = shape else {
            return Layout::Opaque;
        };
        if self.is_cyclic(symbol) || shape.width() > INLINE_WIDTH_LIMIT {
            Layout::Boxed(Some(executable_identity(symbol)), shape)
        } else {
            Layout::Inline(Some(executable_identity(symbol)), shape)
        }
    }

    fn product(&mut self, items: &[Ty]) -> Layout {
        match self.product_shape(items) {
            Some(shape) if shape.width() > INLINE_WIDTH_LIMIT => Layout::Boxed(None, shape),
            Some(shape) => Layout::Inline(None, shape),
            None => Layout::Opaque,
        }
    }

    /// One field's slot count, per-slot kinds, and repr. A cyclic nominal
    /// is answered without expansion — it is boxed by rule 2, so it
    /// occupies one reference slot wherever it appears, and this
    /// short-circuit is what keeps recursive shape computation finite.
    fn slot_shape(&mut self, ty: &Ty) -> Option<(u32, Vec<SlotKind>, FieldRepr)> {
        let reduced;
        let ty = if super::ty_has_projection(ty) {
            reduced = self.reduce(ty);
            &reduced
        } else {
            ty
        };
        if let Ty::Nominal(symbol, _) = ty
            && (self.structs.contains_key(symbol) || self.enums.contains_key(symbol))
            && self.is_cyclic(*symbol)
        {
            return Some((1, vec![SlotKind::Value], FieldRepr::Slot(SlotKind::Value)));
        }
        match self.of(ty) {
            Layout::Slot => {
                let kind = scalar_kind(ty);
                Some((1, vec![kind], FieldRepr::Slot(kind)))
            }
            Layout::Inline(_, shape) => Some((
                shape.width(),
                shape.kinds().to_vec(),
                FieldRepr::Spliced(self.id_of(ty)),
            )),
            Layout::Boxed(_, _) => Some((1, vec![SlotKind::Value], FieldRepr::Slot(SlotKind::Value))),
            Layout::Opaque => None,
        }
    }

    /// Field offsets for a product, flattening nested inline aggregates.
    /// `None` when any field is opaque: opacity propagates outward.
    fn product_shape(&mut self, items: &[Ty]) -> Option<Shape> {
        let mut offsets = Vec::with_capacity(items.len());
        let mut reprs = Vec::with_capacity(items.len());
        let mut kinds = Vec::new();
        let mut width = 0u32;
        for item in items {
            offsets.push(width);
            let (slots, item_kinds, repr) = self.slot_shape(item)?;
            width += slots;
            kinds.extend(item_kinds);
            reprs.push(repr);
        }
        Some(Shape::Product {
            width,
            offsets,
            reprs,
            kinds,
        })
    }

    /// Variant payload offsets for a sum: tag at slot 0, each variant's
    /// payloads from slot 1, width fitting the widest variant. Slot kinds
    /// join across variants; disagreement makes a slot a tagged `Value`.
    fn sum_shape(&mut self, variants: &[Vec<Ty>]) -> Option<Shape> {
        let mut payloads = Vec::with_capacity(variants.len());
        let mut reprs = Vec::with_capacity(variants.len());
        let mut kinds: Vec<Option<SlotKind>> = vec![Some(SlotKind::Int)];
        let mut width = 1u32;
        for payload_tys in variants {
            let mut offsets = Vec::with_capacity(payload_tys.len());
            let mut variant_reprs = Vec::with_capacity(payload_tys.len());
            let mut end = 1u32;
            for ty in payload_tys {
                offsets.push(end);
                let (slots, item_kinds, repr) = self.slot_shape(ty)?;
                variant_reprs.push(repr);
                for (index, kind) in item_kinds.into_iter().enumerate() {
                    let slot = usize::try_from(end).unwrap_or(usize::MAX) + index;
                    if kinds.len() <= slot {
                        kinds.resize(slot + 1, None);
                    }
                    kinds[slot] = match kinds[slot] {
                        None => Some(kind),
                        Some(existing) if existing == kind => Some(existing),
                        Some(_) => Some(SlotKind::Value),
                    };
                }
                end += slots;
            }
            width = width.max(end);
            payloads.push(offsets);
            reprs.push(variant_reprs);
        }
        let kinds = kinds
            .into_iter()
            .map(|kind| kind.unwrap_or(SlotKind::Value))
            .collect();
        Some(Shape::Sum {
            width,
            payloads,
            reprs,
            kinds,
        })
    }

    fn inline_array(&mut self, args: &[Ty]) -> Layout {
        let [element, count] = args else {
            return Layout::Opaque;
        };
        let Ty::Static(StaticValue::Int(count)) = count else {
            // A rigid static parameter: check-only, like a type param.
            return Layout::Opaque;
        };
        let Some(count) = count.as_i64().and_then(|count| u32::try_from(count).ok()) else {
            return Layout::Opaque;
        };
        let Some((stride, element_kinds, element_repr)) = self.slot_shape(element) else {
            return Layout::Opaque;
        };
        let offsets: Vec<u32> = (0..count).map(|index| index * stride).collect();
        let reprs: Vec<FieldRepr> = vec![element_repr; usize::try_from(count).unwrap_or_default()];
        let kinds: Vec<SlotKind> = element_kinds
            .iter()
            .copied()
            .cycle()
            .take(usize::try_from(count * stride).unwrap_or_default())
            .collect();
        let shape = Shape::Product {
            width: count * stride,
            offsets,
            reprs,
            kinds,
        };
        // InlineArray keeps its symbol: constructions declare it, and
        // identity must agree between a spliced embedding and the value
        // built into it.
        if shape.width() > INLINE_WIDTH_LIMIT {
            Layout::Boxed(Some(mir_inline_array()), shape)
        } else {
            Layout::Inline(Some(mir_inline_array()), shape)
        }
    }

    /// Reduce associated-type projections at every depth through the
    /// merged conformance table (the classifier twin of the builder's
    /// `resolved`).
    fn reduce(&self, ty: &Ty) -> Ty {
        struct DeepNormalize<'c> {
            catalog: &'c TypeCatalog,
        }
        impl crate::types::ty::TyFold for DeepNormalize<'_> {
            fn fold_ty(&mut self, ty: &Ty) -> Ty {
                let reduced = if matches!(ty, Ty::Proj(_, _, _)) {
                    let mut scratch = crate::types::solve::VarStore::default();
                    crate::types::solve::normalize_ty(&mut scratch, self.catalog, ty)
                } else {
                    ty.clone()
                };
                self.fold_children(&reduced)
            }
        }
        crate::types::ty::TyFold::fold_ty(
            &mut DeepNormalize {
                catalog: &self.catalog,
            },
            ty,
        )
    }

    /// Whether a nominal's declaration reaches itself through inline
    /// positions (ADR 0045 rule 2) — the shared oracle's answer, cached.
    /// One implementation serves this classifier and the checker's
    /// `'heap` requirement: they must agree exactly.
    fn is_cyclic(&mut self, symbol: Symbol) -> bool {
        if let Some(&known) = self.cyclic.get(&symbol) {
            return known;
        }
        let found = crate::types::catalog::is_layout_recursive(
            symbol,
            &self.structs,
            &self.enums,
            &self.expands,
        );
        self.cyclic.insert(symbol, found);
        found
    }
}

/// A member's slot placement in a shape (ADR 0046): its offset from
/// the container's base — a sum payload's offsets already include the
/// tag slot — and the spliced child's layout for an inline-aggregate
/// member, `None` for a one-slot member. The published wire
/// descriptors transcribe exactly this arithmetic, so builder-side and
/// wire offsets cannot drift.
pub(crate) fn shape_site(
    shape: &Shape,
    index: u16,
    of_variant: Option<u16>,
) -> Option<(u16, Option<LayoutId>)> {
    let (offset, repr) = match (shape, of_variant) {
        (Shape::Product { offsets, reprs, .. }, None) => (
            *offsets.get(usize::from(index))?,
            *reprs.get(usize::from(index))?,
        ),
        (Shape::Sum { payloads, reprs, .. }, Some(variant)) => (
            *payloads
                .get(usize::from(variant))?
                .get(usize::from(index))?,
            *reprs.get(usize::from(variant))?.get(usize::from(index))?,
        ),
        _ => return None,
    };
    let offset = u16::try_from(offset).ok()?;
    let member = match repr {
        FieldRepr::Slot(_) => None,
        FieldRepr::Spliced(child) => Some(child),
    };
    Some((offset, member))
}

/// Buffer element stride in bytes: byte elements pack; every other
/// element class is one 8-byte word. The layout module owns all width
/// arithmetic — slots for aggregates, bytes for buffer elements — so a
/// backend never derives a size on its own (ADR 0045 rule 4).
pub(crate) fn element_stride(element: SlotKind) -> u32 {
    match element {
        SlotKind::Byte => 1,
        _ => 8,
    }
}

/// Strip the wrappers that do not change which aggregate is accessed:
/// uniqueness, and borrows (a field read through a borrow reads the
/// pointee's layout).
fn peel(ty: &Ty) -> &Ty {
    match ty {
        Ty::Unique(inner) | Ty::Borrow(_, inner) => peel(inner),
        other => other,
    }
}

/// The native kind of a one-slot value or buffer element: scalars pin
/// their word class; everything else stays a tagged runtime value until
/// its native form is pinned. The one scalar classifier in the backend —
/// ownership wrappers never change a scalar's word class.
pub(crate) fn scalar_kind(ty: &Ty) -> SlotKind {
    match peel(ty) {
        Ty::Nominal(symbol, args) if args.is_empty() => {
            if *symbol == Symbol::Int {
                SlotKind::Int
            } else if *symbol == Symbol::Bool {
                SlotKind::Bool
            } else if *symbol == Symbol::Byte {
                SlotKind::Byte
            } else if *symbol == Symbol::Float {
                SlotKind::F64
            } else if *symbol == Symbol::RawPtr {
                SlotKind::Ptr
            } else {
                SlotKind::Value
            }
        }
        _ => SlotKind::Value,
    }
}

/// Declared types instantiated against a nominal application's type
/// arguments — the same raw-key substitution `field_types` and
/// `variant_payloads` use.
pub(super) fn instantiate<'t>(
    params: &[crate::types::ty::SchemeParam],
    args: &[Ty],
    declared: impl Iterator<Item = &'t Ty>,
) -> Vec<Ty> {
    // Substitution keys stay raw: scheme parameters keep `Ty::Param`
    // symbols as authored (core params are owner-stamped at creation),
    // so a re-stamped key would never match its occurrences.
    let substitution: FxHashMap<Symbol, Ty> = params
        .iter()
        .map(|param| param.symbol)
        .zip(args.iter().cloned())
        .collect();
    declared
        .map(|ty| ty.substitute(&substitution, &FxHashMap::default(), &FxHashMap::default()))
        .collect()
}

/// How one parameter is represented at a call boundary: no published
/// fact (hidden witness parameters, synthesized bodies), an owned value
/// of a known layout, or a borrow of one. A borrow of an inline
/// aggregate may pass its pointee by value: aggregates have pure value
/// semantics (`SetField` copies; parameter mutation returns through the
/// writeback tuple), so a callee can never mutate through the reference.
/// Per-local value layout for one function, derived from its published
/// signature and its instructions: parameters seed their published
/// layout, the destination of an inline-classified construction holds
/// that layout, a direct call's destination holds the callee's return
/// layout, copies and block-parameter edges propagate, and every other
/// definition produces a uniform one-slot value. A local whose
/// definitions disagree degrades to uniform — an emitter must then box
/// the construction sites that feed it.
pub(crate) fn local_layouts(
    function: &Function,
    table: &[Layout],
    returns: &[Option<LayoutId>],
) -> Vec<Option<LayoutId>> {
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        Unknown,
        Inline(LayoutId),
        Uniform,
    }
    fn join(a: State, b: State) -> State {
        match (a, b) {
            (State::Unknown, other) | (other, State::Unknown) => other,
            (State::Inline(left), State::Inline(right)) if left == right => a,
            _ => State::Uniform,
        }
    }
    enum Def {
        Agg(LocalId, LayoutId),
        Propagate(LocalId, LocalId),
        /// A product field read: the destination holds the member's
        /// spliced layout when the field is itself an inline aggregate,
        /// a uniform value otherwise (the member travels on the inst).
        Field(LocalId, LocalId, Option<LayoutId>),
        Uniform(LocalId),
    }
    let native = |layout: LayoutId| {
        matches!(
            table.get(usize::try_from(layout).unwrap_or(usize::MAX)),
            Some(Layout::Inline(_, _))
        )
    };
    let mut defs: Vec<Def> = Vec::new();
    for (local, repr) in function.param_reprs.iter().enumerate() {
        let local = u16::try_from(local).unwrap_or(u16::MAX);
        match repr.layout() {
            Some(layout) if native(layout) => defs.push(Def::Agg(local, layout)),
            _ => defs.push(Def::Uniform(local)),
        }
    }
    for block in &function.blocks {
        for inst in &block.insts {
            match inst {
                Inst::Aggregate { dest, layout, .. } => {
                    defs.push(if native(*layout) {
                        Def::Agg(*dest, *layout)
                    } else {
                        Def::Uniform(*dest)
                    });
                }
                Inst::Call { dest, func, .. } => {
                    match returns.get(*func).copied().flatten() {
                        Some(layout) if native(layout) => defs.push(Def::Agg(*dest, layout)),
                        _ => defs.push(Def::Uniform(*dest)),
                    }
                }
                Inst::Copy {
                    dest,
                    src: Operand::Local(src),
                } => defs.push(Def::Propagate(*dest, *src)),
                Inst::Field {
                    dest,
                    src: Operand::Local(src),
                    member,
                    ..
                } => defs.push(Def::Field(*dest, *src, *member)),
                // A dynamically indexed element read has no static member
                // in a native struct: its source must stay uniform.
                Inst::GetElement {
                    dest,
                    src: Operand::Local(src),
                    ..
                } => {
                    defs.push(Def::Uniform(*src));
                    defs.push(Def::Uniform(*dest));
                }
                other => {
                    let mut probe = other.clone();
                    visit_inst(&mut probe, &mut |slot, local| {
                        if slot == Slot::Def {
                            defs.push(Def::Uniform(*local));
                        }
                    });
                }
            }
        }
        if let Some(Term::Goto(target, args)) = &block.term {
            for (param, arg) in function.blocks[*target].params.iter().zip(args) {
                match arg {
                    Operand::Local(src) => defs.push(Def::Propagate(*param, *src)),
                    _ => defs.push(Def::Uniform(*param)),
                }
            }
        }
    }
    let mut state = vec![State::Unknown; usize::from(function.n_locals())];
    loop {
        let mut changed = false;
        for def in &defs {
            let (local, incoming) = match def {
                Def::Agg(local, layout) => (*local, State::Inline(*layout)),
                Def::Propagate(local, src) => (*local, state[usize::from(*src)]),
                Def::Field(local, src, member) => {
                    let incoming = match state[usize::from(*src)] {
                        State::Unknown => State::Unknown,
                        State::Uniform => State::Uniform,
                        State::Inline(_) => match member {
                            Some(child) if native(*child) => State::Inline(*child),
                            _ => State::Uniform,
                        },
                    };
                    (*local, incoming)
                }
                Def::Uniform(local) => (*local, State::Uniform),
            };
            let joined = join(state[usize::from(local)], incoming);
            if joined != state[usize::from(local)] {
                state[usize::from(local)] = joined;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    state
        .into_iter()
        .map(|state| match state {
            State::Inline(layout) => Some(layout),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use indexmap::IndexMap;

    use super::*;
    use crate::compiling::module::ModuleId;
    use crate::name_resolution::symbol::{StructId, Symbol};
    use crate::types::ty::{
        EffectRow, ParamKind, Row, Scheme, SchemeParam, StaticInt, StaticValue, Ty,
    };

    fn sym(id: u32) -> Symbol {
        Symbol::Struct(StructId::new(ModuleId(9), id))
    }

    fn int() -> Ty {
        Ty::Nominal(Symbol::Int, Vec::new())
    }

    fn nominal(symbol: Symbol) -> Ty {
        Ty::Nominal(symbol, Vec::new())
    }

    fn strukt(fields: &[(&str, Ty)]) -> StructInfo {
        let mut info = StructInfo::default();
        for (index, (name, ty)) in fields.iter().enumerate() {
            let property = sym(1000 + index as u32);
            info.fields.insert((*name).into(), (property, ty.clone()));
        }
        info
    }

    fn enum_of(params: Vec<SchemeParam>, variants: &[(&str, Vec<Ty>)]) -> Enum {
        let mut def = Enum {
            linear: false,
            heap: false,
            params,
            variants: IndexMap::new(),
            methods: IndexMap::new(),
            predicates: Vec::new(),
        };
        for (index, (name, payloads)) in variants.iter().enumerate() {
            def.variants.insert(
                (*name).into(),
                crate::types::catalog::Variant {
                    symbol: sym(2000 + index as u32),
                    payload_labels: vec![None; payloads.len()],
                    constructor_scheme: Scheme::mono(Ty::Func(
                        payloads.clone(),
                        Box::new(Ty::Tuple(Vec::new())),
                        EffectRow::new(Vec::new(), None),
                    )),
                },
            );
        }
        def
    }

    fn param(id: u32) -> SchemeParam {
        SchemeParam {
            symbol: sym(3000 + id),
            kind: ParamKind::Type,
            default: None,
        }
    }

    struct Fixture {
        structs: FxHashMap<Symbol, StructInfo>,
        enums: FxHashMap<Symbol, Enum>,
    }

    impl Fixture {
        fn new() -> Self {
            Fixture {
                structs: FxHashMap::default(),
                enums: FxHashMap::default(),
            }
        }

        fn session(&self) -> Layouts<'_> {
            let structs: FxHashMap<Symbol, &StructInfo> =
                self.structs.iter().map(|(k, v)| (*k, v)).collect();
            let enums: FxHashMap<Symbol, &Enum> =
                self.enums.iter().map(|(k, v)| (*k, v)).collect();
            Layouts::new(structs, enums, TypeCatalog::default())
        }

        fn layout(&self, ty: &Ty) -> Layout {
            self.session().of(ty)
        }
    }

    /// A flat all-Int product: every field one slot.
    fn product(symbol: Option<Symbol>, width: u32, offsets: Vec<u32>) -> Layout {
        let kinds = vec![SlotKind::Int; usize::try_from(width).unwrap_or_default()];
        let reprs = vec![FieldRepr::Slot(SlotKind::Int); offsets.len()];
        Layout::Inline(
            symbol.map(crate::backend::mir::executable),
            Shape::Product {
                width,
                offsets,
                reprs,
                kinds,
            },
        )
    }

    #[test]
    fn scalars_and_references_are_one_slot() {
        let fixture = Fixture::new();
        assert_eq!(fixture.layout(&int()), Layout::Slot);
        let func = Ty::Func(
            vec![int()],
            Box::new(int()),
            EffectRow::new(Vec::new(), None),
        );
        assert_eq!(fixture.layout(&func), Layout::Slot);
        let borrow = Ty::Borrow(
            crate::types::ty::Perm::Shared,
            Box::new(Ty::Tuple(vec![int(), int()])),
        );
        assert_eq!(fixture.layout(&borrow), Layout::Slot);
    }

    #[test]
    fn point_lays_out_inline() {
        let mut fixture = Fixture::new();
        let point = sym(1);
        fixture
            .structs
            .insert(point, strukt(&[("x", int()), ("y", int())]));
        assert_eq!(
            fixture.layout(&nominal(point)),
            product(Some(point), 2, vec![0, 1])
        );
    }

    #[test]
    fn nested_products_flatten() {
        let mut fixture = Fixture::new();
        let point = sym(1);
        let rect = sym(2);
        fixture
            .structs
            .insert(point, strukt(&[("x", int()), ("y", int())]));
        fixture.structs.insert(
            rect,
            strukt(&[("p", nominal(point)), ("q", nominal(point))]),
        );
        // The nested point layout is interned while the rect's shape is
        // computed, so the spliced fields reference it as L0.
        assert_eq!(
            fixture.layout(&nominal(rect)),
            Layout::Inline(
                Some(crate::backend::mir::executable(rect)),
                Shape::Product {
                    width: 4,
                    offsets: vec![0, 2],
                    reprs: vec![FieldRepr::Spliced(0), FieldRepr::Spliced(0)],
                    kinds: vec![SlotKind::Int; 4],
                }
            )
        );
    }

    #[test]
    fn tuples_lay_out_like_structs() {
        let mut fixture = Fixture::new();
        let point = sym(1);
        fixture
            .structs
            .insert(point, strukt(&[("x", int()), ("y", int())]));
        let tuple = Ty::Tuple(vec![int(), nominal(point), int()]);
        assert_eq!(
            fixture.layout(&tuple),
            Layout::Inline(
                None,
                Shape::Product {
                    width: 4,
                    offsets: vec![0, 1, 3],
                    reprs: vec![
                        FieldRepr::Slot(SlotKind::Int),
                        FieldRepr::Spliced(0),
                        FieldRepr::Slot(SlotKind::Int),
                    ],
                    kinds: vec![SlotKind::Int; 4],
                }
            )
        );
    }

    #[test]
    fn closed_records_use_label_order() {
        let mut fixture = Fixture::new();
        let point = sym(1);
        fixture
            .structs
            .insert(point, strukt(&[("x", int()), ("y", int())]));
        // `Row::closed` label-sorts, so `a` (the point) lands first.
        let record = Ty::Record(Row::closed(vec![
            (crate::label::Label::Named("b".into()), int()),
            (crate::label::Label::Named("a".into()), nominal(point)),
        ]));
        assert_eq!(
            fixture.layout(&record),
            Layout::Inline(
                None,
                Shape::Product {
                    width: 3,
                    offsets: vec![0, 2],
                    reprs: vec![FieldRepr::Spliced(0), FieldRepr::Slot(SlotKind::Int)],
                    kinds: vec![SlotKind::Int; 3],
                }
            )
        );
    }

    #[test]
    fn width_at_the_threshold_stays_inline() {
        let mut fixture = Fixture::new();
        let four = sym(1);
        fixture.structs.insert(
            four,
            strukt(&[("a", int()), ("b", int()), ("c", int()), ("d", int())]),
        );
        assert_eq!(
            fixture.layout(&nominal(four)),
            product(Some(four), 4, vec![0, 1, 2, 3])
        );
    }

    #[test]
    fn wide_aggregates_box() {
        let mut fixture = Fixture::new();
        let five = sym(1);
        fixture.structs.insert(
            five,
            strukt(&[
                ("a", int()),
                ("b", int()),
                ("c", int()),
                ("d", int()),
                ("e", int()),
            ]),
        );
        assert_eq!(
            fixture.layout(&nominal(five)),
            Layout::Boxed(
                Some(crate::backend::mir::executable(five)),
                Shape::Product {
                    width: 5,
                    offsets: vec![0, 1, 2, 3, 4],
                    reprs: vec![FieldRepr::Slot(SlotKind::Int); 5],
                    kinds: vec![SlotKind::Int; 5],
                }
            )
        );
    }

    #[test]
    fn recursive_enums_box_and_stay_finite() {
        let mut fixture = Fixture::new();
        let list = sym(1);
        fixture.enums.insert(
            list,
            enum_of(
                Vec::new(),
                &[("cons", vec![int(), nominal(list)]), ("nil", Vec::new())],
            ),
        );
        // The recursive payload is one boxed reference slot, so the shape
        // is finite: tag + Int + reference.
        assert_eq!(
            fixture.layout(&nominal(list)),
            Layout::Boxed(
                Some(crate::backend::mir::executable(list)),
                Shape::Sum {
                    width: 3,
                    payloads: vec![vec![1, 2], Vec::new()],
                    reprs: vec![
                        vec![
                            FieldRepr::Slot(SlotKind::Int),
                            FieldRepr::Slot(SlotKind::Value),
                        ],
                        Vec::new(),
                    ],
                    kinds: vec![SlotKind::Int, SlotKind::Int, SlotKind::Value],
                }
            )
        );
    }

    #[test]
    fn mutually_recursive_structs_both_box() {
        let mut fixture = Fixture::new();
        let a = sym(1);
        let b = sym(2);
        fixture.structs.insert(a, strukt(&[("b", nominal(b))]));
        fixture.structs.insert(b, strukt(&[("a", nominal(a))]));
        let boxed_one = |symbol| {
            Layout::Boxed(
                Some(crate::backend::mir::executable(symbol)),
                Shape::Product {
                    width: 1,
                    offsets: vec![0],
                    reprs: vec![FieldRepr::Slot(SlotKind::Value)],
                    kinds: vec![SlotKind::Value],
                },
            )
        };
        assert_eq!(fixture.layout(&nominal(a)), boxed_one(a));
        assert_eq!(fixture.layout(&nominal(b)), boxed_one(b));
    }

    #[test]
    fn generic_instantiation_is_inline() {
        let mut fixture = Fixture::new();
        let opt = sym(1);
        let t = param(0);
        let t_ty = Ty::Param(t.symbol);
        fixture.enums.insert(
            opt,
            enum_of(vec![t], &[("some", vec![t_ty]), ("none", Vec::new())]),
        );
        let opt_int = Ty::Nominal(opt, vec![int()]);
        assert_eq!(
            fixture.layout(&opt_int),
            Layout::Inline(
                Some(crate::backend::mir::executable(opt)),
                Shape::Sum {
                    width: 2,
                    payloads: vec![vec![1], Vec::new()],
                    reprs: vec![vec![FieldRepr::Slot(SlotKind::Int)], Vec::new()],
                    kinds: vec![SlotKind::Int, SlotKind::Int],
                }
            )
        );
        // A nested application of the same nominal is not recursion: the
        // declaration graph has no cycle, and the widths stay finite. The
        // inner option is a spliced payload of the outer one.
        let opt_opt_int = Ty::Nominal(opt, vec![opt_int]);
        assert_eq!(
            fixture.layout(&opt_opt_int),
            Layout::Inline(
                Some(crate::backend::mir::executable(opt)),
                Shape::Sum {
                    width: 3,
                    payloads: vec![vec![1], Vec::new()],
                    reprs: vec![vec![FieldRepr::Spliced(0)], Vec::new()],
                    kinds: vec![SlotKind::Int, SlotKind::Int, SlotKind::Int],
                }
            )
        );
    }

    #[test]
    fn param_fields_are_opaque() {
        let mut fixture = Fixture::new();
        let boxed = sym(1);
        let t = param(0);
        let t_ty = Ty::Param(t.symbol);
        let mut info = strukt(&[("value", t_ty.clone())]);
        info.params = vec![t];
        fixture.structs.insert(boxed, info);
        assert_eq!(fixture.layout(&Ty::Param(sym(99))), Layout::Opaque);
        // The rigid application (check-only instances) stays opaque…
        assert_eq!(
            fixture.layout(&Ty::Nominal(boxed, vec![t_ty])),
            Layout::Opaque
        );
        // …and the concrete application lays out.
        assert_eq!(
            fixture.layout(&Ty::Nominal(boxed, vec![int()])),
            product(Some(boxed), 1, vec![0])
        );
    }

    #[test]
    fn heap_structs_are_references() {
        let mut fixture = Fixture::new();
        let node = sym(1);
        let mut info = strukt(&[("value", int()), ("next", nominal(node))]);
        info.heap = true;
        fixture.structs.insert(node, info);
        assert_eq!(fixture.layout(&nominal(node)), Layout::Slot);
    }

    #[test]
    fn inline_arrays_stride_by_element() {
        let mut fixture = Fixture::new();
        let point = sym(1);
        fixture
            .structs
            .insert(point, strukt(&[("x", int()), ("y", int())]));
        let count = |n: i64| Ty::Static(StaticValue::Int(StaticInt::constant(n)));
        let two_ints = Ty::Nominal(Symbol::InlineArray, vec![int(), count(2)]);
        assert_eq!(
            fixture.layout(&two_ints),
            product(Some(Symbol::InlineArray), 2, vec![0, 1])
        );
        // Three points are six slots: over the threshold, boxed, with the
        // element stride preserved in the pointee shape.
        let three_points = Ty::Nominal(Symbol::InlineArray, vec![nominal(point), count(3)]);
        assert_eq!(
            fixture.layout(&three_points),
            Layout::Boxed(
                Some(crate::backend::mir::mir_inline_array()),
                Shape::Product {
                    width: 6,
                    offsets: vec![0, 2, 4],
                    reprs: vec![FieldRepr::Spliced(0); 3],
                    kinds: vec![SlotKind::Int; 6],
                }
            )
        );
    }

    #[test]
    fn empty_aggregates_are_zero_width() {
        let mut fixture = Fixture::new();
        let empty = sym(1);
        fixture.structs.insert(empty, strukt(&[]));
        assert_eq!(
            fixture.layout(&nominal(empty)),
            product(Some(empty), 0, Vec::new())
        );
        assert_eq!(
            fixture.layout(&Ty::Tuple(Vec::new())),
            product(None, 0, Vec::new())
        );
    }

    #[test]
    fn same_shape_nominals_intern_separately() {
        // Pair and Point agree on every slot, but a backend reabstracting
        // by LayoutId must recover the right display identity, so the
        // interned ids differ.
        let mut fixture = Fixture::new();
        let pair = sym(1);
        let point = sym(2);
        fixture
            .structs
            .insert(pair, strukt(&[("a", int()), ("b", int())]));
        fixture
            .structs
            .insert(point, strukt(&[("x", int()), ("y", int())]));
        let mut layouts = fixture.session();
        assert_ne!(layouts.id_of(&nominal(pair)), layouts.id_of(&nominal(point)));
    }

    #[test]
    fn one_slot_spliced_fields_stay_aggregates() {
        // The String model: Storage is a one-field struct around a raw
        // pointer, and String's first field splices it. The flattened
        // kinds cannot distinguish that from a scalar pointer field — the
        // repr is what records it, so reabstraction rebuilds the nested
        // aggregate instead of a bare word.
        let mut fixture = Fixture::new();
        let storage = sym(1);
        let text = sym(2);
        fixture.structs.insert(
            storage,
            strukt(&[("base", Ty::Nominal(Symbol::RawPtr, Vec::new()))]),
        );
        fixture.structs.insert(
            text,
            strukt(&[("storage", nominal(storage)), ("count", int())]),
        );
        assert_eq!(
            fixture.layout(&nominal(text)),
            Layout::Inline(
                Some(crate::backend::mir::executable(text)),
                Shape::Product {
                    width: 2,
                    offsets: vec![0, 1],
                    reprs: vec![FieldRepr::Spliced(0), FieldRepr::Slot(SlotKind::Int)],
                    kinds: vec![SlotKind::Ptr, SlotKind::Int],
                }
            )
        );
    }

    #[test]
    fn slot_kinds_keep_scalar_tags_and_join_to_value() {
        // Bool and Byte are one native word but keep their kinds, so a
        // backend re-tags them exactly; variants that disagree on a
        // slot's kind degrade that slot to a tagged value.
        let mut fixture = Fixture::new();
        let flags = sym(1);
        let mixed = sym(2);
        fixture.structs.insert(
            flags,
            strukt(&[
                ("on", Ty::Nominal(Symbol::Bool, Vec::new())),
                ("raw", Ty::Nominal(Symbol::Byte, Vec::new())),
            ]),
        );
        fixture.enums.insert(
            mixed,
            enum_of(
                Vec::new(),
                &[
                    ("count", vec![int()]),
                    ("truth", vec![Ty::Nominal(Symbol::Bool, Vec::new())]),
                ],
            ),
        );
        assert_eq!(
            fixture.layout(&nominal(flags)),
            Layout::Inline(
                Some(crate::backend::mir::executable(flags)),
                Shape::Product {
                    width: 2,
                    offsets: vec![0, 1],
                    reprs: vec![
                        FieldRepr::Slot(SlotKind::Bool),
                        FieldRepr::Slot(SlotKind::Byte),
                    ],
                    kinds: vec![SlotKind::Bool, SlotKind::Byte],
                }
            )
        );
        assert_eq!(
            fixture.layout(&nominal(mixed)),
            Layout::Inline(
                Some(crate::backend::mir::executable(mixed)),
                Shape::Sum {
                    width: 2,
                    payloads: vec![vec![1], vec![1]],
                    reprs: vec![
                        vec![FieldRepr::Slot(SlotKind::Int)],
                        vec![FieldRepr::Slot(SlotKind::Bool)],
                    ],
                    kinds: vec![SlotKind::Int, SlotKind::Value],
                }
            )
        );
    }

    fn table() -> Vec<Layout> {
        vec![
            Layout::Inline(
                None,
                Shape::Product {
                    width: 2,
                    offsets: vec![0, 1],
                    reprs: vec![FieldRepr::Slot(SlotKind::Int); 2],
                    kinds: vec![SlotKind::Int; 2],
                },
            ),
            Layout::Boxed(
                None,
                Shape::Product {
                    width: 5,
                    offsets: vec![0, 1, 2, 3, 4],
                    reprs: vec![FieldRepr::Slot(SlotKind::Int); 5],
                    kinds: vec![SlotKind::Int; 5],
                },
            ),
        ]
    }

    fn function(n_locals: u16, blocks: Vec<crate::backend::mir::BlockData>) -> Function {
        Function {
            frame_sites: Default::default(),
            param_reprs: Vec::new(),
            return_repr: None,
            name: "t".into(),
            arity: 1,
            locals: crate::backend::mir::LocalInfo::uniform(n_locals),
            blocks,
        }
    }

    #[test]
    fn derivation_follows_constructions_copies_and_edges() {
        use crate::backend::mir::{BlockData, Term};
        let blocks = vec![
            BlockData {
                params: Vec::new(),
                insts: vec![
                    Inst::Aggregate {
                        tag: 0,
                        dest: 1,
                        layout: 0,
                        args: Vec::new(),
                    },
                    Inst::Copy {
                        dest: 2,
                        src: Operand::Local(1),
                    },
                ],
                term: Some(Term::Goto(1, vec![Operand::Local(2)])),
            },
            BlockData {
                params: vec![3],
                insts: Vec::new(),
                term: Some(Term::Return(Operand::Local(3))),
            },
        ];
        let derived = local_layouts(&function(4, blocks), &table(), &[]);
        assert_eq!(derived, vec![None, Some(0), Some(0), Some(0)]);
    }

    #[test]
    fn conflicting_definitions_degrade_to_uniform() {
        use crate::backend::mir::{BlockData, Term};
        let blocks = vec![BlockData {
            params: Vec::new(),
            insts: vec![
                Inst::Aggregate {
                    tag: 0,
                    dest: 1,
                    layout: 0,
                    args: Vec::new(),
                },
                Inst::Call {
                    dest: 1,
                    func: 0,
                    args: Vec::new(),
                    unwind: None,
                },
            ],
            term: Some(Term::Return(Operand::Local(1))),
        }];
        let derived = local_layouts(&function(2, blocks), &table(), &[]);
        assert_eq!(derived, vec![None, None]);
    }

    #[test]
    fn boxed_constructions_stay_uniform() {
        use crate::backend::mir::{BlockData, Term};
        let blocks = vec![BlockData {
            params: Vec::new(),
            insts: vec![Inst::Aggregate {
                tag: 0,
                dest: 1,
                layout: 1,
                args: Vec::new(),
            }],
            term: Some(Term::Return(Operand::Local(1))),
        }];
        let derived = local_layouts(&function(2, blocks), &table(), &[]);
        assert_eq!(derived, vec![None, None]);
    }

    // One scalar classifier for slots and buffer elements: ownership
    // wrappers never change a scalar's word class (a unique Int and a
    // borrowed Int are both an Int in the target).
    #[test]
    fn scalar_kind_peels_ownership_wrappers() {
        let int = Ty::Nominal(Symbol::Int, Vec::new());
        assert_eq!(scalar_kind(&int), SlotKind::Int);
        assert_eq!(scalar_kind(&Ty::Unique(Box::new(int.clone()))), SlotKind::Int);
        assert_eq!(
            scalar_kind(&Ty::Borrow(crate::types::ty::Perm::Shared, Box::new(int))),
            SlotKind::Int
        );
    }

    #[test]
    fn params_and_call_results_seed_their_published_layouts() {
        use crate::backend::mir::{BlockData, Term};
        // Param 0 arrives as an inline pair (by-value borrow), the call
        // returns another; both class their locals.
        let blocks = vec![BlockData {
            params: Vec::new(),
            insts: vec![Inst::Call {
                dest: 1,
                func: 0,
                args: Vec::new(),
                unwind: None,
            }],
            term: Some(Term::Return(Operand::Local(1))),
        }];
        let mut f = function(2, blocks);
        f.param_reprs = vec![ParamRepr::Borrow(0)];
        let derived = local_layouts(&f, &table(), &[Some(0)]);
        assert_eq!(derived, vec![Some(0), Some(0)]);
    }
}
