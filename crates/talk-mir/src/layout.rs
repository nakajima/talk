//! Aggregate layout data (ADR 0045): the shapes the compiler publishes
//! per aggregate type. Backends read these facts; they do not infer them.
//!
//! Widths and offsets are in abstract slot units — one slot holds one
//! scalar or one reference. Slot-to-byte mapping is a target detail.

use crate::MirSymbol;

/// An interned layout: an index into the module's layout table. The
/// aggregate instructions carry one so a backend reads the shape it must
/// produce instead of inferring it.
pub type LayoutId = u32;

/// How a value of one type occupies storage. Inline and boxed aggregates
/// carry the nominal they came from (`None` for tuples, closed records,
/// and inline arrays), so a backend holding only a `LayoutId` can still
/// give a reabstracted value its display identity. Interning therefore
/// separates same-shaped nominals: `Pair` and `Point` may agree on every
/// slot and still get distinct ids.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Layout {
    /// One slot: a scalar, or a reference — a borrow, a closure, an
    /// existential package, a `'heap` object, a buffer handle.
    Slot,
    /// A finite aggregate stored flat in its container.
    Inline(Option<MirSymbol>, Shape),
    /// An aggregate behind one reference slot, because recursion (rule 2)
    /// or width (rule 3) forced it. The shape describes the pointee.
    Boxed(Option<MirSymbol>, Shape),
    /// The type mentions a rigid parameter or projection: legal to build
    /// and ownership-verify in check-only rigid instances, rejected at
    /// emission (ADR 0045 rule 6).
    Opaque,
}

/// The native representation of one slot, so a backend can emit untagged
/// storage (ADR 0045 native layout). Int, Bool, and Byte are all one
/// 64-bit word natively (no sub-word packing in the slot model) but stay
/// distinct kinds so a backend can re-tag a word exactly when a value
/// crosses back into tagged representation. `Value` is a tagged runtime
/// value, for everything whose native form is not pinned yet (references
/// to boxed aggregates, closures, existentials, borrows, heap objects).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotKind {
    Int,
    Bool,
    Byte,
    F64,
    Ptr,
    Value,
}

impl SlotKind {
    fn render(self) -> &'static str {
        match self {
            SlotKind::Int => "int",
            SlotKind::Bool => "bool",
            SlotKind::Byte => "byte",
            SlotKind::F64 => "f64",
            SlotKind::Ptr => "ptr",
            SlotKind::Value => "value",
        }
    }
}

/// How one product field or one sum payload element occupies its slots:
/// one typed slot, or a nested inline aggregate spliced across several.
/// The distinction is what lets a backend reabstract — a spliced field
/// crossing into uniform representation must become that aggregate again
/// (by its own interned layout), not a bare word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FieldRepr {
    Slot(SlotKind),
    Spliced(LayoutId),
}

impl FieldRepr {
    fn render(self) -> String {
        match self {
            FieldRepr::Slot(kind) => kind.render().to_string(),
            FieldRepr::Spliced(layout) => format!("L{layout}"),
        }
    }
}

/// The flat shape of an aggregate: total width in slots, where each
/// field starts, how each field is represented, and what each slot
/// natively is. `kinds` is the flattened per-slot view (spliced fields
/// expanded); `reprs` is the per-field structural view a backend needs to
/// move one field between native and tagged representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// Structs, tuples, and closed records (label-sorted, matching the
    /// row's canonical order): one offset and repr per field in
    /// declaration order.
    Product {
        width: u32,
        offsets: Vec<u32>,
        reprs: Vec<FieldRepr>,
        kinds: Vec<SlotKind>,
    },
    /// Enums: the tag at slot 0, then each variant's payload offsets and
    /// reprs in tag order. Width is the tag plus the widest variant; a
    /// slot whose kind differs across variants is a tagged `Value`.
    Sum {
        width: u32,
        payloads: Vec<Vec<u32>>,
        reprs: Vec<Vec<FieldRepr>>,
        kinds: Vec<SlotKind>,
    },
}

impl Shape {
    pub fn width(&self) -> u32 {
        match self {
            Shape::Product { width, .. } | Shape::Sum { width, .. } => *width,
        }
    }

    pub fn kinds(&self) -> &[SlotKind] {
        match self {
            Shape::Product { kinds, .. } | Shape::Sum { kinds, .. } => kinds,
        }
    }

    fn render(&self) -> String {
        let kinds = |kinds: &[SlotKind]| {
            kinds
                .iter()
                .map(|kind| kind.render())
                .collect::<Vec<_>>()
                .join(", ")
        };
        let fields = |offsets: &[u32], reprs: &[FieldRepr]| {
            offsets
                .iter()
                .zip(reprs)
                .map(|(offset, repr)| format!("{offset}:{}", repr.render()))
                .collect::<Vec<_>>()
                .join(", ")
        };
        match self {
            Shape::Product {
                width,
                offsets,
                reprs,
                kinds: slot_kinds,
            } => format!(
                "width {width}, fields [{}], kinds [{}]",
                fields(offsets, reprs),
                kinds(slot_kinds)
            ),
            Shape::Sum {
                width,
                payloads,
                reprs,
                kinds: slot_kinds,
            } => format!(
                "width {width}, payloads [{}], kinds [{}]",
                payloads
                    .iter()
                    .zip(reprs)
                    .map(|(offsets, reprs)| format!("[{}]", fields(offsets, reprs)))
                    .collect::<Vec<_>>()
                    .join(", "),
                kinds(slot_kinds)
            ),
        }
    }
}

impl Layout {
    /// One-line rendering for the `talk mir` dump.
    pub fn render(&self) -> String {
        let identity = |symbol: &Option<MirSymbol>| match symbol {
            Some(symbol) => format!("{symbol:?} "),
            None => String::new(),
        };
        match self {
            Layout::Slot => "slot".into(),
            Layout::Inline(symbol, shape) => {
                format!("inline {}{}", identity(symbol), shape.render())
            }
            Layout::Boxed(symbol, shape) => format!("boxed {}{}", identity(symbol), shape.render()),
            Layout::Opaque => "opaque".into(),
        }
    }
}

/// How one parameter arrives at a direct call (ADR 0045 native layout):
/// a uniform tagged value, an inline aggregate by value, or an inline
/// aggregate by borrow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamRepr {
    Uniform,
    Value(LayoutId),
    Borrow(LayoutId),
}

impl ParamRepr {
    pub fn layout(self) -> Option<LayoutId> {
        match self {
            ParamRepr::Uniform => None,
            ParamRepr::Value(layout) | ParamRepr::Borrow(layout) => Some(layout),
        }
    }

    pub fn render(self) -> String {
        match self {
            ParamRepr::Uniform => "uniform".into(),
            ParamRepr::Value(layout) => format!("L{layout}"),
            ParamRepr::Borrow(layout) => format!("&L{layout}"),
        }
    }
}
