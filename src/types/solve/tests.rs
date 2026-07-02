use super::*;
use crate::compiling::module::ModuleId;
use crate::name_resolution::symbol::{EffectId, StructId, TypeParameterId};
use crate::types::constraint::CtReason;
use crate::types::ty::Perm;

fn origin() -> CtOrigin {
    CtOrigin::new(NodeID::ANY, CtReason::Apply)
}

fn effect(id: u32) -> Symbol {
    Symbol::Effect(EffectId::new(ModuleId::Current, id))
}

struct Harness {
    store: VarStore,
    errors: Vec<(TypeError, NodeID)>,
    catalog: TypeCatalog,
    schemes: FxHashMap<Symbol, Scheme>,
    mono: FxHashMap<Symbol, Ty>,
    instantiations: FxHashMap<NodeID, Vec<(Symbol, Ty)>>,
    member_resolutions: FxHashMap<NodeID, MemberResolution>,
    coerce_clones: rustc_hash::FxHashSet<NodeID>,
}

impl Harness {
    fn new() -> Self {
        Harness {
            store: VarStore::default(),
            errors: vec![],
            catalog: TypeCatalog::default(),
            schemes: FxHashMap::default(),
            mono: FxHashMap::default(),
            instantiations: FxHashMap::default(),
            member_resolutions: FxHashMap::default(),
            coerce_clones: rustc_hash::FxHashSet::default(),
        }
    }

    fn solve(&mut self, wanteds: Vec<Constraint>) -> Vec<Constraint> {
        let mut solver = Solver {
            store: &mut self.store,
            errors: &mut self.errors,
            catalog: &self.catalog,
            schemes: &self.schemes,
            mono: &self.mono,
            instantiations: &mut self.instantiations,
            member_resolutions: &mut self.member_resolutions,
            coerce_clones: &mut self.coerce_clones,
            level: Level(1),
            defaulting: false,
            givens: vec![],
            touchable_level: None,
            local_params: vec![],
            derived_seen: Default::default(),
        };
        solver.solve(wanteds)
    }
}

#[test]
fn occurs_check_rejects_infinite_type() {
    let mut h = Harness::new();
    let var = h.store.fresh_ty(Level(1), NodeID::ANY);
    let infinite = Ty::Func(vec![Ty::Var(var)], Box::new(Ty::unit()), EffectRow::pure());
    h.solve(vec![Constraint::Eq(Ty::Var(var), infinite, origin())]);
    assert_eq!(h.errors.len(), 1);
    assert!(matches!(h.errors[0].0, TypeError::InfiniteType { .. }));
}

#[test]
fn level_adjustment_propagates_outward() {
    // Rémy 1992: binding an outer-level var to a type containing an
    // inner-level var must drag the inner var's level out, so an inner
    // generalization point can no longer quantify it.
    let mut h = Harness::new();
    let outer = h.store.fresh_ty(Level(0), NodeID::ANY);
    let inner = h.store.fresh_ty(Level(1), NodeID::ANY);
    h.solve(vec![Constraint::Eq(
        Ty::Var(outer),
        Ty::Func(
            vec![Ty::Var(inner)],
            Box::new(Ty::unit()),
            EffectRow::pure(),
        ),
        origin(),
    )]);
    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert_eq!(h.store.level(inner.0), Level(0));
}

#[test]
fn apply_reason_clones_borrowed_cheap_clone_argument() {
    let mut h = Harness::new();
    let cheap = Symbol::Struct(StructId::new(ModuleId::Current, 7));
    h.catalog
        .conformances
        .insert((cheap, Symbol::CheapClone), Default::default());
    let owned = Ty::Nominal(cheap, vec![]);
    let borrowed = Ty::Borrow(Perm::Shared, Box::new(owned.clone()));
    let residual = h.solve(vec![Constraint::Eq(owned, borrowed, origin())]);
    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert!(residual.is_empty(), "{residual:?}");
    assert!(
        h.coerce_clones.contains(&NodeID::ANY),
        "the coercion site should be recorded for lowering"
    );
}

#[test]
fn apply_reason_does_not_strip_borrows_in_general_unification() {
    let mut h = Harness::new();
    let int = Ty::Nominal(Symbol::Int, vec![]);
    let borrowed_int = Ty::Borrow(Perm::Shared, Box::new(int.clone()));
    let residual = h.solve(vec![Constraint::Eq(int, borrowed_int, origin())]);
    assert!(
        h.errors
            .iter()
            .any(|(error, _)| matches!(error, TypeError::Mismatch { .. })),
        "{:?}",
        h.errors
    );
    assert!(residual.is_empty(), "{residual:?}");
}

#[test]
fn implication_floats_untouchable_equalities_without_givens() {
    let mut h = Harness::new();
    let outer = h.store.fresh_ty(Level(1), NodeID::ANY);
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![],
        wanteds: vec![Constraint::Eq(
            Ty::Var(outer),
            Ty::Nominal(Symbol::Int, vec![]),
            origin(),
        )],
        local_params: vec![],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert!(residual.is_empty(), "{:?}", residual);
    assert_eq!(
        h.store.shallow(&Ty::Var(outer)),
        Ty::Nominal(Symbol::Int, vec![])
    );
}

#[test]
fn implication_with_givens_floats_safe_untouchable_outer_variable() {
    let mut h = Harness::new();
    let outer = h.store.fresh_ty(Level(1), NodeID::ANY);
    let marker = Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, 98));
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![Predicate::TypeEq(
            Ty::Param(marker),
            Ty::Nominal(Symbol::Bool, vec![]),
        )],
        wanteds: vec![Constraint::Eq(
            Ty::Var(outer),
            Ty::Nominal(Symbol::Int, vec![]),
            origin(),
        )],
        local_params: vec![],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert!(residual.is_empty(), "{:?}", residual);
    assert_eq!(
        h.store.shallow(&Ty::Var(outer)),
        Ty::Nominal(Symbol::Int, vec![])
    );
}

#[test]
fn implication_can_bind_touchable_local_variable() {
    let mut h = Harness::new();
    let local = h.store.fresh_ty(Level(2), NodeID::ANY);
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![],
        wanteds: vec![Constraint::Eq(
            Ty::Var(local),
            Ty::Nominal(Symbol::Int, vec![]),
            origin(),
        )],
        local_params: vec![],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert!(residual.is_empty(), "{:?}", residual);
    assert_eq!(
        h.store.shallow(&Ty::Var(local)),
        Ty::Nominal(Symbol::Int, vec![])
    );
}

#[test]
fn implication_floats_untouchable_effect_equalities() {
    let mut h = Harness::new();
    let outer = h.store.fresh_eff(Level(1), NodeID::ANY);
    let expected = EffectRow::open(outer);
    let found = EffectRow {
        effects: [effect(1)].into(),
        tail: None,
    };
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![],
        wanteds: vec![Constraint::EffEq(expected.clone(), found, origin())],
        local_params: vec![],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert!(residual.is_empty(), "{:?}", residual);
    let (effects, tail) = h.store.flatten_eff(&expected);
    assert_eq!(effects, [effect(1)].into());
    assert_eq!(tail, FlatTail::None);
}

#[test]
fn implication_rejects_escape_hidden_by_local_given_rewrite() {
    let mut h = Harness::new();
    let outer = h.store.fresh_ty(Level(1), NodeID::ANY);
    let existential = Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, 97));
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![Predicate::TypeEq(
            Ty::Param(existential),
            Ty::Nominal(Symbol::Int, vec![]),
        )],
        wanteds: vec![Constraint::Eq(
            Ty::Var(outer),
            Ty::Param(existential),
            origin(),
        )],
        local_params: vec![existential],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(residual.is_empty(), "{residual:?}");
    assert_eq!(h.errors.len(), 1);
    assert!(matches!(
        h.errors[0].0,
        TypeError::EscapingExistential { .. }
    ));
    assert!(matches!(h.store.shallow(&Ty::Var(outer)), Ty::Var(_)));
}

#[test]
fn implication_rejects_escape_laundered_through_given_chain() {
    // Same leak as above, but the dependence on the constructor-local
    // existential is hidden behind a chain of givens: the wanted's RHS is
    // an OUTER parameter that does not itself appear in `local_params`,
    // yet a given chain `bridge ~ existential`, `existential ~ Int`
    // launders it to a concrete `Int`. If the pre-rewrite residual guard
    // only inspects literal mentions of local params, the escape slips
    // through and `outer := Int` commits globally.
    let mut h = Harness::new();
    let outer = h.store.fresh_ty(Level(1), NodeID::ANY);
    let existential = Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, 96));
    let bridge = Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, 95));
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![
            Predicate::TypeEq(Ty::Param(bridge), Ty::Param(existential)),
            Predicate::TypeEq(Ty::Param(existential), Ty::Nominal(Symbol::Int, vec![])),
        ],
        wanteds: vec![Constraint::Eq(Ty::Var(outer), Ty::Param(bridge), origin())],
        local_params: vec![existential],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(residual.is_empty(), "{residual:?}");
    assert_eq!(h.errors.len(), 1, "errors: {:?}", h.errors);
    assert!(matches!(
        h.errors[0].0,
        TypeError::EscapingExistential { .. }
    ));
    assert!(matches!(h.store.shallow(&Ty::Var(outer)), Ty::Var(_)));
}

#[test]
fn implication_rejects_escaping_existential() {
    let mut h = Harness::new();
    let outer = h.store.fresh_ty(Level(1), NodeID::ANY);
    let existential = Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, 99));
    let residual = h.solve(vec![Constraint::Implic(Box::new(Implication {
        level: Level(2),
        givens: vec![],
        wanteds: vec![Constraint::Eq(
            Ty::Var(outer),
            Ty::Param(existential),
            origin(),
        )],
        local_params: vec![existential],
        touchable_level: Some(Level(2)),
    }))]);

    assert!(residual.is_empty(), "{:?}", residual);
    assert_eq!(h.errors.len(), 1);
    assert!(matches!(
        h.errors[0].0,
        TypeError::EscapingExistential { .. }
    ));
}

#[test]
fn concrete_head_mismatch_with_params_reports_at_gadt_branch() {
    let mut h = Harness::new();
    let param = Symbol::TypeParameter(TypeParameterId::new(ModuleId::Current, 100));
    let left = Ty::Nominal(
        Symbol::Struct(StructId::new(ModuleId::Current, 1)),
        vec![Ty::Param(param)],
    );
    let right = Ty::Nominal(
        Symbol::Struct(StructId::new(ModuleId::Current, 2)),
        vec![Ty::Param(param)],
    );
    h.solve(vec![Constraint::Eq(
        left,
        right,
        CtOrigin::new(NodeID::ANY, CtReason::GadtBranch),
    )]);

    assert_eq!(h.errors.len(), 1);
    assert!(matches!(h.errors[0].0, TypeError::Mismatch { .. }));
}

#[test]
fn cross_kind_gadt_branch_mismatch_with_unresolved_arg_reports_mismatch() {
    let mut h = Harness::new();
    let unresolved = h.store.fresh_ty(Level(1), NodeID::ANY);
    let left = Ty::Tuple(vec![]);
    let right = Ty::Nominal(
        Symbol::Struct(StructId::new(ModuleId::Current, 3)),
        vec![Ty::Var(unresolved)],
    );
    h.solve(vec![Constraint::Eq(
        left,
        right,
        CtOrigin::new(NodeID::ANY, CtReason::GadtBranch),
    )]);

    assert_eq!(h.errors.len(), 1);
    assert!(matches!(h.errors[0].0, TypeError::Mismatch { .. }));
}

#[test]
fn effect_rows_merge_through_open_tails() {
    // Leijen-style row rewriting over a Koka-style effect-label set:
    // <'a | t1> ~ <'b | t2> leaves both flattening to {'a, 'b | t3}.
    let mut h = Harness::new();
    let t1 = h.store.fresh_eff(Level(1), NodeID::ANY);
    let t2 = h.store.fresh_eff(Level(1), NodeID::ANY);
    let a = EffectRow {
        effects: [effect(1)].into(),
        tail: Some(EffTail::Var(t1)),
    };
    let b = EffectRow {
        effects: [effect(2)].into(),
        tail: Some(EffTail::Var(t2)),
    };
    h.solve(vec![Constraint::EffEq(a.clone(), b.clone(), origin())]);
    assert!(h.errors.is_empty(), "{:?}", h.errors);
    let (za, ta) = h.store.flatten_eff(&a);
    let (zb, tb) = h.store.flatten_eff(&b);
    assert_eq!(za, [effect(1), effect(2)].into());
    assert_eq!(zb, za);
    assert_eq!(ta, tb, "both rows share the fresh tail");
}

#[test]
fn closed_effect_row_rejects_extra_labels() {
    let mut h = Harness::new();
    let open = EffectRow {
        effects: [effect(1)].into(),
        tail: None,
    };
    let closed = EffectRow::pure();
    h.solve(vec![Constraint::EffEq(open, closed, origin())]);
    assert_eq!(h.errors.len(), 1);
}

#[test]
fn record_rows_unify_by_decomposition() {
    // { x: Int | r1 } ~ { y: Float | r2 }: each side's leftover field
    // flows into the other's tail (Leijen 2005 §3).
    let mut h = Harness::new();
    let r1 = h.store.fresh_row(Level(1), NodeID::ANY);
    let r2 = h.store.fresh_row(Level(1), NodeID::ANY);
    let a = Row {
        fields: vec![(Label::Named("x".into()), Ty::Nominal(Symbol::Int, vec![]))],
        tail: Some(RowTail::Var(r1)),
    };
    let b = Row {
        fields: vec![(Label::Named("y".into()), Ty::Nominal(Symbol::Float, vec![]))],
        tail: Some(RowTail::Var(r2)),
    };
    h.solve(vec![Constraint::Eq(
        Ty::Record(a.clone()),
        Ty::Record(b.clone()),
        origin(),
    )]);
    assert!(h.errors.is_empty(), "{:?}", h.errors);
    let za = h.store.zonk_row(&a);
    let zb = h.store.zonk_row(&b);
    assert_eq!(za.fields, zb.fields);
    assert_eq!(za.fields.len(), 2);
}

#[test]
fn record_row_occurs_check_rejects_cyclic_tail_through_field() {
    let mut h = Harness::new();
    let r1 = h.store.fresh_row(Level(1), NodeID::ANY);
    let r2 = h.store.fresh_row(Level(1), NodeID::ANY);
    let a = Row {
        fields: vec![(
            Label::Named("x".into()),
            Ty::Record(Row {
                fields: vec![],
                tail: Some(RowTail::Var(r2)),
            }),
        )],
        tail: Some(RowTail::Var(r1)),
    };
    let b = Row {
        fields: vec![],
        tail: Some(RowTail::Var(r2)),
    };
    h.solve(vec![Constraint::Eq(Ty::Record(a), Ty::Record(b), origin())]);
    assert_eq!(h.errors.len(), 1);
    assert!(matches!(h.errors[0].0, TypeError::InfiniteType { .. }));
}

#[test]
fn two_open_row_tails_stop_after_first_occurs_failure() {
    let mut h = Harness::new();
    let x = h.store.fresh_row(Level(1), NodeID::ANY);
    let y = h.store.fresh_row(Level(1), NodeID::ANY);
    let a = Row {
        fields: vec![],
        tail: Some(RowTail::Var(x)),
    };
    let b = Row {
        fields: vec![(
            Label::Named("cycle".into()),
            Ty::Record(Row {
                fields: vec![],
                tail: Some(RowTail::Var(x)),
            }),
        )],
        tail: Some(RowTail::Var(y)),
    };

    h.solve(vec![Constraint::Eq(Ty::Record(a), Ty::Record(b), origin())]);

    assert_eq!(h.errors.len(), 1);
    assert!(matches!(h.errors[0].0, TypeError::InfiniteType { .. }));
    assert!(h.store.value(y.0).is_none());
}

#[test]
fn closed_record_rows_must_match_exactly() {
    let mut h = Harness::new();
    let a = Row::closed(vec![(
        Label::Named("x".into()),
        Ty::Nominal(Symbol::Int, vec![]),
    )]);
    let b = Row::closed(vec![]);
    h.solve(vec![Constraint::Eq(Ty::Record(a), Ty::Record(b), origin())]);
    assert_eq!(h.errors.len(), 1);
}

fn borrowed_int(perm: Perm) -> Ty {
    Ty::Borrow(perm, Box::new(Ty::Nominal(Symbol::Int, vec![])))
}

#[test]
fn perm_var_unifies_with_concrete_permission() {
    let mut h = Harness::new();
    let p = h.store.fresh_perm(Level(1), NodeID::ANY);
    let lhs = borrowed_int(Perm::Var(p));
    h.solve(vec![Constraint::Eq(
        lhs.clone(),
        borrowed_int(Perm::Exclusive),
        origin(),
    )]);
    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert_eq!(h.store.zonk_ty(&lhs), borrowed_int(Perm::Exclusive));
}

#[test]
fn perm_vars_union_and_share_solution() {
    let mut h = Harness::new();
    let p1 = h.store.fresh_perm(Level(1), NodeID::ANY);
    let p2 = h.store.fresh_perm(Level(1), NodeID::ANY);
    let a = borrowed_int(Perm::Var(p1));
    let b = borrowed_int(Perm::Var(p2));
    h.solve(vec![
        Constraint::Eq(a.clone(), b.clone(), origin()),
        Constraint::Eq(b, borrowed_int(Perm::Exclusive), origin()),
    ]);
    assert!(h.errors.is_empty(), "{:?}", h.errors);
    assert_eq!(h.store.zonk_ty(&a), borrowed_int(Perm::Exclusive));
}

#[test]
fn concrete_permission_mismatch_reports_error() {
    let mut h = Harness::new();
    h.solve(vec![Constraint::Eq(
        borrowed_int(Perm::Shared),
        borrowed_int(Perm::Exclusive),
        origin(),
    )]);
    assert!(
        h.errors
            .iter()
            .any(|(error, _)| matches!(error, TypeError::Mismatch { .. })),
        "{:?}",
        h.errors
    );
}

#[test]
fn unsolved_perm_var_defaults_to_shared() {
    let mut h = Harness::new();
    let p = h.store.fresh_perm(Level(1), NodeID::ANY);
    let ty = borrowed_int(Perm::Var(p));
    assert_eq!(
        h.store.default_unsolved_perms(&ty),
        borrowed_int(Perm::Shared)
    );
    // Defaulting binds the variable in the store, so every sharer sees it.
    assert_eq!(h.store.zonk_ty(&ty), borrowed_int(Perm::Shared));
}

#[test]
fn generalizer_quantifies_unsolved_perm_var_into_perm_params() {
    let mut h = Harness::new();
    let mut symbols = crate::name_resolution::symbol::Symbols::default();
    let p = h.store.fresh_perm(Level(1), NodeID::ANY);
    let ty = borrowed_int(Perm::Var(p));
    let mut generalizer = Generalizer::new(
        &mut h.store,
        &mut symbols,
        ModuleId::Current,
        Level(0),
        FxHashMap::default(),
    );
    let scheme = generalizer.generalize(&ty, &[]);
    assert_eq!(scheme.perm_params.len(), 1, "{scheme:?}");
    let Ty::Borrow(Perm::Param(param), _) = &scheme.ty else {
        panic!("expected quantified perm param, got {:?}", scheme.ty);
    };
    assert_eq!(*param, scheme.perm_params[0]);
    // Grade polymorphism is invisible in renders: a perm param shows as `&`.
    assert_eq!(scheme.ty.render_mono(), "&Int");
}

#[test]
fn substitute_replaces_perm_params() {
    let mut symbols = crate::name_resolution::symbol::Symbols::default();
    let param = Symbol::TypeParameter(symbols.next_type_parameter(ModuleId::Current));
    let ty = borrowed_int(Perm::Param(param));
    let mut perms = FxHashMap::default();
    perms.insert(param, Perm::Exclusive);
    assert_eq!(ty.substitute_perms(&perms), borrowed_int(Perm::Exclusive));
}
