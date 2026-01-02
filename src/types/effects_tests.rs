#[cfg(test)]
pub mod tests {
    use indexmap::indexset;

    use crate::{
        assert_eq_diff,
        label::Label,
        name_resolution::symbol::{EffectId, GlobalId, Symbol},
        types::{
            infer_row::RowParamId,
            row::Row,
            scheme::{ForAll, Scheme},
            ty::Ty,
            type_session::TypeEntry,
            types_tests::tests::{typecheck, typecheck_err},
        },
    };

    #[test]
    fn infers_func_with_indirect_effect() {
        let (_ast, types) = typecheck(
            "
          effect 'fizz() -> Int

          func fizzes() {
            'fizz()
          }

          func callsFizzes() {
              fizzes()
          }
        ",
        );

        assert_eq_diff!(
            types
                .get_symbol(&Symbol::Global(GlobalId::from(2)))
                .cloned(),
            Some(TypeEntry::Poly(Scheme {
                foralls: indexset! {ForAll::Row(1.into()),ForAll::Row(2.into())},
                predicates: vec![],
                ty: Ty::Func(
                    Ty::Void.into(),
                    Ty::Int.into(),
                    Row::Extend {
                        row: Row::Param(RowParamId(2)).into(),
                        label: Label::_Symbol(EffectId::from(1).into()),
                        ty: Ty::Func(Ty::Void.into(), Ty::Int.into(), Row::Empty.into())
                    }
                    .into()
                )
            }))
        )
    }

    #[test]
    fn infers_func_with_effect() {
        let (_ast, types) = typecheck(
            "
          effect 'fizz() -> Int

          func fizzes() {
            'fizz()
          }
        ",
        );

        assert_eq!(
            types
                .get_symbol(&Symbol::Global(GlobalId::from(1)))
                .cloned(),
            Some(TypeEntry::Poly(Scheme {
                foralls: indexset! {ForAll::Row(1.into())},
                predicates: vec![],
                ty: Ty::Func(
                    Ty::Void.into(),
                    Ty::Int.into(),
                    Row::Extend {
                        row: Row::Param(RowParamId(1)).into(),
                        label: Label::_Symbol(EffectId::from(1).into()),
                        ty: Ty::Func(Ty::Void.into(), Ty::Int.into(), Row::Empty.into())
                    }
                    .into()
                )
            }))
        )
    }

    #[test]
    fn checks_pure_func_has_no_effects() {
        let (_ast, _types, diagnostics) = typecheck_err(
            "
          effect 'fizz() -> Int

          func fizzes() '[] {
            'fizz()
          }
        ",
        );

        assert_eq!(1, diagnostics.len(), "{diagnostics:?}");
    }

    #[test]
    fn checks_pure_func_has_no_indirect_effects() {
        let (_ast, _types, diagnostics) = typecheck_err(
            "
          effect 'fizz() -> Int

          func callsFizzes() {
              'fizz()
          }

          func fizzes() '[] {
              callsFizzes()
          }
        ",
        );

        assert_eq!(1, diagnostics.len(), "{diagnostics:?}");
    }
}
