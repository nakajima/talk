#[cfg(test)]
pub mod tests {
    use indexmap::indexset;

    use crate::{
        assert_eq_diff,
        diagnostic::{AnyDiagnostic, Diagnostic, Severity},
        label::Label,
        name_resolution::{
            name_resolver::NameResolverError,
            symbol::{EffectId, GlobalId, ParamLocalId, Symbol},
        },
        types::{
            infer_row::RowParamId,
            row::Row,
            scheme::{ForAll, Scheme},
            ty::Ty,
            type_error::TypeError,
            types::TypeEntry,
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

    #[test]
    fn types_handlers() {
        let (_ast, types) = typecheck(
            "
            effect 'fizz(x: Int, y: Bool) -> Int

            @handle 'fizz { a, b in
                0
            }
            ",
        );

        assert_eq!(
            Ty::Int,
            *types
                .get_symbol(&ParamLocalId(3).into())
                .unwrap()
                .as_mono_ty()
        );

        assert_eq!(
            Ty::Bool,
            *types
                .get_symbol(&ParamLocalId(4).into())
                .unwrap()
                .as_mono_ty()
        );
    }

    #[test]
    fn checks_handler_return() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz(x: Int, y: Bool) -> Bool

            @handle 'fizz { a, b in
                0
            }
            ",
        );

        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn checks_handler_args() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz(x: Int, y: Bool) -> Bool

            @handle 'fizz { a in
                true
            }
            ",
        );

        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn continue_in_handler_uses_effect_return_type() {
        let (_ast, _types) = typecheck(
            "
            effect 'fizz() -> Int

            @handle 'fizz {
                continue 123
            }
            ",
        );
    }

    #[test]
    fn continue_in_handler_checks_return_type() {
        let (.., diagnostics) = typecheck_err(
            "
            effect 'fizz() -> Int

            @handle 'fizz {
                continue true
            }
            ",
        );

        assert!(
            diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::InvalidUnification(..),
                    ..
                })
            )),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn continue_with_value_outside_handler_errors() {
        let (.., diagnostics) = typecheck_err("continue 1");

        assert!(
            diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::Typing(Diagnostic {
                    kind: TypeError::ContinueOutsideHandler,
                    ..
                })
            )),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn dupe_handlers_warn() {
        let (.., diagnostics) = typecheck_err(
            "
                effect 'fizz() -> Int

                @handle 'fizz { continue 0 }
                @handle 'fizz { continue 1 }

                'fizz()
                ",
        );

        assert!(
            diagnostics.iter().any(|diag| matches!(
                diag,
                AnyDiagnostic::NameResolution(Diagnostic {
                    severity: Severity::Warn,
                    kind: NameResolverError::ShadowedEffectHandler(_),
                    ..
                })
            )),
            "{diagnostics:?}",
        );
    }

    #[test]
    fn handler_removes_effect_from_enclosing_func() {
        let (_ast, _types, diagnostics) = typecheck_err(
            "
          effect 'fizz() -> Int

          func fizzes() '[] {
            @handle 'fizz { continue 123 }

            'fizz()
          }
        ",
        );

        assert_eq!(0, diagnostics.len(), "{diagnostics:?}");
    }
}
