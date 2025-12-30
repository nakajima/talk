#[cfg(test)]
pub mod tests {
    use crate::{
        label::Label,
        name_resolution::symbol::{EffectId, GlobalId, Symbol},
        types::{
            infer_ty::InferTy, row::Row, ty::Ty, type_session::TypeEntry,
            types_tests::tests::typecheck,
        },
    };

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
            Some(TypeEntry::Mono(Ty::Func(
                Ty::Void.into(),
                Ty::Int.into(),
                Row::Extend {
                    row: Row::Empty.into(),
                    label: Label::_Symbol(EffectId::from(1).into()),
                    ty: Ty::Func(Ty::Void.into(), Ty::Int.into(), Row::Empty.into())
                }
                .into()
            )))
        )
    }
}
