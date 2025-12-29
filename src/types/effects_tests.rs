#[cfg(test)]
pub mod tests {
    use crate::{
        name_resolution::symbol::{GlobalId, Symbol},
        types::{ty::Ty, type_session::TypeEntry, types_tests::tests::typecheck},
    };

    #[test]
    fn types_func_with_effect() {
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
            Some(TypeEntry::Mono(Ty::Func(Ty::Void.into(), Ty::Int.into())))
        )
    }
}
