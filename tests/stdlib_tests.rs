#[cfg(test)]
mod optional_tests {
    use talk::{expr::Expr, parser::parse};

    #[test]
    fn gets_parsed() {
        let parsed = parse("let a: Int?", 123);
        let Expr::Let(_, Some(ty)) = parsed.roots()[0].unwrap() else {
            panic!("didn't get let expr");
        };

        assert_eq!(
            *parsed.get(ty).unwrap(),
            Expr::TypeRepr("Optional".into(), vec![0], false)
        );

        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
    }
}

#[cfg(test)]
mod array_tests {
    use talk::{SymbolID, expr::Expr, parser::parse, type_checker::Ty};

    #[test]
    fn gets_parsed() {
        let parsed = parse("[1,2,3]", 123);
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::LiteralArray(vec![0, 1, 2])
        );

        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(*parsed.get(&2).unwrap(), Expr::LiteralInt("3".into()));
    }

    #[test]
    fn gets_typed() {
        let checked = talk::analysis::check("[1,2,3]").unwrap();
        assert_eq!(
            checked.type_for(checked.root_ids()[0]),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])
        );
    }
}
