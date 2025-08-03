use crate::{
    SymbolTable, builtins,
    name_resolver::NameResolver,
    parser::parse,
    types::{
        ty::{Primitive, Ty},
        type_checking_session::{TypeCheckingResult, TypeCheckingSession},
    },
};

fn check(code: &'static str) -> TypeCheckingResult {
    let parsed = parse(code, "-");
    let resolved = NameResolver::new(
        Default::default(),
        Default::default(),
        "-",
        &Default::default(),
    )
    .resolve(parsed, &mut SymbolTable::base());
    let meta = resolved.meta.borrow();
    let mut session = TypeCheckingSession::new(resolved.roots(), &meta);

    session.solve().unwrap()
}

#[test]
fn checks_int() {
    let checked = check("123");
    assert_eq!(Ty::Primitive(Primitive::Int), checked.typed_roots[0].ty)
}

#[test]
fn checks_let() {
    let checked = check("let x = 123; x");
    assert_eq!(Ty::Primitive(Primitive::Int), checked.typed_roots[1].ty)
}
