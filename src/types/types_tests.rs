use crate::{
    SymbolTable,
    name_resolver::{NameResolver, Scope},
    parser::parse,
    types::{
        ty::{Primitive, Ty},
        type_checking_session::{TypeCheckingResult, TypeCheckingSession},
    },
};

fn check(code: &'static str) -> TypeCheckingResult {
    let parsed = parse(code, "-");
    let resolved = NameResolver::new(
        Scope::new(crate::builtins::default_name_scope()),
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

#[test]
fn checks_let_with_annotation() {
    let checked = check("let x: Byte = 123; x");
    assert_eq!(Ty::Byte, checked.typed_roots[1].ty)
}

#[test]
fn checks_annotated_func() {
    let checked = check("func(x: Int) -> Int { x }");
    assert_eq!(
        Ty::Func {
            params: vec![Ty::Int],
            returns: Box::new(Ty::Int)
        },
        checked.typed_roots[0].ty
    )
}

#[test]
fn checks_unannotated_func() {
    let checked = check("func() { 123 }");
    assert_eq!(
        Ty::Func {
            params: vec![],
            returns: Box::new(Ty::Int)
        },
        checked.typed_roots[0].ty
    )
}
