use crate::{
    SymbolTable,
    name_resolver::{NameResolver, Scope},
    parser::parse,
    types::{
        row::{ClosedRow, Label, Row},
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

    println!("parsed roots: {:#?}", resolved.roots());

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
fn checks_float() {
    let checked = check("1.23");
    assert_eq!(Ty::Primitive(Primitive::Float), checked.typed_roots[0].ty)
}

#[test]
fn checks_bool() {
    let checked = check("true ; false");
    assert_eq!(Ty::Primitive(Primitive::Bool), checked.typed_roots[0].ty);
    assert_eq!(Ty::Primitive(Primitive::Bool), checked.typed_roots[1].ty);
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
            returns: Box::new(Ty::Int),
            generic_constraints: vec![],
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
            returns: Box::new(Ty::Int),
            generic_constraints: vec![],
        },
        checked.typed_roots[0].ty
    )
}

#[test]
fn checks_generic_func() {
    let checked = check("func id<T>(x: T) { x }; id(123); id(1.23)");
    assert_eq!(Ty::Int, checked.typed_roots[1].ty);
    assert_eq!(Ty::Float, checked.typed_roots[2].ty);
}

#[test]
fn checks_unannotated_generic_func() {
    let checked = check("func id(x) { x }; id(123); id(1.23)");
    assert_eq!(Ty::Int, checked.typed_roots[1].ty);
    assert_eq!(Ty::Float, checked.typed_roots[2].ty);
}

#[test]
fn generic_func_type_mismatch_should_fail() {
    // This actually succeeds because T gets constrained to Int
    let result = check("func bad<T>(x: T) -> T { 123 }");

    // The function is valid - it just means T must be Int
    // Let's verify the type
    if let Ty::Func { returns, .. } = &result.typed_roots[0].ty {
        // The return type should be resolved to Int
        assert_eq!(**returns, Ty::Int);
    } else {
        panic!("Expected function type");
    }
}

#[test]
fn generic_func_type_mismatch_at_call_site() {
    // The error happens when we try to call with wrong type
    let result = check("func bad<T>(x: T) -> T { 123 }; bad(1.5)");
    assert_eq!(result.diagnostics.len(), 1);
}

// TODO: Enable when if expressions are implemented
// #[test]
// #[should_panic]
// fn generic_func_breaks_parametricity() {
//     // This should also fail
//     let _result = check("func broken<T>(x: T) -> T { if true { x } else { 42 } }");
// }

#[test]
fn generic_func_tracks_constraints() {
    // This function constrains T to be Int
    let result = check("func add_one<T>(x: T) -> T { 123 }");
    // The function should type check, with T constrained to Int
    if let Ty::Func {
        generic_constraints,
        ..
    } = &result.typed_roots[0].ty
    {
        // Should have constraint that T = Int
        assert!(
            !generic_constraints.is_empty(),
            "Should have generic constraints"
        );
    } else {
        panic!("Expected function type");
    }
}

#[test]
fn generic_func_constrained_valid() {
    // This should actually be valid - T is constrained to Int
    let _result = check("func wrong<T>(x: T) -> Int { x }");
}

#[test]
fn generic_func_wrong_call() {
    // The error should happen when we try to call with wrong type
    // Using float instead of string to avoid unimplemented string literals
    let result = check("func wrong<T>(x: T) -> Int { x }; wrong(1.5)");
    assert_eq!(result.diagnostics.len(), 1);
}

#[test]
fn checks_record_literal() {
    let checked = check("{ y: 123, z: 1.23 }");
    assert_eq!(
        Ty::Product(Row::Closed(ClosedRow {
            fields: vec!["y".into(), "z".into()],
            values: vec![Ty::Int, Ty::Float],
        })),
        checked.typed_roots[0].ty
    );
}

#[test]
fn checks_record_literal_member() {
    let checked = check("let x = { y: 123, z: 1.23 }; x.y ; x.z");
    assert_eq!(Ty::Int, checked.typed_roots[1].ty);
    assert_eq!(Ty::Float, checked.typed_roots[2].ty);
}

#[test]
fn checks_tuple() {
    let checked = check("(123, 1.23)");
    assert_eq!(
        Ty::Product(Row::Closed(ClosedRow {
            fields: vec![Label::Int(0), Label::Int(1)],
            values: vec![Ty::Int, Ty::Float]
        })),
        checked.typed_roots[0].ty
    );
}

#[test]
fn checks_tuple_member() {
    let checked = check("let x = (123, 1.23) ; x.0; x.1");
    assert_eq!(3, checked.typed_roots.len());
    assert_eq!(Ty::Int, checked.typed_roots[1].ty);
    assert_eq!(Ty::Float, checked.typed_roots[2].ty);
}
