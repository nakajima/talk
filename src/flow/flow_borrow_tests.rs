//! Flow-checker borrow/provenance/capture tests: the remainder of the
//! ported legacy suite, with byte-identical sources so parity is
//! auditable.

use crate::compiling::driver::{Driver, DriverConfig, Source, Typed};
use crate::diagnostic::AnyDiagnostic;

fn flow_driver(source: &str) -> Driver<Typed> {
    Driver::new(
        vec![Source::from(source)],
        DriverConfig::new("FlowBorrowTest"),
    )
    .parse()
    .expect("parse failed")
    .resolve_names()
    .expect("name resolution failed")
    .type_check()
}

fn flow_errors(source: &str) -> Vec<String> {
    flow_driver(source)
        .phase
        .diagnostics
        .iter()
        .filter_map(|diagnostic| match diagnostic {
            AnyDiagnostic::Ownership(diag) => Some(diag.kind.to_string()),
            _ => None,
        })
        .collect()
}

fn assert_no_errors(source: &str) {
    let errors = flow_errors(source);
    assert!(errors.is_empty(), "expected no flow errors, got {errors:?}");
}

fn assert_error_contains(source: &str, needle: &str) {
    let errors = flow_errors(source);
    assert!(
        errors.iter().any(|error| error.contains(needle)),
        "expected an error containing {needle:?}, got {errors:?}"
    );
}

fn assert_no_error_contains(source: &str, needle: &str) {
    let errors = flow_errors(source);
    assert!(
        !errors.iter().any(|error| error.contains(needle)),
        "expected no error containing {needle:?}, got {errors:?}"
    );
}

// ----- Borrowed-storage / classification -------------------------------------

#[test]
fn allows_borrowed_field_in_struct_type() {
    assert_no_errors("struct View {\n\tlet path: Substring\n}");
}

#[test]
fn allows_borrowed_payload_in_enum_type() {
    assert_no_errors("enum View {\n\tcase path(Substring)\n}");
}

#[test]
fn rejects_borrowed_global() {
    assert_error_contains(
        "let path = \"hello\".utf8().slice(0, 1)",
        "cannot be stored in global 'path'",
    );
}

#[test]
fn allows_character_literal_global() {
    // Character is a borrowed view, but a literal points into static data.
    assert_no_errors("let newline = '\\n'\nlet lambda = 'λ'\nprint(newline)\nprint(lambda)");
}

#[test]
fn allows_global_iterator_over_global_array() {
    // A borrow-wrapping global is fine when its loans are rooted in other
    // globals: both live for the whole program, and reassignment of the
    // owner is rejected program-wide (see the test below).
    assert_no_errors("let numbers = [1, 2, 3]\nlet it = numbers.iter()\nprint(it.next())");
}

#[test]
fn rejects_function_assigning_a_globally_borrowed_global() {
    // The dangling hole the global-rooted allowance would otherwise open:
    // a function reassigns the owner between top-level uses of the
    // borrower. The assignment itself is the error.
    assert_error_contains(
        "let numbers = [1, 2, 3]\nlet it = numbers.iter()\nfunc stomp() {\n\tnumbers = [9]\n}\nstomp()\nprint(it.next())",
        "borrow",
    );
}

#[test]
fn rejects_borrow_typed_struct_field() {
    assert_error_contains("struct Holder {\n\tlet r: &String\n}", "cannot be stored");
}

#[test]
fn rejects_borrow_typed_enum_payload() {
    assert_error_contains("enum Holder {\n\tcase r(&String)\n}", "cannot be stored");
}

#[test]
fn allows_function_typed_field_with_borrow_params() {
    // A function value whose signature mentions borrows is not itself a
    // stored borrow.
    assert_no_errors("struct Mapper {\n\tlet f: (&String) -> Int\n}");
}

#[test]
fn mut_method_on_shared_borrowing_struct_keeps_its_loan() {
    // it.next() mutates the iterator's cursor, not the array it borrows:
    // an exclusive touch of the borrower is capped at the loan's shared
    // kind, so it must not invalidate the iterator's own borrow.
    assert_no_errors(
        "func main() -> Int {\n\tlet numbers = [7, 8]\n\tlet it = numbers.iter()\n\tlet r1 = it.next()\n\tlet r2 = it.next()\n\t0\n}",
    );
}

#[test]
fn two_shared_iterators_over_one_array_coexist() {
    assert_no_errors(
        "func main() -> Int {\n\tlet numbers = [7, 8]\n\tlet it = numbers.iter()\n\tlet it2 = numbers.iter()\n\tlet r1 = it.next()\n\tlet r2 = it2.next()\n\t0\n}",
    );
}

// ----- Unique types -------------------------------------------------------------

#[test]
fn unique_parameter_value_moves_like_owned() {
    assert_error_contains(
        "func bad(consume x: *String) -> Int {\n\tlet y = x\n\tx.byte_count\n}",
        "Use of moved value 'x'",
    );
}

#[test]
fn owned_argument_satisfies_unique_parameter() {
    assert_no_errors(
        "func take(x: *String) -> Int {\n\tx.byte_count\n}\nfunc ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}",
    );
}

// ----- Provenance / returns ---------------------------------------------------

#[test]
fn returning_borrow_through_expression_match() {
    assert_no_errors(
        "func first(s: &String, flag: Bool) -> Substring {\n\tlet v = s.utf8()\n\tmatch flag {\n\t\ttrue -> v.slice(0, 1),\n\t\tfalse -> v.slice(1, 1)\n\t}\n}",
    );
    assert_error_contains(
        "func bad(flag: Bool) -> Substring {\n\tlet s = \"hello\" + \" world\"\n\tmatch flag {\n\t\ttrue -> s.utf8().slice(0, 1),\n\t\tfalse -> s.utf8().slice(1, 1)\n\t}\n}",
        "owned by this function",
    );
}

#[test]
fn rejects_returning_substring_of_local_owned_value() {
    assert_error_contains(
        "func bad() -> Substring {\n\tlet s = \"hello\" + \" world\"\n\ts.utf8().slice(0, 1)\n}",
        "owned by this function",
    );
}

#[test]
fn rejects_returning_substring_of_owned_parameter() {
    assert_error_contains(
        "func first(consume s: String) -> Substring {\n\ts.utf8().slice(0, 1)\n}",
        "owned by this function",
    );
}

#[test]
fn allows_returning_substring_of_borrowed_parameter() {
    assert_no_errors("func first(s: &String) -> Substring {\n\ts.utf8().slice(0, 1)\n}");
}

#[test]
fn rejects_returning_struct_wrapping_local_substring() {
    // A struct with a Borrowed-marked field is itself borrow-containing:
    // wrapping a local's substring must not smuggle it past the return check.
    assert_error_contains(
        "struct Wrapper {\n\tlet sub: Substring\n}\nfunc make() -> Wrapper {\n\tlet s = \"ab\" + \"cd\"\n\tWrapper(sub: s.utf8().slice(0, 2))\n}",
        "owned by this function",
    );
}

#[test]
fn rejects_returning_enum_wrapping_local_substring() {
    assert_error_contains(
        "enum View {\n\tcase path(Substring)\n}\nfunc make() -> View {\n\tlet s = \"ab\" + \"cd\"\n\tView.path(s.utf8().slice(0, 2))\n}",
        "owned by this function",
    );
}

#[test]
fn protocol_default_method_receiver_is_borrowed_param() {
    // The implicit receiver of a protocol default method is `&Self`, so a
    // borrow derived from it is parameter-derived provenance (core's
    // Iterator.map returns a struct wrapping the receiver this way).
    assert_no_errors(
        "protocol P {\n\tfunc name() -> &String\n\tfunc first() -> Substring {\n\t\tself.name().utf8().slice(0, 1)\n\t}\n}",
    );
}

#[test]
fn allows_returning_struct_wrapping_substring_of_borrowed_parameter() {
    assert_no_errors(
        "struct Wrapper {\n\tlet sub: Substring\n}\nfunc make(s: &String) -> Wrapper {\n\tWrapper(sub: s.utf8().slice(0, 2))\n}",
    );
}

#[test]
fn ordinary_borrowed_return_tracks_single_borrowed_argument_owner() {
    assert_error_contains(
        "func first(s: &String) -> Substring {\n\ts.utf8().slice(0, 1)\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = first(s)\n\tlet moved = s\n\tsub.byte_count\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn borrow_of_one_argument_stays_precise_when_another_is_moved() {
    assert_no_errors(
        "func choose(a: &String, b: &String) -> Substring {\n\ta.utf8().slice(0, 1)\n}\nfunc ok() -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = choose(a, b)\n\tlet moved = b\n\tsub.byte_count\n}",
    );
}

#[test]
fn borrow_of_one_argument_still_rejects_moving_that_argument() {
    assert_error_contains(
        "func choose(a: &String, b: &String) -> Substring {\n\ta.utf8().slice(0, 1)\n}\nfunc bad() -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = choose(a, b)\n\tlet moved = a\n\tsub.byte_count\n}",
        "borrowed value 'sub'",
    );
}

#[test]
fn ordinary_borrowed_return_from_owned_local_cannot_escape() {
    assert_error_contains(
        "func first(s: &String) -> Substring {\n\ts.utf8().slice(0, 1)\n}\nfunc bad() -> Substring {\n\tlet s = \"hello\" + \" world\"\n\tfirst(s)\n}",
        "owned by this function",
    );
}

#[test]
fn ordinary_borrowed_return_can_escape_borrowed_parameter() {
    assert_no_errors(
        "func first(s: &String) -> Substring {\n\ts.utf8().slice(0, 1)\n}\nfunc ok(s: &String) -> Substring {\n\tfirst(s)\n}",
    );
}

// ----- Inferred params are borrows (ownership plan 3.3(b)) -------------------

#[test]
fn inferred_param_caller_reuses_argument_after_call() {
    // `func peek(x)` is `func peek(x: String)`'s twin: the call borrows,
    // so the caller can keep using `s` afterward.
    assert_no_errors(
        "func peek(x) -> Int {\n\tx.byte_count\n}\nlet s = \"a\" + \"b\"\nlet n = peek(s)\nlet m = s.byte_count\nprint(n + m)",
    );
}

#[test]
fn inferred_consume_param_still_consumes() {
    // The stamped mode is the authority: `consume x` without an annotation
    // keeps owned-parameter semantics, so the caller's later use errors.
    assert_error_contains(
        "func eat(consume x) -> Int {\n\t0\n}\nlet s = \"a\" + \"b\"\nlet n = eat(s)\nlet m = s.byte_count\nprint(n + m)",
        "Use of moved value 's'",
    );
}

#[test]
fn consume_marker_against_inferred_borrow_param_is_rejected() {
    // Call-site `consume` against a borrow-mode parameter is a contract
    // conflict for annotated params; the inferred twin must agree.
    assert_error_contains(
        "func peek(x) -> Int {\n\tx.byte_count\n}\nlet s = \"a\" + \"b\"\nlet n = peek(consume s)\nprint(n)",
        "the parameter borrows",
    );
}

#[test]
fn borrowed_return_among_several_arguments_is_precisely_provenanced() {
    assert_no_errors(
        "func choose(a: &String, b: &String) -> Substring {\n\ta.utf8().slice(0, 1)\n}\nfunc bad() -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = choose(a, b)\n\tsub.byte_count\n}",
    );
}

#[test]
fn rejects_returning_tuple_containing_local_borrow() {
    assert_error_contains(
        "func bad() -> (Substring, Int) {\n\tlet s = \"hello\" + \" world\"\n\t(s.utf8().slice(0, 1), 1)\n}",
        "owned by this function",
    );
}

#[test]
fn record_containing_borrow_tracks_owner_invalidation() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet record = { sub: s.utf8().slice(0, 1) }\n\tlet moved = s\n\trecord.sub.byte_count\n}",
        "Cannot move 's' while it is borrowed as 'record'",
    );
}

#[test]
fn generic_container_containing_borrow_tracks_owner_invalidation() {
    assert_error_contains(
        "enum Maybe<T> {\n\tcase some(T)\n\tcase none\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet maybe = Maybe.some(s.utf8().slice(0, 1))\n\tlet moved = s\n\tmatch maybe {\n\t\t.some(sub) -> sub.byte_count,\n\t\t.none -> 0\n\t}\n}",
        "Use of borrowed value 'maybe'",
    );
}

#[test]
fn rejects_returning_owned_generic_container_containing_borrow() {
    assert_error_contains(
        "enum Maybe<T> {\n\tcase some(T)\n\tcase none\n}\nfunc bad() -> Maybe<Substring> {\n\tlet s = \"hello\" + \" world\"\n\tMaybe.some(s.utf8().slice(0, 1))\n}",
        "owned by this function",
    );
}

// ----- Move-out-of-borrowed ----------------------------------------------------
//
// Tier 2: extracting a CheapClone value from a borrow clones it silently (an
// O(1) buffer retain); only non-CheapClone extraction still moves out.

#[test]
fn clones_returning_cheap_clone_field_from_shared_borrow() {
    assert_no_errors(
        "struct Person {\n\tlet name: String\n}\nfunc ok(person: &Person) -> String {\n\tperson.name\n}",
    );
}

#[test]
fn clones_binding_cheap_clone_field_from_shared_borrow() {
    assert_no_errors(
        "struct Person {\n\tlet name: String\n}\nfunc ok(person: &Person) -> Int {\n\tlet name = person.name\n\tname.byte_count\n}",
    );
}

#[test]
fn clones_passing_cheap_clone_field_from_shared_borrow_by_value() {
    assert_no_errors(
        "struct Person {\n\tlet name: String\n}\nfunc take(name: String) -> Int {\n\tname.byte_count\n}\nfunc ok(person: &Person) -> Int {\n\ttake(person.name)\n}",
    );
}

#[test]
fn rejects_returning_non_cheap_clone_field_from_shared_borrow() {
    assert_error_contains(
        "struct Name {\n\tlet value: String\n}\nstruct Person {\n\tlet name: Name\n}\nfunc bad(person: &Person) -> Name {\n\tperson.name\n}",
        "out of borrowed value 'person'",
    );
}

#[test]
fn rejects_binding_non_cheap_clone_field_from_shared_borrow() {
    assert_error_contains(
        "struct Name {\n\tlet value: String\n}\nstruct Person {\n\tlet name: Name\n}\nfunc bad(person: &Person) -> Int {\n\tlet name = person.name\n\t0\n}",
        "out of borrowed value 'person'",
    );
}

#[test]
fn allows_copy_field_read_from_shared_borrow() {
    assert_no_errors(
        "struct Person {\n\tlet age: Int\n}\nfunc ok(person: &Person) -> Int {\n\tperson.age\n}",
    );
}

#[test]
fn clones_cheap_clone_field_extraction_from_borrowed_nominal() {
    // ByteStorage is CheapClone: extracting it from a borrowed Substring
    // retains the refcounted buffer instead of moving out.
    assert_no_errors("func ok(sub: Substring) -> Int {\n\tlet storage = sub.storage\n\t0\n}");
}

#[test]
fn coerces_borrowed_cheap_clone_argument_to_owned_parameter() {
    let typed = flow_driver(
        "func take(s: String) -> Int {\n\ts.byte_count\n}\nfunc ok(s: &String) -> Int {\n\ttake(s)\n}",
    );
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
}

#[test]
fn cheap_clone_extraction_runs_on_vm_without_double_free() {
    // The clone retains the shared buffer; dropping both the owner and the
    // clone releases it twice. A missing retain double-frees (VM error).
    let source = "struct Person {\n\tlet name: String\n}\nfunc extract(person: &Person) -> String {\n\tperson.name\n}\nfunc check() -> Int {\n\tlet p = Person(name: \"hello\" + \" world\")\n\tlet n = extract(p)\n\tn.byte_count\n}\ncheck()";
    let typed = flow_driver(source);
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let value = lowered.run_vm().expect("vm");
    match value {
        crate::vm::interp::Value::I64(n) => assert_eq!(n, 11),
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn cow_write_to_shared_buffer_preserves_value_semantics() {
    // items2 shares h.items' buffer (tier-2 clone = retain). Writing
    // through items2 must copy the shared buffer first, leaving h.items
    // untouched: 1 * 100 + 99, not 99 * 100 + 99.
    let source = "struct Holder {\n\tlet items: Array<Int>\n}\nfunc get_items(h: &Holder) -> Array<Int> {\n\th.items\n}\nfunc check() -> Int {\n\tlet arr = [1, 2, 3]\n\tlet h = Holder(items: arr)\n\tlet items2 = get_items(h)\n\titems2.set(0, 99)\n\th.items.get(0) * 100 + (items2.get(0) + 0)\n}\ncheck()";
    let typed = flow_driver(source);
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let value = lowered.run_vm().expect("vm");
    match value {
        crate::vm::interp::Value::I64(n) => assert_eq!(n, 199, "the write must not alias h.items"),
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn cheap_clone_extraction_leaks_nothing() {
    let source = "struct Person {\n\tlet name: String\n}\nfunc extract(person: &Person) -> String {\n\tperson.name\n}\nfunc check() -> Int {\n\tlet p = Person(name: \"hello\" + \" world\")\n\tlet n = extract(p)\n\tn.byte_count\n}\ncheck()";
    let typed = flow_driver(source);
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let mut evaluator = crate::lambda_g::eval::Evaluator::new();
    let value = evaluator
        .run_main(
            &mut lowered.phase.program,
            lowered.phase.main,
            lowered.phase.result_ty,
        )
        .expect("eval");
    assert_eq!(
        value,
        crate::lambda_g::eval::EvalValue::I64(11),
        "unexpected result"
    );
    assert_eq!(
        evaluator.live_allocations(),
        0,
        "every allocation should be released by scope-exit drops"
    );
}

#[test]
fn rejects_borrowed_non_cheap_clone_argument_to_owned_parameter() {
    let typed = flow_driver(
        "struct Name {\n\tlet value: String\n}\nfunc take(consume name: Name) -> Int {\n\t0\n}\nfunc bad(name: &Name) -> Int {\n\ttake(name)\n}",
    );
    assert!(typed.has_errors(), "expected a type error");
}

// ----- ADR 0025 / plan S3: payload binders under borrowed scrutinees ---------
//
// A variant payload binder under a borrowed scrutinee carries the
// borrow-erased surface type; ownership lives in `borrowed_roots` instead.
// The move-out-of-borrow judgment must consult that registration for ROOT
// places too — otherwise consuming the binder records a genuine move and the
// caller's enum frees the same payload again.

#[test]
fn rejects_returning_non_cheap_clone_payload_binder_from_borrowed_scrutinee() {
    assert_error_contains(
        "struct Name {\n\tlet value: String\n}\nenum E {\n\tcase a(Name)\n}\nfunc steal(e: E) -> Name {\n\tmatch e {\n\t\t.a(n) -> n\n\t}\n}",
        "out of borrowed value",
    );
}

#[test]
fn rejects_storing_non_cheap_clone_payload_binder_into_owned_struct() {
    assert_error_contains(
        "struct Name {\n\tlet value: String\n}\nstruct Holder {\n\tlet name: Name\n}\nenum E {\n\tcase a(Name)\n}\nfunc hold(e: E) -> Int {\n\tlet h = match e {\n\t\t.a(n) -> Holder(name: n)\n\t}\n\th.name.value.byte_count\n}",
        "out of borrowed value",
    );
}

#[test]
fn rejects_tuple_nested_payload_binder_consume_from_borrowed_scrutinee() {
    assert_error_contains(
        "struct Name {\n\tlet value: String\n}\nenum E {\n\tcase a(Name)\n}\nfunc first(x: E, y: E) -> Name {\n\tmatch (x, y) {\n\t\t(.a(n), _) -> n\n\t}\n}",
        "out of borrowed value",
    );
}

#[test]
fn rejects_consume_argument_of_payload_binder_from_borrowed_scrutinee() {
    assert_error_contains(
        "struct Name {\n\tlet value: String\n}\nenum E {\n\tcase a(Name)\n}\nfunc eat(consume name: Name) -> Int {\n\t0\n}\nfunc go(e: E) -> Int {\n\tmatch e {\n\t\t.a(n) -> eat(consume n)\n\t}\n}",
        "out of borrowed value",
    );
}

#[test]
fn rejects_consume_argument_of_cheap_clone_payload_binder_from_borrowed_scrutinee() {
    // `consume` disables the tier-2 clone (ADR 0018): a forced move out of
    // borrowed storage errors even for a CheapClone payload.
    assert_error_contains(
        "enum E {\n\tcase a(String)\n}\nfunc eat(consume s: String) -> Int {\n\ts.byte_count\n}\nfunc go(e: E) -> Int {\n\tmatch e {\n\t\t.a(s) -> eat(consume s)\n\t}\n}",
        "out of borrowed value",
    );
}

#[test]
fn clones_cheap_clone_payload_binder_returned_from_borrowed_scrutinee() {
    // Tier 2: a String payload consumed through the binder retains instead
    // of moving out of the caller's enum.
    assert_no_errors(
        "enum E {\n\tcase a(String)\n}\nfunc steal(e: E) -> String {\n\tmatch e {\n\t\t.a(s) -> s\n\t}\n}",
    );
}

#[test]
fn generic_payload_binder_from_borrowed_self_rejects_non_cheap_instantiation() {
    // The generic body checks clean (the tier-2 mark defers to θ); an
    // owned non-CheapClone instantiation must be a loud lowering error,
    // never a silent move out of the borrowed receiver.
    let typed = flow_driver(
        "struct Name {\n\tlet value: String\n}\nenum Fizz<T> {\n\tcase foo(T)\n\n\tfunc unwrap() -> T {\n\t\tmatch self {\n\t\t\t.foo(t) -> t\n\t\t}\n\t}\n}\nfunc go() -> Int {\n\tlet f = Fizz.foo(Name(value: \"x\" + \"y\"))\n\tlet n = f.unwrap()\n\tn.value.byte_count\n}\ngo()",
    );
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let lowered = typed.lower();
    assert!(
        lowered
            .phase
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("CheapClone")),
        "expected a lowering rejection for the non-CheapClone instantiation, got {:?}",
        lowered.phase.diagnostics
    );
}

// ----- Borrow conflicts / invalidation ------------------------------------------

#[test]
fn rejects_borrow_use_after_owner_move() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\tlet moved = s\n\tsub.byte_count\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn rejects_borrow_use_after_owner_reassignment() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\ts = \"new\" + \" value\"\n\tsub.byte_count\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn rejects_borrow_use_after_owner_reassignment_across_join() {
    assert_error_contains(
        "func bad(flag: Bool) -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = a.utf8().slice(0, 1)\n\tif flag { sub = b.utf8().slice(0, 1) }\n\ta = \"new\" + \" value\"\n\tsub.byte_count\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn rejects_borrow_use_after_owner_reassignment_across_join_mirror() {
    assert_error_contains(
        "func bad(flag: Bool) -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = a.utf8().slice(0, 1)\n\tif flag { sub = b.utf8().slice(0, 1) }\n\tb = \"new\" + \" value\"\n\tsub.byte_count\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn rejects_reassigned_borrow_use_after_owner_move() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\tsub = s.utf8().slice(1, 1)\n\tlet moved = s\n\tsub.byte_count\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn allows_owner_move_after_borrow_last_use() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\tlet n = sub.byte_count\n\tlet moved = s\n\tn\n}",
    );
}

#[test]
fn rejects_owner_move_while_borrow_has_later_use() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\tlet moved = s\n\tsub.byte_count\n}",
        "Cannot move 's' while it is borrowed as 'sub'",
    );
}

#[test]
fn rejects_match_scrutinee_move_while_borrowed() {
    // Scrutinee consumption happens at the Switch terminator: the check
    // must run in the error pass too, not only the silent fixpoint.
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\tlet n = match s {\n\t\t_ -> 1\n\t}\n\tsub.byte_count + n\n}",
        "Cannot move 's' while it is borrowed as 'sub'",
    );
}

#[test]
fn move_while_mutably_borrowed_does_not_report_spurious_shared_borrow() {
    let source = "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet moved = s\n\tborrow.byte_count\n}";
    assert_error_contains(source, "Cannot move 's' while it is borrowed as 'borrow'");
    assert_no_error_contains(source, "Cannot take shared borrow");
}

#[test]
fn mutable_method_receiver_invalidates_borrows_of_receiver() {
    assert_error_contains(
        "struct Box {\n\tlet value: String\n\tmut func touch() -> Int {\n\t\tself.value.byte_count\n\t}\n}\nfunc bad() -> Int {\n\tlet box = Box(value: \"hello\" + \" world\")\n\tlet sub = box.value.utf8().slice(0, 1)\n\tlet n = box.touch()\n\tsub.byte_count + n\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn shared_method_receiver_cannot_assign_self_field() {
    let errors = flow_errors(
        "struct Counter {\n\tlet n: Int\n\tfunc bump() -> () {\n\t\tself.n = self.n + 1\n\t\t()\n\t}\n}",
    );
    assert!(!errors.is_empty(), "expected a rejection, got none");
}

#[test]
fn mut_method_receiver_can_assign_self_field() {
    assert_no_errors(
        "struct Counter {\n\tlet n: Int\n\tmut func bump() -> () {\n\t\tself.n = self.n + 1\n\t\t()\n\t}\n}",
    );
}

#[test]
fn shared_borrow_ends_at_last_use_before_mutation() {
    assert_no_errors(
        "struct Box {\n\tlet value: String\n\tmut func touch() -> Int {\n\t\tself.value.byte_count\n\t}\n}\nfunc ok() -> Int {\n\tlet box = Box(value: \"hello\" + \" world\")\n\tlet sub = box.value.utf8().slice(0, 1)\n\tlet n = sub.byte_count\n\tbox.touch() + n\n}",
    );
}

#[test]
fn live_shared_borrow_blocks_later_mutation() {
    assert_error_contains(
        "struct Box {\n\tlet value: String\n\tmut func touch() -> Int {\n\t\tself.value.byte_count\n\t}\n}\nfunc bad() -> Int {\n\tlet box = Box(value: \"hello\" + \" world\")\n\tlet sub = box.value.utf8().slice(0, 1)\n\tlet n = box.touch()\n\tsub.byte_count + n\n}",
        "already shared borrowed as 'sub'",
    );
}

#[test]
fn rejects_read_while_mutable_borrow_is_live() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet n = s.byte_count\n\tborrow.byte_count + n\n}",
        "already mutable borrowed as 'borrow'",
    );
}

#[test]
fn mutable_borrow_ends_at_last_use_before_read() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet n = borrow.byte_count\n\ts.byte_count + n\n}",
    );
}

#[test]
fn loop_carried_mutable_borrow_lives_until_storage_dead() {
    assert_error_contains(
        "func observe(s: &String) -> Int {\n\ts.byte_count\n}\nfunc mutate(s: &mut String) -> Int {\n\ts.byte_count\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet r: &mut String = s\n\tlet i = 0\n\tloop i < 2 {\n\t\tlet n = observe(r)\n\t\tlet m = mutate(s)\n\t\ti = i + 1\n\t}\n\t0\n}",
        "already mutable borrowed as 'r'",
    );
}

#[test]
fn per_iteration_mutable_borrow_can_end_before_mutation() {
    assert_no_errors(
        "func observe(s: &String) -> Int {\n\ts.byte_count\n}\nfunc mutate(s: &mut String) -> Int {\n\ts.byte_count\n}\nfunc ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet i = 0\n\tloop i < 2 {\n\t\tlet r: &mut String = s\n\t\tlet n = observe(r)\n\t\tlet m = mutate(s)\n\t\ti = i + 1\n\t}\n\t0\n}",
    );
}

#[test]
fn mutable_call_argument_invalidates_shared_borrow() {
    assert_error_contains(
        "func mutate(s: &mut String) -> Int {\n\ts.byte_count\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\tlet n = mutate(s)\n\tsub.byte_count + n\n}",
        "Use of borrowed value 'sub'",
    );
}

// ----- Captures ------------------------------------------------------------------

#[test]
fn rejects_owned_value_capture_without_capture_mode() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func() -> Int {\n\t\ts.byte_count\n\t}\n}",
        "Cannot capture ownership-sensitive value 's'",
    );
}

#[test]
fn rejects_borrowed_value_capture_without_capture_mode() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.utf8().slice(0, 1)\n\treturn func() -> Int {\n\t\tsub.byte_count\n\t}\n}",
        "Cannot capture ownership-sensitive value 'sub'",
    );
}

#[test]
fn explicit_consuming_capture_moves_parent_value() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [consuming s]() -> Int {\n\t\ts.byte_count\n\t}\n\ts.byte_count\n}",
        "Use of moved value 's'",
    );
}

#[test]
fn explicit_consuming_capture_can_escape() {
    assert_no_errors(
        "func ok() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func [consuming s]() -> Int {\n\t\ts.byte_count\n\t}\n}",
    );
}

#[test]
fn owning_closure_value_copy_moves_source() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [consuming s]() -> Int {\n\t\ts.byte_count\n\t}\n\tlet g = f\n\tf() + g()\n}",
        "Use of moved value 'f'",
    );
}

#[test]
fn capture_free_function_values_remain_copyable() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet f = func() -> Int {\n\t\t1\n\t}\n\tlet g = f\n\tf() + g()\n}",
    );
}

#[test]
fn explicit_copy_capture_requires_copy_type() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func [copy s]() -> Int {\n\t\ts.byte_count\n\t}\n}",
        "copy captures require a copyable type",
    );
}

#[test]
fn unused_explicit_borrow_capture_can_end_before_owner_move() {
    assert_no_errors(
        "func ok() -> String {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&s]() -> Int {\n\t\ts.byte_count\n\t}\n\treturn s\n}",
    );
}

#[test]
fn explicit_borrow_capture_blocks_owner_move_until_closure_last_use() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&s]() -> Int {\n\t\ts.byte_count\n\t}\n\tlet moved = s\n\tf()\n}",
        "Cannot move 's' while it is borrowed as 'f'",
    );
}

#[test]
fn unused_explicit_mut_borrow_capture_can_end_before_read() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&mut s]() -> Int {\n\t\ts.byte_count\n\t}\n\ts.byte_count\n}",
    );
}

#[test]
fn explicit_mut_borrow_capture_blocks_reads_until_closure_last_use() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&mut s]() -> Int {\n\t\ts.byte_count\n\t}\n\tlet n = s.byte_count\n\tf() + n\n}",
        "already mutable borrowed as 'f'",
    );
}

#[test]
fn explicit_borrow_capture_cannot_escape() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func [&s]() -> Int {\n\t\ts.byte_count\n\t}\n}",
        "borrow captures are tied to the current stack frame",
    );
}

#[test]
fn rejects_escaping_generic_capture_returned_through_local() {
    assert_error_contains(
        "func bad<Value>(consume value: Value) -> () -> Value {\n\tlet f = func() -> Value {\n\t\tvalue\n\t}\n\treturn f\n}",
        "Cannot capture ownership-sensitive value 'value'",
    );
}

#[test]
fn rejects_escaping_generic_capture_passed_as_argument() {
    assert_error_contains(
        "func accept<Value>(consume f: () -> Value) -> Int {\n\t0\n}\nfunc bad<Value>(consume value: Value) -> Int {\n\taccept(func() -> Value {\n\t\tvalue\n\t})\n}",
        "Cannot capture ownership-sensitive value 'value'",
    );
}

#[test]
fn rejects_escaping_borrow_capture_even_when_referent_is_copy() {
    // Shared borrows of Copy heads erase at elaboration (`&Int` never
    // surfaces), so the surviving Copy-referent borrow is the exclusive
    // one — the escape check must not have a Copy hole for it.
    assert_error_contains(
        "func bad(value: &mut Int) -> () -> &mut Int {\n\treturn func() -> &mut Int {\n\t\tvalue\n\t}\n}",
        "Cannot capture ownership-sensitive value 'value'",
    );
}

#[test]
fn allows_nonescaping_generic_closure_capture() {
    assert_no_errors(
        "func ok<Value>(value: Value) -> Value {\n\tlet f = func() -> Value {\n\t\tvalue\n\t}\n\tf()\n}",
    );
}

// ----- Call-site ownership markers (ADR 0018) -------------------------------

#[test]
fn consume_marker_forces_a_generic_move() {
    // Without the marker the earlier consume auto-clones (liveness);
    // `consume` disables the clone, so the later use is a moved-value error.
    assert_error_contains(
        "func take<T>(consume x: T) -> Int { 0 }\nfunc f<T>(consume x: T) -> Int {\n\ttake(consume x) + take(x)\n}",
        "Use of moved value 'x'",
    );
}

#[test]
fn generic_early_consume_auto_clones_without_marker() {
    assert_no_errors(
        "func take<T>(consume x: T) -> Int { 0 }\nfunc f<T>(consume x: T) -> Int {\n\ttake(x) + take(x)\n}",
    );
}

#[test]
fn copy_marker_preserves_the_source() {
    // `copy` disables last-use move selection: the source stays live.
    assert_no_errors(
        "func take(consume s: String) -> Int { 0 }\nfunc f(consume s: String) -> Int {\n\tlet a = take(copy s)\n\tlet b = take(s)\n\ta + b\n}",
    );
}

#[test]
fn copy_marker_on_non_cloneable_errors() {
    assert_error_contains(
        "struct Socket 'linear {\n\tlet fd: Int\n}\nfunc close(consume s: Socket) -> Int { 0 }\nfunc f(consume s: Socket) -> Int {\n\tclose(copy s)\n}",
        "copy",
    );
}

#[test]
fn borrow_marker_requires_a_borrowing_parameter() {
    assert_error_contains(
        "func take(consume s: String) -> Int { 0 }\nfunc f(s: String) -> Int {\n\ttake(borrow s)\n}",
        "borrow",
    );
}

#[test]
fn borrow_marker_on_a_borrowing_parameter_is_quiet() {
    assert_no_errors(
        "func read(s: String) -> Int { 0 }\nfunc f(s: String) -> Int {\n\tread(borrow s)\n}",
    );
}

#[test]
fn mut_marker_requires_an_exclusive_parameter() {
    assert_error_contains(
        "struct Counter {\n\tlet count: Int\n}\nfunc read(c: Counter) -> Int {\n\tc.count\n}\nfunc f(mut c: Counter) -> Int {\n\tread(mut c)\n}",
        "mut",
    );
}

#[test]
fn mut_marker_on_an_exclusive_parameter_is_quiet() {
    assert_no_errors(
        "struct Counter {\n\tlet count: Int\n}\nfunc bump(mut c: Counter) -> Int {\n\tc.count = c.count + 1\n\tc.count\n}\nfunc f(mut c: Counter) -> Int {\n\tbump(mut c)\n}",
    );
}

#[test]
fn rejects_rvalue_argument_to_a_mut_parameter() {
    // V1: a `mut` parameter needs an addressable place to write back to.
    assert_error_contains(
        "struct Counter {\n\tlet count: Int\n}\nfunc bump(mut c: Counter) -> Int {\n\tc.count = c.count + 1\n\tc.count\n}\nfunc f() -> Int {\n\tbump(Counter(count: 0))\n}",
        "mutable place",
    );
}

// ----- Iteration/access regression matrix (ADR 0021) --------------------------

/// Every error diagnostic's rendered message, any phase. The matrix cares
/// that a program is rejected; which phase rejects it is an
/// implementation detail (typing catches direct perm mismatches, flow
/// catches place-level upgrades).
fn all_error_messages(source: &str) -> Vec<String> {
    flow_driver(source)
        .phase
        .diagnostics
        .iter()
        .map(|diagnostic| format!("{diagnostic:?}"))
        .collect()
}

fn assert_rejected(source: &str, needle: &str) {
    let errors = all_error_messages(source);
    assert!(
        errors.iter().any(|error| error.contains(needle)),
        "expected a rejection mentioning {needle:?}, got {errors:?}"
    );
}

#[test]
fn borrowed_generic_payload_requires_copy_or_cheap_clone_bound() {
    assert_rejected(
        "struct Item {\n\tlet name: String\n}\nenum Box2<T> {\n\tcase full(T)\n}\nfunc wrap<T>(v: &T) -> Box2<T> {\n\tBox2.full(v)\n}\nfunc main() -> Int {\n\tlet item = Item(name: \"a\" + \"b\")\n\tlet b = wrap(item)\n\t0\n}",
        "Copy or CheapClone",
    );
}

#[test]
fn borrowed_generic_payload_accepts_cheap_clone_bound() {
    let typed = flow_driver(
        "enum Box2<T> {\n\tcase full(T)\n}\nfunc wrap<T: CheapClone>(v: &T) -> Box2<T> {\n\tBox2.full(v)\n}\nfunc main() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet b = wrap(s)\n\t0\n}",
    );
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
}

#[test]
fn allows_mut_receiver_call_through_owned_field_in_mut_func() {
    // `self` is an exclusive place inside a `mut func`; `self.inner` is a
    // projection through that exclusive root, so the nested mutating call
    // is legal.
    assert_no_errors(
        "struct Inner {\n\tlet value: Int\n\tmut func bump() -> Int {\n\t\tself.value = self.value + 1\n\t\tself.value\n\t}\n}\nstruct Outer {\n\tlet inner: Inner\n\tmut func poke() -> Int {\n\t\tself.inner.bump()\n\t}\n}",
    );
}

#[test]
fn rejects_mut_receiver_call_on_shared_borrow_parameter() {
    // A `&Inner` parameter grants shared access only; typing rejects the
    // exclusive receiver directly.
    assert_rejected(
        "struct Inner {\n\tlet value: Int\n\tmut func bump() -> Int {\n\t\tself.value = self.value + 1\n\t\tself.value\n\t}\n}\nfunc f(inner: &Inner) -> Int {\n\tinner.bump()\n}",
        "&mut Inner",
    );
}

#[test]
fn rejects_mut_receiver_call_through_field_of_shared_borrow() {
    // `outer.inner` types as owned `Inner`, so unification cannot see the
    // upgrade; the place's root is a shared borrow, and exclusive access
    // through it must fail at the flow level.
    assert_error_contains(
        "struct Inner {\n\tlet value: Int\n\tmut func bump() -> Int {\n\t\tself.value = self.value + 1\n\t\tself.value\n\t}\n}\nstruct Outer {\n\tlet inner: Inner\n}\nfunc f(outer: &Outer) -> Int {\n\touter.inner.bump()\n}",
        "shared borrow",
    );
}

#[test]
fn rejects_borrowed_loop_element_passed_to_consuming_callback() {
    // The loop element is borrowed from the array; a `consume` callback
    // parameter demands ownership.
    assert_rejected(
        "enum Entry {\n\tcase doc(String)\n}\nfunc drain(entries: Array<Entry>, fn: (consume Entry) -> ()) {\n\tfor entry in entries {\n\t\tfn(entry)\n\t}\n}",
        "Entry",
    );
}

// ----- Borrow-storing structs (ADR 0021 stage 3) ------------------------------

#[test]
fn rejects_borrow_field_in_unmarked_struct() {
    assert_error_contains("struct Ref {\n\tlet inner: &String\n}", "cannot be stored");
}

#[test]
fn borrowed_marker_legalizes_borrow_storing_struct() {
    // A struct that spells its stored borrow and declares itself Borrowed
    // is a borrow-containing value, tracked by provenance like Substring.
    assert_no_errors(
        "struct Ref {\n\tlet inner: &String\n}\nextend Ref: Borrowed {}\nfunc peek(s: &String) -> Int {\n\tlet r = Ref(inner: s)\n\tr.inner.byte_count\n}",
    );
}

#[test]
fn borrowed_marker_struct_cannot_escape_its_loan() {
    // The Ref borrows a local; returning it would dangle. Provenance
    // (not the storage rule — Ref is marked) must reject it.
    assert_error_contains(
        "struct Ref {\n\tlet inner: &String\n}\nextend Ref: Borrowed {}\nfunc escape() -> Ref {\n\tlet s = \"a\" + \"b\"\n\tRef(inner: s)\n}",
        "owned by this function",
    );
}

// ----- Consuming iteration (ADR 0021 stage 6) ---------------------------------

#[test]
fn consume_for_source_used_after_loop_is_rejected() {
    assert_error_contains(
        "func f() -> Int {\n\tlet xs = [1, 2]\n\tfor x in consume xs {\n\t}\n\txs.count\n}",
        "used again",
    );
}

#[test]
fn consume_for_source_through_borrow_is_rejected() {
    assert_error_contains(
        "func f(xs: &Array<Int>) -> Int {\n\tfor x in consume xs {\n\t}\n\t0\n}",
        "borrow",
    );
}

#[test]
fn consume_for_dead_source_is_quiet() {
    assert_no_errors("func f() -> Int {\n\tlet xs = [1, 2]\n\tfor x in consume xs {\n\t}\n\t0\n}");
}

// ----- First-class borrow-typed call results (ADR 0021 prerequisite) ---------

/// No diagnostics of ANY kind (typing included — `assert_no_errors` only
/// filters ownership).
fn assert_clean_all(source: &str) {
    let errors = all_error_messages(source);
    assert!(errors.is_empty(), "expected no diagnostics, got {errors:?}");
}

#[test]
fn borrow_result_binds_against_borrow_annotation() {
    assert_clean_all(
        "func first(xs: &Array<String>) -> Int {\n\tlet e: &String = xs.get(0)\n\t0\n}",
    );
}

#[test]
fn borrow_result_returns_through_borrowed_param() {
    assert_clean_all("func first(xs: &Array<String>) -> &String {\n\txs.get(0)\n}");
}

#[test]
fn generic_borrow_result_binds_against_borrow_annotation() {
    assert_clean_all("func first<T>(xs: &Array<T>) -> Int {\n\tlet e: &T = xs.get(0)\n\t0\n}");
}

#[test]
fn returning_borrow_result_of_local_array_is_rejected() {
    // First-class borrow results still cannot dangle: provenance roots
    // the element borrow in the local array.
    assert_error_contains(
        "func bad() -> &String {\n\tlet xs = [\"a\" + \"b\"]\n\txs.get(0)\n}",
        "owned by this function",
    );
}

// ----- Mutable iteration (ADR 0021 stage 7) -----------------------------------

#[test]
fn mut_for_source_through_borrow_is_rejected() {
    // `for mut` needs exclusive access to the source for the iterator scope.
    assert_rejected(
        "func f(xs: &Array<Int>) -> Int {\n\tfor x in mut xs {\n\t\tx = x + 1\n\t}\n\t0\n}",
        "&Array",
    );
}

#[test]
fn mut_for_over_owned_local_is_quiet() {
    assert_clean_all(
        "func f() -> Int {\n\tlet xs = [1, 2]\n\tfor x in mut xs {\n\t\tx = x + 1\n\t}\n\txs.count\n}",
    );
}

#[test]
fn mut_for_source_can_be_mut_borrowed_after_loop() {
    assert_clean_all(
        "func touch(xs: &mut Array<Int>) -> Int {\n\txs.push(3)\n\txs.count\n}\nfunc f() -> Int {\n\tlet xs = [1, 2]\n\tfor x in mut xs {\n\t\tx = x + 1\n\t}\n\ttouch(xs)\n}",
    );
}

#[test]
fn mut_for_rejects_early_exit_until_commit_is_on_exit() {
    assert_rejected(
        "func f() -> Int {\n\tlet xs = [1, 2]\n\tfor x in mut xs {\n\t\tbreak\n\t}\n\t0\n}",
        "`break`, `continue`, and `return` inside `mut` iteration",
    );
}

// ----- Plan R3: multi-owner provenance folds over all owning loans -----------

#[test]
fn loan_owners_fold_over_every_owning_loan() {
    use crate::flow::loans::{Origin, ProvLoan, Provenance};
    use crate::flow::moves::MoveState;
    use crate::flow::place::Place;
    use crate::name_resolution::symbol::{DeclaredLocalId, Symbol};
    use crate::types::ty::Perm;

    let borrower = Symbol::DeclaredLocal(DeclaredLocalId(1));
    let first = Symbol::DeclaredLocal(DeclaredLocalId(2));
    let second = Symbol::DeclaredLocal(DeclaredLocalId(3));
    let mut state = MoveState::default();
    state.provenances.insert(
        Place::root(borrower),
        Provenance {
            loans: vec![
                ProvLoan {
                    origin: Origin::Local,
                    owner: Some(Place::root(first)),
                    kind: Perm::Exclusive,
                },
                ProvLoan {
                    origin: Origin::Local,
                    owner: Some(Place::root(second)),
                    kind: Perm::Shared,
                },
            ],
        },
    );
    let borrower_place = Place::root(borrower);
    let owners = state.loan_owners_for(&borrower_place);
    assert!(
        owners.iter().any(|owner| *owner == Place::root(first)),
        "first owner missing: {owners:?}"
    );
    assert!(
        owners.iter().any(|owner| *owner == Place::root(second)),
        "a conflict on the second owner would go unseen: {owners:?}"
    );
    // Weakest across owners: one shared owning loan caps an exclusive
    // touch of the borrower to shared.
    assert_eq!(
        state.rebased_perm(&Place::root(borrower), Perm::Exclusive),
        Perm::Shared
    );
}

#[test]
fn rebased_perm_stays_exclusive_when_every_owner_is_exclusive() {
    use crate::flow::loans::{Origin, ProvLoan, Provenance};
    use crate::flow::moves::MoveState;
    use crate::flow::place::Place;
    use crate::name_resolution::symbol::{DeclaredLocalId, Symbol};
    use crate::types::ty::Perm;

    let borrower = Symbol::DeclaredLocal(DeclaredLocalId(1));
    let first = Symbol::DeclaredLocal(DeclaredLocalId(2));
    let second = Symbol::DeclaredLocal(DeclaredLocalId(3));
    let mut state = MoveState::default();
    state.provenances.insert(
        Place::root(borrower),
        Provenance {
            loans: vec![
                ProvLoan {
                    origin: Origin::Local,
                    owner: Some(Place::root(first)),
                    kind: Perm::Exclusive,
                },
                ProvLoan {
                    origin: Origin::Local,
                    owner: Some(Place::root(second)),
                    kind: Perm::Exclusive,
                },
            ],
        },
    );
    assert_eq!(
        state.rebased_perm(&Place::root(borrower), Perm::Exclusive),
        Perm::Exclusive
    );
    assert_eq!(
        state.rebased_perm(&Place::root(borrower), Perm::Shared),
        Perm::Shared
    );
}
