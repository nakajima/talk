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
        "let path = \"hello\".slice(0, 1)",
        "cannot be stored in global 'path'",
    );
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
        "func bad(x: *String) -> Int {\n\tlet y = x\n\tx.length\n}",
        "Use of moved value 'x'",
    );
}

#[test]
fn owned_argument_satisfies_unique_parameter() {
    assert_no_errors(
        "func take(x: *String) -> Int {\n\tx.length\n}\nfunc ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}",
    );
}

// ----- Provenance / returns ---------------------------------------------------

#[test]
fn rejects_returning_substring_of_local_owned_value() {
    assert_error_contains(
        "func bad() -> Substring {\n\tlet s = \"hello\" + \" world\"\n\ts.slice(0, 1)\n}",
        "owned by this function",
    );
}

#[test]
fn rejects_returning_substring_of_owned_parameter() {
    assert_error_contains(
        "func first(s: String) -> Substring {\n\ts.slice(0, 1)\n}",
        "owned by this function",
    );
}

#[test]
fn allows_returning_substring_of_borrowed_parameter() {
    assert_no_errors("func first(s: &String) -> Substring {\n\ts.slice(0, 1)\n}");
}

#[test]
fn rejects_returning_struct_wrapping_local_substring() {
    // A struct with a Borrowed-marked field is itself borrow-containing:
    // wrapping a local's substring must not smuggle it past the return check.
    assert_error_contains(
        "struct Wrapper {\n\tlet sub: Substring\n}\nfunc make() -> Wrapper {\n\tlet s = \"ab\" + \"cd\"\n\tWrapper(sub: s.slice(0, 2))\n}",
        "owned by this function",
    );
}

#[test]
fn rejects_returning_enum_wrapping_local_substring() {
    assert_error_contains(
        "enum View {\n\tcase path(Substring)\n}\nfunc make() -> View {\n\tlet s = \"ab\" + \"cd\"\n\tView.path(s.slice(0, 2))\n}",
        "owned by this function",
    );
}

#[test]
fn protocol_default_method_receiver_is_borrowed_param() {
    // The implicit receiver of a protocol default method is `&Self`, so a
    // borrow derived from it is parameter-derived provenance (core's
    // Iterator.map returns a struct wrapping the receiver this way).
    assert_no_errors(
        "protocol P {\n\tfunc name() -> &String\n\tfunc first() -> Substring {\n\t\tself.name().slice(0, 1)\n\t}\n}",
    );
}

#[test]
fn allows_returning_struct_wrapping_substring_of_borrowed_parameter() {
    assert_no_errors(
        "struct Wrapper {\n\tlet sub: Substring\n}\nfunc make(s: &String) -> Wrapper {\n\tWrapper(sub: s.slice(0, 2))\n}",
    );
}

#[test]
fn ordinary_borrowed_return_tracks_single_borrowed_argument_owner() {
    assert_error_contains(
        "func first(s: &String) -> Substring {\n\ts.slice(0, 1)\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = first(s)\n\tlet moved = s\n\tsub.length\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn borrow_of_one_argument_stays_precise_when_another_is_moved() {
    assert_no_errors(
        "func choose(a: &String, b: &String) -> Substring {\n\ta.slice(0, 1)\n}\nfunc ok() -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = choose(a, b)\n\tlet moved = b\n\tsub.length\n}",
    );
}

#[test]
fn borrow_of_one_argument_still_rejects_moving_that_argument() {
    assert_error_contains(
        "func choose(a: &String, b: &String) -> Substring {\n\ta.slice(0, 1)\n}\nfunc bad() -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = choose(a, b)\n\tlet moved = a\n\tsub.length\n}",
        "borrowed value 'sub'",
    );
}

#[test]
fn ordinary_borrowed_return_from_owned_local_cannot_escape() {
    assert_error_contains(
        "func first(s: &String) -> Substring {\n\ts.slice(0, 1)\n}\nfunc bad() -> Substring {\n\tlet s = \"hello\" + \" world\"\n\tfirst(s)\n}",
        "owned by this function",
    );
}

#[test]
fn ordinary_borrowed_return_can_escape_borrowed_parameter() {
    assert_no_errors(
        "func first(s: &String) -> Substring {\n\ts.slice(0, 1)\n}\nfunc ok(s: &String) -> Substring {\n\tfirst(s)\n}",
    );
}

#[test]
fn borrowed_return_among_several_arguments_is_precisely_provenanced() {
    assert_no_errors(
        "func choose(a: &String, b: &String) -> Substring {\n\ta.slice(0, 1)\n}\nfunc bad() -> Int {\n\tlet a = \"hello\" + \" world\"\n\tlet b = \"bye\" + \" now\"\n\tlet sub = choose(a, b)\n\tsub.length\n}",
    );
}

#[test]
fn rejects_returning_tuple_containing_local_borrow() {
    assert_error_contains(
        "func bad() -> (Substring, Int) {\n\tlet s = \"hello\" + \" world\"\n\t(s.slice(0, 1), 1)\n}",
        "owned by this function",
    );
}

#[test]
fn record_containing_borrow_tracks_owner_invalidation() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet record = { sub: s.slice(0, 1) }\n\tlet moved = s\n\trecord.sub.length\n}",
        "Cannot move 's' while it is borrowed as 'record'",
    );
}

#[test]
fn generic_container_containing_borrow_tracks_owner_invalidation() {
    assert_error_contains(
        "enum Maybe<T> {\n\tcase some(T)\n\tcase none\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet maybe = Maybe.some(s.slice(0, 1))\n\tlet moved = s\n\tmatch maybe {\n\t\t.some(sub) -> sub.length,\n\t\t.none -> 0\n\t}\n}",
        "Use of borrowed value 'maybe'",
    );
}

#[test]
fn rejects_returning_owned_generic_container_containing_borrow() {
    assert_error_contains(
        "enum Maybe<T> {\n\tcase some(T)\n\tcase none\n}\nfunc bad() -> Maybe<Substring> {\n\tlet s = \"hello\" + \" world\"\n\tMaybe.some(s.slice(0, 1))\n}",
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
        "struct Person {\n\tlet name: String\n}\nfunc ok(person: &Person) -> Int {\n\tlet name = person.name\n\tname.length\n}",
    );
}

#[test]
fn clones_passing_cheap_clone_field_from_shared_borrow_by_value() {
    assert_no_errors(
        "struct Person {\n\tlet name: String\n}\nfunc take(name: String) -> Int {\n\tname.length\n}\nfunc ok(person: &Person) -> Int {\n\ttake(person.name)\n}",
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
        "func take(s: String) -> Int {\n\ts.length\n}\nfunc ok(s: &String) -> Int {\n\ttake(s)\n}",
    );
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
}

#[test]
fn cheap_clone_extraction_runs_on_vm_without_double_free() {
    // The clone retains the shared buffer; dropping both the owner and the
    // clone releases it twice. A missing retain double-frees (VM error).
    let source = "struct Person {\n\tlet name: String\n}\nfunc extract(person: &Person) -> String {\n\tperson.name\n}\nfunc check() -> Int {\n\tlet p = Person(name: \"hello\" + \" world\")\n\tlet n = extract(p)\n\tn.length\n}\ncheck()";
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
    let source = "struct Person {\n\tlet name: String\n}\nfunc extract(person: &Person) -> String {\n\tperson.name\n}\nfunc check() -> Int {\n\tlet p = Person(name: \"hello\" + \" world\")\n\tlet n = extract(p)\n\tn.length\n}\ncheck()";
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
        "struct Name {\n\tlet value: String\n}\nfunc take(name: Name) -> Int {\n\t0\n}\nfunc bad(name: &Name) -> Int {\n\ttake(name)\n}",
    );
    assert!(typed.has_errors(), "expected a type error");
}

// ----- Borrow conflicts / invalidation ------------------------------------------

#[test]
fn rejects_borrow_use_after_owner_move() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\tlet moved = s\n\tsub.length\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn rejects_borrow_use_after_owner_reassignment() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\ts = \"new\" + \" value\"\n\tsub.length\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn rejects_reassigned_borrow_use_after_owner_move() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\tsub = s.slice(1, 1)\n\tlet moved = s\n\tsub.length\n}",
        "Use of borrowed value 'sub'",
    );
}

#[test]
fn allows_owner_move_after_borrow_last_use() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\tlet n = sub.length\n\tlet moved = s\n\tn\n}",
    );
}

#[test]
fn rejects_owner_move_while_borrow_has_later_use() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\tlet moved = s\n\tsub.length\n}",
        "Cannot move 's' while it is borrowed as 'sub'",
    );
}

#[test]
fn rejects_match_scrutinee_move_while_borrowed() {
    // Scrutinee consumption happens at the Switch terminator: the check
    // must run in the error pass too, not only the silent fixpoint.
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\tlet n = match s {\n\t\t_ -> 1\n\t}\n\tsub.length + n\n}",
        "Cannot move 's' while it is borrowed as 'sub'",
    );
}

#[test]
fn move_while_mutably_borrowed_does_not_report_spurious_shared_borrow() {
    let source = "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet moved = s\n\tborrow.length\n}";
    assert_error_contains(source, "Cannot move 's' while it is borrowed as 'borrow'");
    assert_no_error_contains(source, "Cannot take shared borrow");
}

#[test]
fn mutable_method_receiver_invalidates_borrows_of_receiver() {
    assert_error_contains(
        "struct Box {\n\tlet value: String\n\tmut func touch() -> Int {\n\t\tself.value.length\n\t}\n}\nfunc bad() -> Int {\n\tlet box = Box(value: \"hello\" + \" world\")\n\tlet sub = box.value.slice(0, 1)\n\tlet n = box.touch()\n\tsub.length + n\n}",
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
        "struct Box {\n\tlet value: String\n\tmut func touch() -> Int {\n\t\tself.value.length\n\t}\n}\nfunc ok() -> Int {\n\tlet box = Box(value: \"hello\" + \" world\")\n\tlet sub = box.value.slice(0, 1)\n\tlet n = sub.length\n\tbox.touch() + n\n}",
    );
}

#[test]
fn live_shared_borrow_blocks_later_mutation() {
    assert_error_contains(
        "struct Box {\n\tlet value: String\n\tmut func touch() -> Int {\n\t\tself.value.length\n\t}\n}\nfunc bad() -> Int {\n\tlet box = Box(value: \"hello\" + \" world\")\n\tlet sub = box.value.slice(0, 1)\n\tlet n = box.touch()\n\tsub.length + n\n}",
        "already shared borrowed as 'sub'",
    );
}

#[test]
fn rejects_read_while_mutable_borrow_is_live() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet n = s.length\n\tborrow.length + n\n}",
        "already mutable borrowed as 'borrow'",
    );
}

#[test]
fn mutable_borrow_ends_at_last_use_before_read() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet n = borrow.length\n\ts.length + n\n}",
    );
}

#[test]
fn loop_carried_mutable_borrow_lives_until_storage_dead() {
    assert_error_contains(
        "func observe(s: &String) -> Int {\n\ts.length\n}\nfunc mutate(s: &mut String) -> Int {\n\ts.length\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet r: &mut String = s\n\tlet i = 0\n\tloop i < 2 {\n\t\tlet n = observe(r)\n\t\tlet m = mutate(s)\n\t\ti = i + 1\n\t}\n\t0\n}",
        "already mutable borrowed as 'r'",
    );
}

#[test]
fn per_iteration_mutable_borrow_can_end_before_mutation() {
    assert_no_errors(
        "func observe(s: &String) -> Int {\n\ts.length\n}\nfunc mutate(s: &mut String) -> Int {\n\ts.length\n}\nfunc ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet i = 0\n\tloop i < 2 {\n\t\tlet r: &mut String = s\n\t\tlet n = observe(r)\n\t\tlet m = mutate(s)\n\t\ti = i + 1\n\t}\n\t0\n}",
    );
}

#[test]
fn mutable_call_argument_invalidates_shared_borrow() {
    assert_error_contains(
        "func mutate(s: &mut String) -> Int {\n\ts.length\n}\nfunc bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\tlet n = mutate(s)\n\tsub.length + n\n}",
        "Use of borrowed value 'sub'",
    );
}

// ----- Captures ------------------------------------------------------------------

#[test]
fn rejects_owned_value_capture_without_capture_mode() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func() -> Int {\n\t\ts.length\n\t}\n}",
        "Cannot capture ownership-sensitive value 's'",
    );
}

#[test]
fn rejects_borrowed_value_capture_without_capture_mode() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet sub = s.slice(0, 1)\n\treturn func() -> Int {\n\t\tsub.length\n\t}\n}",
        "Cannot capture ownership-sensitive value 'sub'",
    );
}

#[test]
fn explicit_consuming_capture_moves_parent_value() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [consuming s]() -> Int {\n\t\ts.length\n\t}\n\ts.length\n}",
        "Use of moved value 's'",
    );
}

#[test]
fn explicit_consuming_capture_can_escape() {
    assert_no_errors(
        "func ok() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func [consuming s]() -> Int {\n\t\ts.length\n\t}\n}",
    );
}

#[test]
fn owning_closure_value_copy_moves_source() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [consuming s]() -> Int {\n\t\ts.length\n\t}\n\tlet g = f\n\tf() + g()\n}",
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
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func [copy s]() -> Int {\n\t\ts.length\n\t}\n}",
        "copy captures require a copyable type",
    );
}

#[test]
fn unused_explicit_borrow_capture_can_end_before_owner_move() {
    assert_no_errors(
        "func ok() -> String {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&s]() -> Int {\n\t\ts.length\n\t}\n\treturn s\n}",
    );
}

#[test]
fn explicit_borrow_capture_blocks_owner_move_until_closure_last_use() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&s]() -> Int {\n\t\ts.length\n\t}\n\tlet moved = s\n\tf()\n}",
        "Cannot move 's' while it is borrowed as 'f'",
    );
}

#[test]
fn unused_explicit_mut_borrow_capture_can_end_before_read() {
    assert_no_errors(
        "func ok() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&mut s]() -> Int {\n\t\ts.length\n\t}\n\ts.length\n}",
    );
}

#[test]
fn explicit_mut_borrow_capture_blocks_reads_until_closure_last_use() {
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet f = func [&mut s]() -> Int {\n\t\ts.length\n\t}\n\tlet n = s.length\n\tf() + n\n}",
        "already mutable borrowed as 'f'",
    );
}

#[test]
fn explicit_borrow_capture_cannot_escape() {
    assert_error_contains(
        "func bad() -> () -> Int {\n\tlet s = \"hello\" + \" world\"\n\treturn func [&s]() -> Int {\n\t\ts.length\n\t}\n}",
        "borrow captures are tied to the current stack frame",
    );
}

#[test]
fn rejects_escaping_generic_capture_returned_through_local() {
    assert_error_contains(
        "func bad<Value>(value: Value) -> () -> Value {\n\tlet f = func() -> Value {\n\t\tvalue\n\t}\n\treturn f\n}",
        "Cannot capture ownership-sensitive value 'value'",
    );
}

#[test]
fn rejects_escaping_generic_capture_passed_as_argument() {
    assert_error_contains(
        "func accept<Value>(f: () -> Value) -> Int {\n\t0\n}\nfunc bad<Value>(value: Value) -> Int {\n\taccept(func() -> Value {\n\t\tvalue\n\t})\n}",
        "Cannot capture ownership-sensitive value 'value'",
    );
}

#[test]
fn rejects_escaping_borrow_capture_even_when_referent_is_copy() {
    assert_error_contains(
        "func bad(value: &Int) -> () -> &Int {\n\treturn func() -> &Int {\n\t\tvalue\n\t}\n}",
        "Cannot capture ownership-sensitive value 'value'",
    );
}

#[test]
fn allows_nonescaping_generic_closure_capture() {
    assert_no_errors(
        "func ok<Value>(value: Value) -> Value {\n\tlet f = func() -> Value {\n\t\tvalue\n\t}\n\tf()\n}",
    );
}
