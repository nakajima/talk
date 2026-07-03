//! Flow-checker tests: the ported legacy move/drop corpus plus the new
//! linear must-consume behaviors. Sources are kept byte-identical to the
//! legacy tests they port so parity is auditable.

use crate::compiling::driver::{Driver, DriverConfig, Source, Typed};
use crate::diagnostic::AnyDiagnostic;

fn flow_driver(source: &str) -> Driver<Typed> {
    Driver::new(vec![Source::from(source)], DriverConfig::new("FlowTest"))
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

// ----- Basic moves / copies / reassignment ---------------------------------

#[test]
fn rejects_use_after_simple_owned_move() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nlet t = s\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn allows_copy_value_reuse_after_assignment() {
    assert_no_errors("let x = 1\nlet y = x\nx + y");
}

#[test]
fn allows_reassignment_after_owned_move() {
    assert_no_errors(
        "let s = \"hello\" + \" world\"\nlet t = s\ns = \"new\" + \" value\"\ns.length",
    );
}

#[test]
fn rejects_use_before_initializer() {
    assert_error_contains("let s: String\ns.length", "Use of moved value 's'");
}

// ----- Call arguments / receivers -------------------------------------------

#[test]
fn borrowed_call_argument_does_not_move_owned_value() {
    assert_no_errors(
        "func borrow(s: &String) -> Int {\n\ts.length\n}\nlet s = \"hello\" + \" world\"\nlet n = borrow(s)\ns.length + n",
    );
}

#[test]
fn by_value_call_argument_moves_owned_value() {
    assert_error_contains(
        "func take(s: String) -> Int {\n\ts.length\n}\nlet s = \"hello\" + \" world\"\nlet n = take(s)\ns.length + n",
        "Use of moved value 's'",
    );
}

#[test]
fn repeated_owned_call_operand_is_rejected() {
    assert_error_contains(
        "func take(a: String, b: String) -> Int {\n\ta.length + b.length\n}\nlet s = \"hello\" + \" world\"\ntake(s, s)",
        "Use of moved value 's'",
    );
}

#[test]
fn constructor_argument_moves_owned_value() {
    assert_error_contains(
        "struct Box {\n\tlet value: String\n}\nlet s = \"hello\" + \" world\"\nlet box = Box(value: s)\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn default_method_receiver_does_not_move_owned_receiver() {
    assert_no_errors(
        "struct Box {\n\tlet value: String\n\tfunc len() -> Int {\n\t\tself.value.length\n\t}\n}\nlet box = Box(value: \"hello\" + \" world\")\nlet n = box.len()\nbox.value.length + n",
    );
}

#[test]
fn explicit_consuming_method_receiver_moves_owned_receiver() {
    assert_error_contains(
        "struct Box {\n\tlet value: String\n\tconsuming func consume() -> Int {\n\t\tself.value.length\n\t}\n}\nlet box = Box(value: \"hello\" + \" world\")\nlet n = box.consume()\nbox.value.length + n",
        "Use of moved value 'box'",
    );
}

#[test]
fn by_value_method_argument_moves_owned_value() {
    assert_error_contains(
        "struct Sink {\n\tlet id: Int\n\tfunc take(value: String) -> Int {\n\t\tvalue.length\n\t}\n}\nlet sink = Sink(id: 1)\nlet s = \"hello\" + \" world\"\nlet n = sink.take(s)\ns.length + n",
        "Use of moved value 's'",
    );
}

#[test]
fn borrowed_method_argument_does_not_move_owned_value() {
    assert_no_errors(
        "struct Sink {\n\tlet id: Int\n\tfunc take(value: &String) -> Int {\n\t\tvalue.length\n\t}\n}\nlet sink = Sink(id: 1)\nlet s = \"hello\" + \" world\"\nlet n = sink.take(s)\ns.length + n",
    );
}

// ----- Aggregate literals ---------------------------------------------------

#[test]
fn tuple_literal_moves_owned_element() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nlet pair = (s, 1)\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn array_literal_moves_owned_element() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nlet array = [s]\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn record_literal_moves_owned_field_value() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nlet record = { value: s }\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn repeated_owned_tuple_operand_is_rejected() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nlet pair = (s, s)\n0",
        "Use of moved value 's'",
    );
}

// ----- Partial (field) moves ------------------------------------------------

#[test]
fn rejects_use_after_struct_with_owned_field_move() {
    assert_error_contains(
        "struct Person {\n\tlet name: String\n}\nlet person = Person(name: \"Pat\" + \"!\")\nlet moved = person\nperson.name.length",
        "Use of moved value 'person'",
    );
}

#[test]
fn allows_sibling_field_after_owned_field_move() {
    assert_no_errors(
        "struct Person {\n\tlet name: String\n\tlet age: Int\n}\nlet person = Person(name: \"Pat\" + \"!\", age: 40)\nlet name = person.name\nperson.age",
    );
}

#[test]
fn rejects_whole_struct_use_after_owned_field_move() {
    assert_error_contains(
        "struct Person {\n\tlet name: String\n\tlet age: Int\n}\nlet person = Person(name: \"Pat\" + \"!\", age: 40)\nlet name = person.name\nlet moved = person\nmoved.age",
        "Use of moved value 'person.name'",
    );
}

#[test]
fn field_assignment_restores_moved_field() {
    assert_no_errors(
        "struct Person {\n\tlet name: String\n\tlet age: Int\n}\nlet person = Person(name: \"Pat\" + \"!\", age: 40)\nlet name = person.name\nperson.name = \"Sue\" + \"!\"\nperson.name.length + person.age",
    );
}

// ----- Copy structs / generics ----------------------------------------------

#[test]
fn allows_reuse_after_copy_struct_assignment() {
    assert_no_errors(
        "struct Point {\n\tlet x: Int\n}\nlet point = Point(x: 1)\nlet copy = point\npoint.x + copy.x",
    );
}

#[test]
fn rejects_use_after_generic_struct_instantiated_with_owned_field_move() {
    assert_error_contains(
        "struct Box<Item> {\n\tlet value: Item\n}\nlet box = Box(value: \"hello\" + \" world\")\nlet moved = box\nbox.value.length",
        "Use of moved value 'box'",
    );
}

#[test]
fn allows_reuse_after_generic_struct_instantiated_with_copy_field_assignment() {
    assert_no_errors(
        "struct Box<Item> {\n\tlet value: Item\n}\nlet box = Box(value: 1)\nlet copy = box\nbox.value + copy.value",
    );
}

// ----- Control-flow joins -----------------------------------------------------

#[test]
fn match_arm_move_then_use_is_rejected() {
    assert_error_contains(
        "enum E {\n\tcase a\n\tcase b\n}\nfunc bad(e: E) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tmatch e {\n\t\t.a -> {\n\t\t\tlet moved = s\n\t\t\ts.length\n\t\t},\n\t\t.b -> 0\n\t}\n}",
        "Use of moved value 's'",
    );
}

#[test]
fn match_arm_move_does_not_poison_sibling_arm() {
    assert_no_errors(
        "enum E {\n\tcase a\n\tcase b\n}\nfunc ok(e: E) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tmatch e {\n\t\t.a -> {\n\t\t\tlet moved = s\n\t\t\t0\n\t\t},\n\t\t.b -> s.length\n\t}\n}",
    );
}

#[test]
fn branch_move_then_use_after_join_is_rejected() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nlet flag = true\nif flag {\n\tlet t = s\n\t1\n} else {\n\t2\n}\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn rejects_loop_carried_move_reuse() {
    assert_error_contains(
        "func take(s: String) -> Int {\n\ts.length\n}\nlet s = \"hello\" + \" world\"\nlet i = 0\nloop i < 2 {\n\tlet n = take(s)\n\ti = i + 1\n}",
        "Use of moved value 's'",
    );
}

// ----- Move propagation across nested bodies ---------------------------------

#[test]
fn nested_function_capture_move_propagates_to_parent() {
    assert_error_contains(
        "let s = \"hello\" + \" world\"\nfunc inner[consuming s]() -> Int {\n\ts.length\n}\ns.length",
        "Use of moved value 's'",
    );
}

#[test]
fn trailing_block_body_move_propagates_to_parent() {
    assert_error_contains(
        "func run(f: () -> Int) -> Int {\n\t0\n}\nlet s = \"hello\" + \" world\"\nlet n = run() {\n\tlet moved = s\n\t0\n}\ns.length + n",
        "Use of moved value 's'",
    );
}

// ----- Drop schedules (HIR annotations) --------------------------------------

use crate::flow::drops::{DropElaboration, DropReason, DropSchedule};
use crate::hir;

/// The named function's body block in the checked HIR. Top-level `func`
/// declarations are lowered to `let name = func ...` during name
/// resolution, so both shapes are searched.
fn func_body(driver: &Driver<Typed>, name: &str) -> hir::Block {
    for file in driver.phase.hir.values() {
        for root in &file.roots {
            let hir::Node::Decl(decl) = root else {
                continue;
            };
            match &decl.kind {
                hir::DeclKind::Func(func) if func.name.name_str() == name => {
                    return func.body.clone();
                }
                hir::DeclKind::Let { lhs, rhs: Some(rhs), .. } => {
                    let binds_name = matches!(
                        &lhs.kind,
                        hir::PatternKind::Bind(bound) if bound.name_str() == name
                    );
                    if binds_name
                        && let hir::ExprKind::Func(func) = &rhs.kind
                    {
                        return func.body.clone();
                    }
                }
                _ => {}
            }
        }
    }
    panic!("no function named {name} in checked HIR");
}

/// The named function's STORED, flow-annotated MIR body — the drop
/// authority lowering consumes.
fn stored_body(driver: &Driver<Typed>, name: &str) -> std::sync::Arc<crate::lower::mir::Body> {
    let block = func_body(driver, name);
    driver
        .phase
        .mir_bodies
        .get(block.id)
        .expect("function body stored")
}

/// Every elaborated drop candidate in the body, as (display name of the
/// dropped symbol — empty for expression targets, reason, kind), in
/// statement order.
fn candidate_drops(
    driver: &Driver<Typed>,
    body: &crate::lower::mir::Body,
) -> Vec<(String, DropReason, DropElaboration)> {
    use crate::lower::mir;
    let names = &driver.phase.resolved_names.symbol_names;
    body.blocks
        .iter()
        .flat_map(|block| &block.statements)
        .filter_map(|statement| {
            let mir::Statement::DropCandidate { target, reason, .. } = &statement.kind else {
                return None;
            };
            let kind = statement.ownership.drop.as_ref()?.kind;
            let name = match target {
                mir::DropTarget::Symbol { symbol, .. } => {
                    names.get(symbol).cloned().unwrap_or_default()
                }
                mir::DropTarget::Expr(_) => String::new(),
            };
            Some((name, *reason, kind))
        })
        .collect()
}

#[test]
fn straight_line_owned_local_drops_static_at_scope_exit() {
    let driver = flow_driver("func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\t1\n}");
    let body = stored_body(&driver, "make");
    assert_eq!(
        candidate_drops(&driver, &body),
        vec![("s".into(), DropReason::ScopeExit, DropElaboration::Static)]
    );
}

#[test]
fn aggregate_move_makes_source_scope_drop_dead() {
    let driver = flow_driver(
        "func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet pair = (s, 1)\n\t0\n}",
    );
    let body = stored_body(&driver, "make");
    // Reverse declaration order: `pair` (live) drops first, then `s` (moved).
    assert_eq!(
        candidate_drops(&driver, &body),
        vec![
            ("pair".into(), DropReason::ScopeExit, DropElaboration::Static),
            ("s".into(), DropReason::ScopeExit, DropElaboration::Dead),
        ]
    );
}

#[test]
fn branch_move_makes_scope_drop_conditional() {
    let driver = flow_driver(
        "func make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\tlet t = s\n\t\t1\n\t} else {\n\t\t2\n\t}\n\t0\n}",
    );
    let body = stored_body(&driver, "make");
    let s_drops: Vec<_> = candidate_drops(&driver, &body)
        .into_iter()
        .filter(|(name, _, _)| name == "s")
        .collect();
    assert_eq!(
        s_drops,
        vec![("s".into(), DropReason::ScopeExit, DropElaboration::Conditional)]
    );
}

#[test]
fn field_move_makes_scope_drop_open() {
    let driver = flow_driver(
        "struct Person {\n\tlet name: String\n\tlet age: Int\n}\nfunc make() -> Int {\n\tlet person = Person(name: \"Pat\" + \"!\", age: 40)\n\tlet name = person.name\n\tperson.age\n}",
    );
    let body = stored_body(&driver, "make");
    // Reverse declaration order: `name` (live), then `person` (partly moved).
    assert_eq!(
        candidate_drops(&driver, &body),
        vec![
            ("name".into(), DropReason::ScopeExit, DropElaboration::Static),
            ("person".into(), DropReason::ScopeExit, DropElaboration::Open),
        ]
    );
}

#[test]
fn early_exit_schedules_enclosing_scope_drops() {
    let driver = flow_driver(
        "func make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\treturn 1\n\t}\n\ts.length\n}",
    );
    let body = stored_body(&driver, "make");
    let early: Vec<_> = candidate_drops(&driver, &body)
        .into_iter()
        .filter(|(_, reason, _)| *reason == DropReason::EarlyExit)
        .collect();
    // The early return drops `s` (still live on that path).
    assert_eq!(
        early,
        vec![("s".into(), DropReason::EarlyExit, DropElaboration::Static)]
    );
}

#[test]
fn assignment_schedules_replace_drop() {
    let driver = flow_driver(
        "func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ts = \"new\" + \" value\"\n\ts.length\n}",
    );
    let body = stored_body(&driver, "make");
    let replace: Vec<_> = candidate_drops(&driver, &body)
        .into_iter()
        .filter(|(_, reason, _)| *reason == DropReason::AssignmentReplace)
        .collect();
    assert_eq!(
        replace,
        vec![(String::new(), DropReason::AssignmentReplace, DropElaboration::Static)]
    );
}

#[test]
fn consumed_expressions_are_annotated() {
    let driver = flow_driver(
        "func take(s: String) -> Int {\n\ts.length\n}\nfunc make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}",
    );
    let body = func_body(&driver, "make");
    let mut consuming_uses = 0;
    {
        use derive_visitor::Drive;
        let mut visitor = ConsumeCounter(&mut consuming_uses);
        for node in &body.body {
            node.drive(&mut visitor);
        }
    }
    assert_eq!(consuming_uses, 1, "the argument use of `s` consumes");
}

#[derive(derive_visitor::Visitor)]
#[visitor(hir::Expr(enter))]
struct ConsumeCounter<'a>(&'a mut usize);

impl ConsumeCounter<'_> {
    fn enter_expr(&mut self, expr: &hir::Expr) {
        if expr.ownership.consumes {
            *self.0 += 1;
        }
    }
}

// ----- Linear must-consume ----------------------------------------------------

#[test]
fn linear_value_dropped_at_scope_exit_is_rejected() {
    assert_error_contains(
        "struct Token 'linear {\n\tlet id: Int\n}\nfunc make() -> Int {\n\tlet token = Token(id: 1)\n\t0\n}",
        "is linear and must be consumed",
    );
}

#[test]
fn linear_value_consumed_by_consuming_method_is_accepted() {
    assert_no_errors(
        "struct Token 'linear {\n\tlet id: Int\n\tconsuming func close() -> Int {\n\t\tself.id\n\t}\n}\nfunc make() -> Int {\n\tlet token = Token(id: 1)\n\ttoken.close()\n}",
    );
}

#[test]
fn linear_value_moved_in_one_branch_only_is_rejected() {
    assert_error_contains(
        "struct Token 'linear {\n\tlet id: Int\n\tconsuming func close() -> Int {\n\t\tself.id\n\t}\n}\nfunc make(flag: Bool) -> Int {\n\tlet token = Token(id: 1)\n\tif flag {\n\t\ttoken.close()\n\t} else {\n\t\t0\n\t}\n}",
        "is linear and must be consumed",
    );
}

// ----- End-to-end under the Flow flag -----------------------------------------

/// A drop-heavy program compiles and runs (VM + reference evaluator agree)
/// with the flow checker selected. Lowering still derives its drop plan
/// internally until P3 re-points it at the HIR annotations; this proves the
/// pipeline holds together under the flag.
#[test]
fn vm_and_evaluator_agree_under_flow_checker() {
    let source = "func shout(s: String) -> Int {\n\ts.length\n}\nfunc make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\tlet t = s\n\t\tshout(t)\n\t} else {\n\t\t2\n\t}\n}\nmake(true)";
    let typed = Driver::new(vec![Source::from(source)], DriverConfig::new("FlowVmTest"))
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let vm_value = lowered.run_vm().expect("vm");
    let evaluator_value = lowered.eval_for_tests().expect("evaluator");
    match (&evaluator_value, &vm_value) {
        (crate::lambda_g::eval::EvalValue::I64(a), crate::vm::interp::Value::I64(b)) => {
            assert_eq!(a, b);
            assert_eq!(*b, 11);
        }
        other => panic!("unexpected results: {other:?}"),
    }
}

// ----- Deinit ------------------------------------------------------------------

/// A `Deinit` conformance runs at scope exit: the destructor increments a
/// global, observable through the VM. The deinit body's own scope drops
/// self's fields — no double teardown, no recursion.
#[test]
fn deinit_runs_at_scope_exit() {
    let source = "let counter = 0\nstruct Guard {\n\tlet id: Int\n}\nextend Guard: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tcounter = counter + 1\n\t\t()\n\t}\n}\nfunc scope() -> Int {\n\tlet g = Guard(id: 1)\n\t0\n}\nlet n = scope() + scope()\ncounter";
    let typed = Driver::new(vec![Source::from(source)], DriverConfig::new("DeinitVm"))
        .parse()
        .expect("parse")
        .resolve_names()
        .expect("resolve")
        .type_check();
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let value = lowered.run_vm().expect("vm");
    match value {
        crate::vm::interp::Value::I64(n) => assert_eq!(n, 2, "deinit should run once per scope"),
        other => panic!("unexpected result: {other:?}"),
    }
}

// ----- Heap classification ------------------------------------------------------

#[test]
fn heap_struct_classifies_as_object() {
    let typed = flow_driver("struct Node 'heap {\n\tlet value: Int\n}\n0");
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let types = &typed.phase.types;
    let grades = crate::flow::grades::GradeView::new(types);
    let symbol = types
        .catalog
        .structs
        .keys()
        .copied()
        .find(|s| types.display_names.get(s).map(String::as_str) == Some("Node"))
        .expect("Node in catalog");
    let ty = crate::types::ty::Ty::Nominal(symbol, vec![]);
    assert!(grades.is_object(&ty), "'heap struct should classify as object");
    assert!(grades.contains_object(&ty));
    assert!(!grades.needs_drop(&ty), "objects release via regions, not drops");
    assert!(grades.is_copy(&ty), "object handles copy freely");
}

#[test]
fn value_struct_with_heap_field_stays_value() {
    let typed = flow_driver(
        "struct Node 'heap {\n\tlet value: Int\n}\nstruct Wrapper {\n\tlet node: Node\n}\n0",
    );
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let types = &typed.phase.types;
    let grades = crate::flow::grades::GradeView::new(types);
    let symbol = types
        .catalog
        .structs
        .keys()
        .copied()
        .find(|s| types.display_names.get(s).map(String::as_str) == Some("Wrapper"))
        .expect("Wrapper in catalog");
    let ty = crate::types::ty::Ty::Nominal(symbol, vec![]);
    assert!(!grades.is_object(&ty), "no contagion: Wrapper stays a value");
    assert!(
        grades.contains_object(&ty),
        "but it carries a handle (bind-boundary scans)"
    );
}

#[test]
fn rejects_heap_struct_claiming_copy() {
    assert_error_contains_any_diagnostic(
        "struct Node 'heap {\n\tlet value: Int\n}\nextend Node: Copy {}\n0",
    );
}

#[test]
fn rejects_heap_struct_claiming_cheap_clone() {
    assert_error_contains_any_diagnostic(
        "struct Node 'heap {\n\tlet value: Int\n}\nextend Node: CheapClone {}\n0",
    );
}

fn assert_error_contains_any_diagnostic(source: &str) {
    let typed = flow_driver(source);
    assert!(
        typed.has_errors(),
        "expected a diagnostic, got none for {source:?}"
    );
}

// ----- Heap aliasing (P3) -------------------------------------------------------

#[test]
fn heap_aliases_freely_without_moves_or_conflicts() {
    assert_no_errors(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc ok() -> Int {\n\tlet a = Node(value: 1)\n\tlet b = a\n\tlet c = a\n\tb.value + c.value + a.value\n}\n0",
    );
}

#[test]
fn heap_field_assignment_through_alias_is_clean() {
    assert_no_errors(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc ok() -> Int {\n\tlet a = Node(value: 1)\n\tlet b = a\n\tb.value = 9\n\ta.value\n}\n0",
    );
}

#[test]
fn heap_borrowed_param_field_assignment_is_clean() {
    assert_no_errors(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc poke(n: Node) -> Int {\n\tn.value = 5\n\tn.value\n}\n0",
    );
}

#[test]
fn heap_cross_link_and_cycle_are_clean() {
    assert_no_errors(
        "struct Node 'heap {\n\tlet value: Int\n\tlet next: Node?\n}\nfunc ok() -> Int {\n\tlet a = Node(value: 1, next: Optional.none)\n\tlet b = Node(value: 2, next: Optional.some(a))\n\ta.next = Optional.some(b)\n\t0\n}\n0",
    );
}

#[test]
fn heap_binding_gets_release_schedule() {
    let typed = flow_driver(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc scope() -> Int {\n\tlet a = Node(value: 1)\n\t0\n}\n0",
    );
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    assert!(
        typed
            .phase
            .flow
            .drops
            .iter()
            .any(|fact| fact.place == "a"),
        "the heap binding should get a scope-exit release schedule: {:?}",
        typed.phase.flow.drops
    );
}

#[test]
fn value_borrow_conflicts_still_fire() {
    // Regression: the object exemption must not weaken value checking.
    assert_error_contains(
        "func bad() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet borrow: &mut String = s\n\tlet n = s.length\n\tborrow.length + n\n}\n0",
        "already mutable borrowed",
    );
}

#[test]
fn rejects_heap_capture_in_escaping_closure() {
    assert_error_contains(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc bad() -> () -> Int {\n\tlet n = Node(value: 1)\n\treturn func() -> Int {\n\t\tn.value\n\t}\n}\n0",
        "escape",
    );
}

#[test]
fn rejects_heap_in_existential() {
    assert_error_contains(
        "struct Node 'heap {\n\tlet value: Int\n}\nextend Node: Showable {\n\tfunc show() -> String {\n\t\t\"node\"\n\t}\n}\nfunc bad() -> Int {\n\tlet s: any Showable = Node(value: 1)\n\t0\n}\n0",
        "existential",
    );
}

#[test]
fn rejects_heap_in_raw_storage_container() {
    assert_error_contains(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc bad() -> Int {\n\tlet items = [Node(value: 1)]\n\t0\n}\n0",
        "raw storage",
    );
}

#[test]
fn heap_global_is_allowed() {
    assert_no_errors(
        "struct Node 'heap {\n\tlet value: Int\n}\nlet root = Node(value: 1)\nroot.value",
    );
}

// ----- Heap lowering e2e (P4) -----------------------------------------------------

fn run_heap_vm(source: &str) -> crate::vm::interp::Value {
    let typed = flow_driver(source);
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    lowered.run_vm().expect("vm")
}

fn run_heap_eval(source: &str) -> (crate::lambda_g::eval::EvalValue, usize, usize) {
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
    (value, evaluator.live_objects(), evaluator.live_allocations())
}

#[test]
fn heap_aliased_mutation_is_visible_on_vm() {
    let value = run_heap_vm(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc check() -> Int {\n\tlet a = Node(value: 1)\n\tlet b = a\n\tb.value = 42\n\ta.value\n}\ncheck()",
    );
    assert_eq!(value, crate::vm::interp::Value::I64(42));
}

#[test]
fn heap_cycle_frees_and_leaks_nothing() {
    let (value, live_objects, live_allocations) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n\tlet next: Node?\n}\nfunc check() -> Int {\n\tlet a = Node(value: 1, next: Optional.none)\n\tlet b = Node(value: 2, next: Optional.some(a))\n\ta.next = Optional.some(b)\n\tb.value\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(2));
    assert_eq!(live_objects, 0, "cycle freed at scope exit");
    assert_eq!(live_allocations, 0, "no buffer leaks");
}

#[test]
fn heap_mut_func_mutates_in_place() {
    let value = run_heap_vm(
        "struct Counter 'heap {\n\tlet count: Int\n\tmut func bump() -> Int {\n\t\tself.count = self.count + 1\n\t\tself.count\n\t}\n}\nfunc check() -> Int {\n\tlet c = Counter(count: 0)\n\tlet d = c\n\tlet n1 = c.bump()\n\tlet n2 = d.bump()\n\tn1 * 10 + n2\n}\ncheck()",
    );
    assert_eq!(
        value,
        crate::vm::interp::Value::I64(12),
        "both names see both bumps (no copy-back)"
    );
}

#[test]
fn heap_deinit_runs_at_region_teardown() {
    let value = run_heap_vm(
        "let counter = 0\nstruct Guard 'heap {\n\tlet id: Int\n}\nextend Guard: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tcounter = counter + 1\n\t\t()\n\t}\n}\nfunc scope() -> Int {\n\tlet g = Guard(id: 1)\n\tlet h = Guard(id: 2)\n\t0\n}\nlet n = scope()\ncounter",
    );
    assert_eq!(
        value,
        crate::vm::interp::Value::I64(2),
        "deinit once per object at region teardown"
    );
}

#[test]
fn heap_string_fields_release_buffers() {
    let (_, live_objects, live_allocations) = run_heap_eval(
        "struct Named 'heap {\n\tlet name: String\n}\nfunc check() -> Int {\n\tlet n = Named(name: \"hello\" + \" world\")\n\tn.name.length\n}\ncheck()",
    );
    assert_eq!(live_objects, 0);
    assert_eq!(live_allocations, 0, "finalizer frees the owned buffer");
}

#[test]
fn heap_returned_alias_keeps_region_alive() {
    let value = run_heap_vm(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc make() -> Node {\n\tNode(value: 7)\n}\nfunc check() -> Int {\n\tlet n = make()\n\tn.value\n}\ncheck()",
    );
    assert_eq!(value, crate::vm::interp::Value::I64(7));
}


// ----- Heap adversarial hardening (P5) --------------------------------------------

#[test]
fn heap_handles_in_value_containers_balance() {
    let (_, live_objects, live_allocations) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc check() -> Int {\n\tlet n = Node(value: 1)\n\tlet pair = (n, 2)\n\tlet opt = Optional.some(n)\n\t0\n}\ncheck()",
    );
    assert_eq!(live_objects, 0, "tuple/enum-carried handles balance");
    assert_eq!(live_allocations, 0);
}

#[test]
fn heap_interior_alias_outlives_constructing_frame() {
    let value = run_heap_vm(
        "struct Node 'heap {\n\tlet value: Int\n\tlet next: Node?\n}\nfunc make() -> Node {\n\tlet root = Node(value: 7, next: Optional.none)\n\tlet child = Node(value: 9, next: Optional.none)\n\troot.next = Optional.some(child)\n\tchild\n}\nfunc check() -> Int {\n\tlet a = make()\n\ta.value\n}\ncheck()",
    );
    assert_eq!(
        value,
        crate::vm::interp::Value::I64(9),
        "returning an interior alias keeps the region alive"
    );
}

#[test]
fn heap_interior_alias_balances_ledger() {
    let (value, live_objects, live_allocations) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n\tlet next: Node?\n}\nfunc make() -> Node {\n\tlet root = Node(value: 7, next: Optional.none)\n\tlet child = Node(value: 9, next: Optional.none)\n\troot.next = Optional.some(child)\n\tchild\n}\nfunc check() -> Int {\n\tlet a = make()\n\ta.value\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(9));
    assert_eq!(live_objects, 0, "whole region frees when the alias drops");
    assert_eq!(live_allocations, 0);
}

#[test]
fn heap_global_works_and_mutates() {
    let value = run_heap_vm(
        "struct Node 'heap {\n\tlet value: Int\n}\nlet root = Node(value: 1)\nfunc bump() -> Int {\n\troot.value = root.value + 10\n\troot.value\n}\nbump() + root.value",
    );
    assert_eq!(value, crate::vm::interp::Value::I64(22));
}

#[test]
fn heap_deinit_creating_objects_nests_teardown() {
    let value = run_heap_vm(
        "let counter = 0\nstruct Inner 'heap {\n\tlet id: Int\n}\nextend Inner: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tcounter = counter + 1\n\t\t()\n\t}\n}\nstruct Outer 'heap {\n\tlet id: Int\n}\nextend Outer: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tlet extra = Inner(id: 9)\n\t\tcounter = counter + 100\n\t\t()\n\t}\n}\nfunc scope() -> Int {\n\tlet o = Outer(id: 1)\n\t0\n}\nlet n = scope()\ncounter",
    );
    assert_eq!(
        value,
        crate::vm::interp::Value::I64(101),
        "a deinit-created region tears down nested inside the walk"
    );
}

#[test]
fn heap_resurrection_from_deinit_traps() {
    let source = "struct Slot 'heap {\n\tlet held: Guard?\n}\nstruct Guard 'heap {\n\tlet id: Int\n}\nlet keeper = Slot(held: Optional.none)\nextend Guard: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tkeeper.held = Optional.some(self)\n\t\t()\n\t}\n}\nfunc scope() -> Int {\n\tlet g = Guard(id: 1)\n\t0\n}\nscope()";
    let typed = flow_driver(source);
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let mut lowered = typed.lower();
    assert!(
        lowered.phase.diagnostics.is_empty(),
        "lowering: {:?}",
        lowered.phase.diagnostics
    );
    let error = lowered.run_vm().expect_err("resurrection should trap");
    assert!(
        error.contains("teardown"),
        "expected the store-during-teardown trap, got: {error}"
    );
}

#[test]
fn heap_linked_regions_free_together() {
    let (_, live_objects, live_allocations) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n\tlet next: Node?\n}\nfunc check() -> Int {\n\tlet a = Node(value: 1, next: Optional.none)\n\tlet b = Node(value: 2, next: Optional.none)\n\ta.next = Optional.some(b)\n\t0\n}\ncheck()",
    );
    assert_eq!(live_objects, 0, "merged regions free when both roots drop");
    assert_eq!(live_allocations, 0);
}

// ----- Dict (P6 stdlib validation) ----------------------------------------------

#[test]
fn dict_inserts_and_looks_up() {
    let value = run_heap_vm(
        "func check() -> Int {\n\tlet d = Dict<Int>()\n\td.insert(\"one\", 1)\n\td.insert(\"two\", 2)\n\td.insert(\"three\", 3)\n\tlet two: Int? = d.get(\"two\")\n\tlet four: Int? = d.get(\"four\")\n\tlet hit = match two {\n\t\t.some(v) -> v,\n\t\t.none -> 0 - 1\n\t}\n\tlet miss = match four {\n\t\t.some(v) -> v,\n\t\t.none -> 0 - 1\n\t}\n\thit * 10 + miss\n}\ncheck()",
    );
    assert_eq!(value, crate::vm::interp::Value::I64(19), "hit=2, miss=-1");
}

#[test]
fn dict_leaks_nothing() {
    let (value, live_objects, _) = run_heap_eval(
        "func check() -> Int {\n\tlet d = Dict<Int>()\n\td.insert(\"one\", 1)\n\td.insert(\"two\", 2)\n\td.count\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(2));
    assert_eq!(live_objects, 0, "dict region frees at scope exit");
}

// ----- Http router on heap chain (P6) ---------------------------------------------

#[test]
fn http_router_grows_past_four_routes() {
    // The old router hardcoded 4 slots; the heap chain has no cap.
    let source = "func check() -> Int {\n\tlet server = HTTP.Server()\n\tserver.get(\"/\", func() -> String { \"home\" })\n\tserver.get(\"/a\", func() -> String { \"aaa\" })\n\tserver.get(\"/b\", func() -> String { \"bbb\" })\n\tserver.get(\"/c\", func() -> String { \"ccc\" })\n\tserver.get(\"/d\", func() -> String { \"ddd\" })\n\tserver.get(\"/e\", func() -> String { \"eee\" })\n\tlet wire = server.handle(\"GET /d HTTP/1.1\")\n\twire.find(\"ddd\")\n}\ncheck()";
    let value = run_heap_vm(source);
    let crate::vm::interp::Value::I64(position) = value else {
        panic!("unexpected result: {value:?}");
    };
    assert!(position > 0, "the fifth route should dispatch: {position}");
}

#[test]
fn http_router_misses_cleanly() {
    let source = "func check() -> Int {\n\tlet server = HTTP.Server()\n\tserver.get(\"/\", func() -> String { \"home\" })\n\tlet wire = server.handle(\"GET /nope HTTP/1.1\")\n\twire.find(\"404\")\n}\ncheck()";
    let value = run_heap_vm(source);
    let crate::vm::interp::Value::I64(position) = value else {
        panic!("unexpected result: {value:?}");
    };
    assert!(position > 0, "missing routes should 404: {position}");
}

#[test]
fn dict_with_string_values_shares_buffers_safely() {
    // The generic body extracts node.value with Value = String: the
    // instantiation must retain the buffer (tier-2 decided at lowering).
    let (value, live_objects, live_allocations) = run_heap_eval(
        "func check() -> Int {\n\tlet d = Dict<String>()\n\td.insert(\"greet\", \"hello\" + \" world\")\n\tlet got: String? = d.get(\"greet\")\n\tmatch got {\n\t\t.some(s) -> s.length,\n\t\t.none -> 0 - 1\n\t}\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(11));
    assert_eq!(live_objects, 0);
    assert_eq!(live_allocations, 0, "extracted String must retain, not share");
}

#[test]
fn dict_with_string_values_runs_on_vm() {
    let value = run_heap_vm(
        "func check() -> Int {\n\tlet d = Dict<String>()\n\td.insert(\"greet\", \"hello\" + \" world\")\n\tlet got: String? = d.get(\"greet\")\n\tmatch got {\n\t\t.some(s) -> s.length,\n\t\t.none -> 0 - 1\n\t}\n}\ncheck()",
    );
    assert_eq!(value, crate::vm::interp::Value::I64(11), "no double free");
}

#[test]
fn generic_heap_extraction_clones_per_instantiation() {
    // The generic body can't know Value's grade; lowering decides at the
    // instantiation: String retains its buffer, Int does nothing.
    let source = "struct Holder<Value> 'heap {\n\tlet value: Value\n}\nfunc extract<Value>(h: Holder<Value>) -> Value {\n\th.value\n}\nfunc check() -> Int {\n\tlet h = Holder(value: \"hello\" + \" world\")\n\tlet s = extract(h)\n\tlet i = Holder(value: 41)\n\tlet n = extract(i)\n\ts.length + n\n}\ncheck()";
    let (value, live_objects, live_allocations) = run_heap_eval(source);
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(52));
    assert_eq!(live_objects, 0);
    assert_eq!(live_allocations, 0, "String instantiation retains; Int does nothing");
}

#[test]
fn generic_heap_extraction_rejects_non_cheap_owned_instantiation() {
    // Wrap { name: String } is owned but not CheapClone: the instantiation
    // cannot decide between clone and move, so lowering reports it.
    let source = "struct Wrap {\n\tlet name: String\n}\nstruct Holder<Value> 'heap {\n\tlet value: Value\n}\nfunc extract<Value>(h: Holder<Value>) -> Value {\n\th.value\n}\nfunc check() -> Int {\n\tlet h = Holder(value: Wrap(name: \"hi\" + \"!\"))\n\tlet w = extract(h)\n\t0\n}\ncheck()";
    let typed = flow_driver(source);
    assert!(!typed.has_errors(), "{:?}", typed.diagnostics());
    let lowered = typed.lower();
    assert!(
        lowered
            .phase
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("CheapClone")),
        "expected the unsupported-instantiation diagnostic: {:?}",
        lowered.phase.diagnostics
    );
}

// ----- Enum payload drops (pre-merge hardening) -----------------------------------

#[test]
fn enum_payload_drops_at_scope_exit() {
    let (_, _, live_allocations) = run_heap_eval(
        "func check() -> Int {\n\tlet o = Optional.some(\"hello\" + \" world\")\n\t0\n}\ncheck()",
    );
    assert_eq!(live_allocations, 0, "the Optional's String payload must free");
}

#[test]
fn enum_payload_extraction_transfers_ownership() {
    let (value, _, live_allocations) = run_heap_eval(
        "func check() -> Int {\n\tlet o = Optional.some(\"hello\" + \" world\")\n\tlet n = match o {\n\t\t.some(s) -> s.length,\n\t\t.none -> 0\n\t}\n\tn\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(11));
    assert_eq!(live_allocations, 0, "payload freed exactly once");
}

#[test]
fn enum_payload_conditional_drop() {
    let (_, _, live_allocations) = run_heap_eval(
        "func take(o: String?) -> Int {\n\t0\n}\nfunc check(flag: Bool) -> Int {\n\tlet o = Optional.some(\"hello\" + \" world\")\n\tif flag {\n\t\ttake(o)\n\t} else {\n\t\t0\n\t}\n}\ncheck(true) + check(false)",
    );
    assert_eq!(live_allocations, 0, "moved-on-one-path payload drops exactly once");
}

#[test]
fn consumed_by_value_param_drops_in_callee() {
    let (value, _, live_allocations) = run_heap_eval(
        "func take(name: String) -> Int {\n\tname.length\n}\nfunc check() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ttake(s)\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(11));
    assert_eq!(live_allocations, 0, "the consumed argument's drop rides the callee");
}


// ----- Ledger completeness (pre-merge hardening) -----------------------------------

#[test]
fn destructured_heap_rvalue_balances() {
    let (_, live_objects, _) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc check() -> Int {\n\tlet (a, b) = (Node(value: 1), Node(value: 2))\n\ta.value + b.value\n}\ncheck()",
    );
    assert_eq!(live_objects, 0, "destructured rvalue handles free at scope exit");
}

#[test]
fn destructured_heap_place_read_balances() {
    let (_, live_objects, _) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc check() -> Int {\n\tlet pair = (Node(value: 1), Node(value: 2))\n\tlet (a, b) = pair\n\ta.value + b.value\n}\ncheck()",
    );
    assert_eq!(live_objects, 0, "aliasing destructure neither leaks nor double-frees");
}

#[test]
fn rvalue_match_scrutinee_releases() {
    let (value, live_objects, _) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc make() -> Node? {\n\tOptional.some(Node(value: 7))\n}\nfunc check() -> Int {\n\tmatch make() {\n\t\t.some(n) -> n.value,\n\t\t.none -> 0\n\t}\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(7));
    assert_eq!(live_objects, 0, "the scrutinee temp's region frees after the match");
}

#[test]
fn heap_rvalue_arg_through_witness_call_releases() {
    // Rule D on the protocol-dispatch call path: an rvalue argument
    // carrying a handle dies with the call.
    let (value, live_objects, _) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n}\nprotocol Taker {\n\tfunc take(n: Node) -> Int\n}\nstruct Sink {}\nextend Sink: Taker {\n\tfunc take(n: Node) -> Int {\n\t\tn.value\n\t}\n}\nfunc check<T: Taker>(sink: T) -> Int {\n\tsink.take(Node(value: 3))\n}\ncheck(Sink())",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(3));
    assert_eq!(live_objects, 0, "the temp releases after the witness call");
}

#[test]
fn heap_rvalue_arg_through_closure_call_releases() {
    let (value, live_objects, _) = run_heap_eval(
        "struct Node 'heap {\n\tlet value: Int\n}\nfunc check() -> Int {\n\tlet f = func(n: Node) -> Int {\n\t\tn.value\n\t}\n\tf(Node(value: 5))\n}\ncheck()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(5));
    assert_eq!(live_objects, 0, "the temp releases after the closure call");
}

// ----- Existential drops + derive ban + cross-file (pre-merge hardening) ----------

#[test]
fn existential_payload_drops() {
    let (_, _, live_allocations) = run_heap_eval(
        "func check() -> Int {\n\tlet x: any Showable = \"hello\" + \" world\"\n\t0\n}\ncheck()",
    );
    assert_eq!(live_allocations, 0, "the packed String's buffer must free");
}

#[test]
fn existential_payload_deinit_runs() {
    let value = run_heap_vm(
        "let counter = 0\nstruct Guard {\n\tlet id: Int\n}\nextend Guard: Deinit {\n\tconsuming func deinit() -> Void {\n\t\tcounter = counter + 1\n\t\t()\n\t}\n}\nextend Guard: Showable {\n\tfunc show() -> String {\n\t\t\"guard\"\n\t}\n}\nfunc scope() -> Int {\n\tlet x: any Showable = Guard(id: 1)\n\t0\n}\nlet n = scope()\ncounter",
    );
    assert_eq!(
        value,
        crate::vm::interp::Value::I64(1),
        "the packed Guard's deinit runs when the existential drops"
    );
}

#[test]
fn rejects_auto_derived_showable_on_heap_struct() {
    // Structural derivation would cycle on graphs: heap structs need an
    // explicit conformance.
    let typed = flow_driver(
        "struct Node 'heap {\n\tlet value: Int\n}\nprint(Node(value: 1))\n0",
    );
    assert!(
        typed.has_errors(),
        "auto-derived Showable on 'heap must be rejected"
    );
}

#[test]
fn cross_file_global_move_drops_once() {
    let file_a = "public let shared = \"hello\" + \" world\"";
    let file_b = "use { shared } from ./a.tlk\nlet taken = shared\ntaken.length";
    let typed = Driver::new(
        vec![
            Source::in_memory("a.tlk".into(), file_a),
            Source::in_memory("b.tlk".into(), file_b),
        ],
        DriverConfig::new("CrossFile"),
    )
    .parse()
    .expect("parse")
    .resolve_names()
    .expect("resolve")
    .type_check();
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
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(11));
    assert_eq!(
        evaluator.live_allocations(),
        0,
        "the moved global drops exactly once"
    );
}

// ----- Unsafe gating ----------------------------------------------------------

#[test]
fn rejects_raw_pointer_usage_in_safe_source() {
    assert_error_contains(
        "let p = _alloc<Int>(1)\n0",
        "only available in core or sources marked '// unsafe'",
    );
}

#[test]
fn allows_raw_pointer_usage_in_unsafe_source() {
    assert_no_errors("// unsafe\nlet p = _alloc<Int>(1)\n0");
}

// ----- ADR 0010: flow analysis on the MIR CFG ----------------------------------

/// Bug 2 (ADR 0010): a `break`'s early-exit drops are target-relative — a
/// linear value declared BEFORE the loop and consumed after it is fine (the
/// tree walk scheduled every enclosing scope's drops at the break, then
/// rejected the "dropped" linear).
#[test]
fn linear_consumed_after_a_loop_with_break_is_accepted() {
    assert_no_errors(
        "struct Token 'linear {\n\tlet id: Int\n\tconsuming func close() -> Int {\n\t\tself.id\n\t}\n}\nfunc make() -> Int {\n\tlet token = Token(id: 1)\n\tlet i = 0\n\tloop i < 3 {\n\t\ti = i + 1\n\t\tif i == 2 {\n\t\t\tbreak\n\t\t}\n\t}\n\ttoken.close()\n}",
    );
}

/// The false UseAfterMove (ADR 0010 context): a value moved before a
/// branch and reassigned in EVERY branch is initialized at the join — the
/// tree walk merged arm states INTO the pre-branch state, so the stale
/// move survived the join.
#[test]
fn move_reassigned_in_every_branch_is_accepted() {
    assert_no_errors(
        "func consume(s: String) -> Int {\n\ts.length\n}\nfunc f(flag: Bool) -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet n = consume(s)\n\tif flag {\n\t\ts = \"c\" + \"d\"\n\t} else {\n\t\ts = \"e\" + \"f\"\n\t}\n\tconsume(s) + n\n}",
    );
}

/// Bug 1 (ADR 0010), error side: a value moved on a conditional path
/// ending in `continue` reaches the loop head as moved — using it on the
/// next iteration is a use-after-move. The tree walk discarded the
/// diverging arm's state at the if-join and ACCEPTED this program; it then
/// double-freed at runtime.
#[test]
fn move_on_conditional_continue_path_is_use_after_move_on_reentry() {
    assert_error_contains(
        "func consume(s: String) -> Int {\n\ts.length\n}\nfunc f() -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet i = 0\n\tlet n = 0\n\tloop i < 2 {\n\t\ti = i + 1\n\t\tif i == 1 {\n\t\t\tn = consume(s)\n\t\t\tcontinue\n\t\t}\n\t}\n\tn\n}\nf()",
        "Use of moved value 's'",
    );
}

/// Bug 1 (ADR 0010), runtime side: a value moved on one `break` path and
/// live on another is may-moved at the loop exit — its drop is
/// flag-guarded (Conditional), never unconditional. The tree walk believed
/// it live (both arms diverge, states discarded) and emitted a static
/// double-freeing drop.
#[test]
fn move_on_conditional_break_path_drops_once() {
    let (value, _, live_allocations) = run_heap_eval(
        "func consume(s: String) -> Int {\n\ts.length\n}\nfunc f(flag: Bool) -> Int {\n\tlet s = \"a\" + \"b\"\n\tlet n = 0\n\tloop {\n\t\tif flag {\n\t\t\tn = consume(s)\n\t\t\tbreak\n\t\t}\n\t\tbreak\n\t}\n\tn\n}\nf(true) + f(false)",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(2));
    assert_eq!(live_allocations, 0, "the moved value drops exactly once");
}

/// A loop-local live at a `break` drops on the break path (the early-exit
/// candidates at the break are the authority; ADR 0010 observed lowering's
/// stack-derived compensation leaking here).
#[test]
fn live_loop_local_drops_on_break_path() {
    let (value, _, live_allocations) = run_heap_eval(
        "func f() -> Int {\n\tlet i = 0\n\tloop i < 3 {\n\t\ti = i + 1\n\t\tlet s = \"a\" + \"b\"\n\t\tif i == 2 {\n\t\t\tbreak\n\t\t}\n\t\tlet n = s.length\n\t}\n\t7\n}\nf()",
    );
    assert_eq!(value, crate::lambda_g::eval::EvalValue::I64(7));
    assert_eq!(live_allocations, 0, "the loop-local drops on the break path too");
}
