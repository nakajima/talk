//! Flow-checker tests: the ported legacy move/drop corpus (from
//! `src/ownership`'s suite) plus the new linear must-consume behaviors, all
//! running with `CheckerKind::Flow`. Sources are kept byte-identical to the
//! legacy tests they port so parity is auditable.

use crate::compiling::driver::{CheckerKind, Driver, DriverConfig, Source, Typed};
use crate::diagnostic::AnyDiagnostic;

fn flow_driver(source: &str) -> Driver<Typed> {
    let mut config = DriverConfig::new("FlowTest");
    config.checker = CheckerKind::Flow;
    Driver::new(vec![Source::from(source)], config)
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

fn kinds(drops: &[DropSchedule]) -> Vec<DropElaboration> {
    drops.iter().map(|schedule| schedule.kind).collect()
}

#[test]
fn straight_line_owned_local_drops_static_at_scope_exit() {
    let driver = flow_driver("func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\t1\n}");
    let body = func_body(&driver, "make");
    assert_eq!(kinds(&body.drops), vec![DropElaboration::Static]);
    assert_eq!(body.drops[0].reason, DropReason::ScopeExit);
}

#[test]
fn aggregate_move_makes_source_scope_drop_dead() {
    let driver = flow_driver(
        "func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet pair = (s, 1)\n\t0\n}",
    );
    let body = func_body(&driver, "make");
    // Reverse declaration order: `pair` (live) drops first, then `s` (moved).
    assert_eq!(
        kinds(&body.drops),
        vec![DropElaboration::Static, DropElaboration::Dead]
    );
}

#[test]
fn branch_move_makes_scope_drop_conditional() {
    let driver = flow_driver(
        "func make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\tlet t = s\n\t\t1\n\t} else {\n\t\t2\n\t}\n\t0\n}",
    );
    let body = func_body(&driver, "make");
    assert_eq!(kinds(&body.drops), vec![DropElaboration::Conditional]);
}

#[test]
fn field_move_makes_scope_drop_open() {
    let driver = flow_driver(
        "struct Person {\n\tlet name: String\n\tlet age: Int\n}\nfunc make() -> Int {\n\tlet person = Person(name: \"Pat\" + \"!\", age: 40)\n\tlet name = person.name\n\tperson.age\n}",
    );
    let body = func_body(&driver, "make");
    // Reverse declaration order: `name` (live), then `person` (partly moved).
    assert_eq!(
        kinds(&body.drops),
        vec![DropElaboration::Static, DropElaboration::Open]
    );
}

#[test]
fn early_exit_schedules_enclosing_scope_drops() {
    let driver = flow_driver(
        "func make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\treturn 1\n\t}\n\ts.length\n}",
    );
    let body = func_body(&driver, "make");
    // Find the return statement inside the if's then-block.
    let mut early: Option<Vec<DropSchedule>> = None;
    for node in &body.body {
        if let hir::Node::Stmt(stmt) = node
            && let hir::StmtKind::If(_, then_block, _) = &stmt.kind
        {
            for inner in &then_block.body {
                if let hir::Node::Stmt(inner_stmt) = inner
                    && matches!(inner_stmt.kind, hir::StmtKind::Return(_))
                {
                    early = Some(inner_stmt.drops.clone());
                }
            }
        }
    }
    let early = early.expect("return statement with drops");
    assert_eq!(early.len(), 1, "{early:?}");
    assert_eq!(early[0].kind, DropElaboration::Static);
    assert_eq!(early[0].reason, DropReason::EarlyExit);
}

#[test]
fn assignment_schedules_replace_drop() {
    let driver = flow_driver(
        "func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\ts = \"new\" + \" value\"\n\ts.length\n}",
    );
    let body = func_body(&driver, "make");
    let mut replace: Option<Vec<DropSchedule>> = None;
    for node in &body.body {
        if let hir::Node::Stmt(stmt) = node
            && matches!(stmt.kind, hir::StmtKind::Assignment(..))
        {
            replace = Some(stmt.drops.clone());
        }
    }
    let replace = replace.expect("assignment statement with drops");
    assert_eq!(replace.len(), 1, "{replace:?}");
    assert_eq!(replace[0].kind, DropElaboration::Static);
    assert_eq!(replace[0].reason, DropReason::AssignmentReplace);
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
        "linear struct Token {\n\tlet id: Int\n}\nfunc make() -> Int {\n\tlet token = Token(id: 1)\n\t0\n}",
        "is linear and must be consumed",
    );
}

#[test]
fn linear_value_consumed_by_consuming_method_is_accepted() {
    assert_no_errors(
        "linear struct Token {\n\tlet id: Int\n\tconsuming func close() -> Int {\n\t\tself.id\n\t}\n}\nfunc make() -> Int {\n\tlet token = Token(id: 1)\n\ttoken.close()\n}",
    );
}

#[test]
fn linear_value_moved_in_one_branch_only_is_rejected() {
    assert_error_contains(
        "linear struct Token {\n\tlet id: Int\n\tconsuming func close() -> Int {\n\t\tself.id\n\t}\n}\nfunc make(flag: Bool) -> Int {\n\tlet token = Token(id: 1)\n\tif flag {\n\t\ttoken.close()\n\t} else {\n\t\t0\n\t}\n}",
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
    let mut config = DriverConfig::new("FlowVmTest");
    config.checker = CheckerKind::Flow;
    let typed = Driver::new(vec![Source::from(source)], config)
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

// ----- Differential: flow drop schedules ≡ legacy drop elaboration ------------

/// Every drop the flow checker schedules that will actually emit (kind !=
/// Dead) must match the legacy checker's drop-plan obligations for the same
/// source, and vice versa. Dead entries are excluded because the two sides
/// disagree only on where they bother *recording* a no-op: flow also checks
/// synthesized init bodies (scheduling Dead replace-drops for first-time
/// field writes) that legacy never visits. Flow's exact Dead placements are
/// pinned by the unit tests above. This differential replaces a throwaway
/// lowering shim: P3 re-points lowering at the annotations; until then this
/// pins their equivalence.
#[test]
fn flow_drop_schedules_match_legacy_obligations() {
    let corpus: &[&str] = &[
        "func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\t1\n}",
        "func make() -> Int {\n\tlet s = \"hello\" + \" world\"\n\tlet pair = (s, 1)\n\t0\n}",
        "func make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\tlet t = s\n\t\t1\n\t} else {\n\t\t2\n\t}\n\t0\n}",
        "struct Person {\n\tlet name: String\n\tlet age: Int\n}\nfunc make() -> Int {\n\tlet person = Person(name: \"Pat\" + \"!\", age: 40)\n\tlet name = person.name\n\tperson.age\n}",
        "func make(flag: Bool) -> Int {\n\tlet s = \"hello\" + \" world\"\n\tif flag {\n\t\treturn 1\n\t}\n\ts.length\n}",
    ];
    for source in corpus {
        let legacy = legacy_scope_drops(source);
        let flow = flow_scope_drops(source);
        assert_eq!(
            flow, legacy,
            "flow schedules diverge from legacy obligations for:\n{source}"
        );
    }
}

/// Legacy: (root name, kind, reason) for every drop obligation, sorted.
fn legacy_scope_drops(source: &str) -> Vec<(String, String, String)> {
    let driver = Driver::new(
        vec![Source::from(source.to_string().leak() as &str)],
        DriverConfig::new("FlowDiffLegacy"),
    )
    .parse()
    .expect("parse")
    .resolve_names()
    .expect("resolve")
    .type_check();
    assert!(!driver.has_errors(), "{:?}", driver.diagnostics());
    let names = &driver.phase.types.display_names;
    let mut out: Vec<(String, String, String)> = driver
        .phase
        .ownership
        .drop_plan
        .obligations
        .iter()
        .filter(|obligation| format!("{:?}", obligation.kind) != "Dead")
        .map(|obligation| {
            let name = names
                .get(&obligation.key_path.root)
                .cloned()
                .unwrap_or_else(|| format!("{}", obligation.key_path.root));
            (
                name,
                format!("{:?}", obligation.kind),
                format!("{:?}", obligation.reason),
            )
        })
        .collect();
    out.sort();
    out
}

/// Flow: (root name, kind, reason) for every schedule annotated onto the
/// HIR (blocks and statements), sorted.
fn flow_scope_drops(source: &str) -> Vec<(String, String, String)> {
    let driver = flow_driver(source.to_string().leak());
    assert!(!driver.has_errors(), "{:?}", driver.diagnostics());
    let names = &driver.phase.types.display_names;
    let mut collector = ScheduleCollector { out: vec![] };
    for file in driver.phase.hir.values() {
        for root in &file.roots {
            use derive_visitor::Drive;
            root.drive(&mut collector);
        }
    }
    let mut out: Vec<(String, String, String)> = collector
        .out
        .iter()
        .filter(|schedule| schedule.kind != DropElaboration::Dead)
        .map(|schedule| {
            let name = names
                .get(&schedule.place.root)
                .cloned()
                .unwrap_or_else(|| format!("{}", schedule.place.root));
            (
                name,
                format!("{:?}", schedule.kind),
                format!("{:?}", schedule.reason),
            )
        })
        .collect();
    out.sort();
    out
}

#[derive(derive_visitor::Visitor)]
#[visitor(hir::Block(enter), hir::Stmt(enter))]
struct ScheduleCollector {
    out: Vec<DropSchedule>,
}

impl ScheduleCollector {
    fn enter_block(&mut self, block: &hir::Block) {
        self.out.extend(block.drops.iter().cloned());
    }

    fn enter_stmt(&mut self, stmt: &hir::Stmt) {
        self.out.extend(stmt.drops.iter().cloned());
    }
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
