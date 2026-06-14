# Parity test audit: the previous backend's suites, dispositioned

Every test from the pre-rewrite tree (`6a602348^`) is accounted for
here: **covered** (an existing new test pins the same behavior),
**ported** (a new test added by this audit), **adapted** (ported with a
deliberate change, explained), or **N/A** (tied to deleted machinery,
with the reason). New tests live in `src/vm/vm_tests.rs` unless noted.

Fixes that fell out of this audit (each loud before, broken or silent):
nested/anonymous record member reads and assignments (records are λ_G
tuples — extract/rebuild, not GetField/SetField), functions mutating
top-level bindings (`top_level_cells` registry), main's and blocks'
value types derived from the *final* node only (a trailing loop or
assignment yields Void), unannotated lets taking the rhs's inferred
type (variant patterns see a concrete head), self-contained handlers no
longer forcing the abort-capable convention (`handlers_defined`
subtraction + `Ctx::local_handlers`), solver-inferred associated-type
bindings written back to conformance rows, negative io counts passing
through, and parametered trailing blocks.

## src/ir/interpreter.rs (127 tests)

| Old test | Disposition |
|---|---|
| empty_is_void | ported — `on_empty_program` |
| prints / print_displays_unit | covered — `on_hello_world`; REPL `values_render_talk_style` pins `()` |
| int / float / add_int / sub / mul / div | covered — `on_arithmetic` + REPL render tests |
| record_literal | ported — `on_record_literal_members` |
| struct_field | covered — `on_memberwise_struct` |
| generic_struct_field | ported — `on_generic_struct_field` |
| add_method / fib | covered — `on_calls`, `on_fib` |
| matching | ported — `on_literal_match` |
| interprets_comparisons / not / or / and | ported — `on_comparisons_and_logic` |
| interprets_if_expr | covered — `on_branches` |
| interprets_string_plus | covered — `on_string_concat` |
| interprets_greet_regression / struct_print_example | covered — `on_struct_example` (Struct.tlk) |
| interprets_closure | covered — closure tests (M6) |
| interprets_mut_closure | ported — `on_top_level_mut_closure` (drove the `top_level_cells` fix) |
| interprets_nested_closure | ported — `on_nested_closure_returned_as_value` |
| early_return_skips_following_side_effects | ported — `on_early_return_skipping_side_effects` |
| interprets_nested_lvalue_assignment | ported — `on_nested_record_field_assignment` (drove the record-member fixes) |
| imports_first_class_external_function_references | ported — `on_core_function_as_value` |
| explicit_main_function_is_entrypoint | ported — `on_explicit_main_entrypoint` + 2 more (feature reinstated) |
| interprets_counter | ported — `on_independent_counters` |
| interprets_array_literal_properties / array_get | covered — Array.tlk example |
| interprets_simple_match | covered — M4 enum tests |
| interprets_unqualified_variant_arg | ported — `on_unqualified_variant_argument` |
| interprets_or_pattern_in_let | ported — `on_or_pattern_in_a_let` (parser desugar added) |
| interprets_or_pattern_falls_through_to_next_arm | ported — `on_or_pattern_falling_through_arms` |
| formats_record / formats_struct_instance / formats_enum_variant | covered — REPL `records_and_variants_render_with_their_names` (struct format unified with derived show: `Name(field: v)`) |
| formats_array | N/A — `#[ignore]`d in the old tree; array show covered below |
| interprets_protocol_example | ported — `on_protocol_defaults_with_associated_types` (drove the assoc write-back fix) |
| interprets_effect_call / interprets_effect_handler_resume_value | covered — M9 resume tests (old `'[fizz]` row syntax is now `'fizz`) |
| effect_handlers_for_same_effect_have_unique_symbols | ported — `on_handlers_in_two_functions` (drove the self-contained-handler fix) |
| interprets_throw_with_effect_handler | covered — M7 abort tests |
| interprets_nested_extend_method / _with_self_access | ported — `on_nested_extend_with_self_access` |
| interprets_nested_extend_method_with_generic | adapted — `on_nested_extend_with_generics` (generic protocols became associated types in the new type system) |
| interprets_nested_extend_method_with_array | covered — Array.tlk + conditional-conformance tests |
| interprets_array_iter_method / iterator_simple / iterator | covered — Iteratin.tlk + iterator tests |
| interprets_io_open_and_close / interprets_io_open_write_read | N/A — the `io_open` @_ir splice with a Talk String was retired; `open_path` (pure Talk, NUL-copied) is the surface, pinned by `on_open_path` |
| io_open_with_unterminated_rawptr_returns_einval | N/A — semantics changed: the NUL scan stops at end of memory (host open then fails with its own errno); EINVAL-on-unterminated was an old-interpreter check |
| interprets_io_close_invalid_fd | covered — `on_io_error_returns` (EBADF) |
| interprets_io_sleep | covered — `on_statically_routed_sleep` |
| interprets_io_socket_bind_listen_accept / _returns_valid_fd / io_connect / io_accept_returns_valid_fd / interprets_socket_via_core_functions | covered — `on_socket_loopback`, `on_server_accept_script` |
| io_write_with_negative_count_does_not_panic / io_read_… | ported — `on_negative_io_counts_pass_through` (behavior reinstated in both engines) |
| interprets_optional_match / interprets_core_optional_match | covered — M4/M5 Optional tests; ported — `on_match_on_an_unannotated_next` |
| interprets_simple_loop_break | covered — Loop.tlk example |
| interprets_match_with_conditional_and_break | ported — `on_match_with_break_in_an_arm` (drove the unannotated-let inference fix) |
| interprets_let_binding_of_enum_param | ported — `on_match_on_a_rebound_enum_param` |
| interprets_let_else | covered — `on_let_else` (this audit's earlier phase) |
| auto_derives_show_for_generic_enum | covered — derived-show tests (Optional) |
| interprets_io_write_to_stdout | covered — FileIO.tlk + write_string tests |
| interprets_write_string_to_stdout / interprets_print_raw | N/A as written (the old `'io` handler shape differs); behavior covered by FileIO.tlk |
| interprets_trailing_block_as_function_arg / _with_side_effects | covered — `on_trailing_blocks` |
| interprets_trailing_block_with_params | ported — `on_parametered_trailing_blocks` (feature implemented by this audit) |
| interprets_int_show_inline | N/A — redundant with show + loop tests |
| interprets_int_show / _zero / _negative / bool_show_* / string_show / float_show / _zero / _negative | ported — `on_show_for_scalars` (floats also in Show.tlk) |
| interprets_string_equals / slice / find / find_from | ported — `on_string_operations` |
| interprets_struct_auto_show / _empty / enum_auto_show_* | ported — `on_show_for_empty_and_payloadless`, `on_show_with_multiple_payloads` |
| interprets_struct_auto_show_user_override | ported — `on_show_override` |
| interprets_struct_with_unshowable_field_no_error | ported — `on_unshowable_fields_stay_lazy` |
| interprets_struct_auto_show_via_generic | ported — `on_show_through_a_generic_bound` |
| interprets_binding_survives_early_return_branch | ported — `on_binding_surviving_an_early_return_branch` |
| interprets_float_trunc_then_show | ported — `on_float_trunc_then_show` |
| interprets_float_show_int_part_only | covered — Show.tlk |
| interprets_trunc / interprets_itof | ported — `on_trunc_and_itof_splices` |
| interprets_generic_struct_auto_show | ported — `on_generic_struct_show_erases_arguments` |
| interprets_func_show / _via_generic / struct_with_func_field_show | **not ported** — Showable for function types (rendering a closure as its type) is not implemented in the new checker; tracked as a known feature gap below |
| loop_with_function_calls_and_io | ported — `on_loop_with_calls_and_io` |
| loop_alloc_read_write_echo | ported — `on_echo_loop_over_two_connections` (drove the block-value-type fix) |
| chat_server_echo_with_prefix / _full_pattern_with_print / _echo_to_client_fd / heap_write_to_non_stdout_fd | covered — `on_server_accept_script`, `on_socket_loopback`, `on_read_loop_with_split_writes` (fd-content introspection was an old-CaptureIO detail) |
| read_loop_receives_split_writes | ported — `on_read_loop_with_split_writes` |
| loop_let_initializer_not_evaluated_before_loop / _immutable_not_duplicated | ported — `on_loop_lets_not_evaluated_before_loop` |
| pure_method_calls_do_not_clobber_receiver_bindings | ported — `on_pure_method_calls_not_clobbering_receivers` |
| http_server_handles_registered_route / _returns_404 / _rejects_non_get / _executes_handler_per_request / _handles_multiple_registered_routes | ported — the five `on_http_*` tests |
| real_socketpair_io_read_write | ported — `vm_round_trips_heap_bytes_through_a_real_socketpair` |
| real_socketpair_full_server_echo / _loop_iteration_echo | covered — the socketpair port + `on_echo_loop_over_two_connections` exercise the same marshaling |
| conditional_conformance_array_show | ported — `on_array_show_through_conditional_conformance` |

**Known gap, deliberately unported:** `Showable` for function values
(`(func(x: Int) -> Int { x }).show()` → `"(Int) -> Int"`, 3 old tests).
Requires a conformance rule for arrow types in the solver plus a
synthesized show witness rendering the static type. Diagnosed cleanly
today (`NotConforming`).

## src/types tests (types_tests.rs 166 + effects_tests.rs 17)

**170 of the 183 old cases replay verbatim against the new checker** in
`types_tests::previous_checker_suite_behaviors_hold` (a table-driven
regression test generated from the old sources; clean-vs-error
expectations preserved). Fixes that fell out: extra explicit type
arguments are rejected again (`id<Int, Bool>(1)`); handler blocks must
name all of an effect's payloads or none; **generic methods** carry
their declared generics as scheme parameters (instantiated fresh per
call, monomorphized per instantiation); **methods on enums** dispatch
exactly like struct methods; and **record projections generalize over
rows** — a member constraint no nominal or protocol owns defaults the
receiver to an open record row at the solver's improvement step
(Gaster & Jones, POPL 1996; Leijen, Trends in FP 2005), the row tail
generalizes, and monomorphization splices each call's concrete row
into the signature (`Ty::substitute` row splicing + row instantiation
recording), so `func f(r) { r.a }` runs on both engines with per-θ
field indices. Stuck member constraints with concrete heads also float
to the final solve now (group ordering no longer mis-reports a pending
signature as an unknown member).

The 13 cases not in the table, each with its reason:

**Deliberate design changes** (the new type system means something
different here):
- `types_nested_generalized_funcs`, `generalizes_locals`,
  `row_generalizes_in_local_let_when_fresh` — local bindings are
  monomorphic (MonoLocalBinds; OutsideIn(X) §4.2). The old checker
  generalized locals.
- `rejects_ambiguous_protocol_member_requirement` — the old checker
  errored on a member resolvable through one bound while another
  protocol of the same name existed; the new resolution is unambiguous
  and accepts it.
- `checks_handler_return` — abort values now type against the *handled
  scope* (M7 semantics, enforced by the lowering's types + verifier),
  not the effect's declared return.
- `func_type_annotation_on_let_is_honored` — annotations no longer
  auto-quantify free type names (`let id: (T) -> T = …` needs declared
  generics).

**Nominal member constraints generalize** (qualified types — Jones
1994): `types_struct_method_on_arg` now passes as
`member_constraints_generalize_into_schemes`. A member use on an
unknown receiver rides the binder's scheme
(`Scheme.member_constraints`) and each instantiation re-emits and
discharges it against its concrete receiver; the lowerer resolves the
member per specialization by label (struct/enum methods, then protocol
witnesses). Covered by `member_constraints_*` in types_tests and
`vm_matches_evaluator_on_member_constrained_functions` (methods,
fields, and a mixed struct/record receiver) two-engine. Two old tests
pinned the superseded unique-owner improvement and were updated:
`member_on_unknown_improves_to_unique_nominal` →
`member_on_unknown_generalizes_with_a_constraint` (the receiver stays
polymorphic), `ambiguous_member_errors` →
`member_owned_by_two_protocols_rides_the_scheme` (a use owned by
several protocols is no longer an error at the definition; each call
site discharges it). Unique-owner improvement still runs, but only as
last-resort defaulting in the final solve. Discharge against a
receiver whose conformances (or bounds) provide the label more than
once is an `AmbiguousMember` error suggesting the protocol-static
forms (`Aa.m(…)`), with LSP quick-fixes that apply the rewrite —
`ambiguous_member_use_suggests_the_explicit_forms`,
`ambiguous_member_via_scheme_constraint_errors_at_the_call`,
`ambiguous_member_quick_fix_offers_each_protocol`.

**Known gaps** (real features the old checker had):
- `types_as` — protocol-typed values (`A() as Fizz` — existentials).
- `extend_with_concrete_type_arg` — inherent extends with partially
  concrete type arguments (`extend Pair<Y, Void>`).

**Old-checker internals**: `param_collect_metas_is_empty` (asserts an
internal API of the deleted solver).

## Other old suites

- `src/ir/lowerer_tests.rs` (39) — lowered the deleted IR; behaviors
  covered transitively by the two-engine suite above.
- `src/ir/instruction.rs` / `executor.rs` (12) — deleted-machine
  internals; the executor was the unfinished async runtime.
- `src/compiling/core.rs` (7 → 1) — the old module-cache machinery
  (callee facts, cache roundtrips) does not exist in this architecture.
- `src/types/matcher.rs` (6), `constraints/store.rs`,
  `constraints/row_subset.rs` (6) — old-solver internals; the new
  solver has its own six tests in `solve.rs`.
- `src/lsp/server.rs` (27 → 27) and `src/analysis/hover.rs` (9 → 6+5) —
  hover and goto-on-variant-pattern restored and re-tested during this
  audit.
