# Commit-by-commit review: `bigdiff2` against `main`

Reviewed 145 commits reachable from `HEAD` but not `main`, in reverse topological order. Every non-merge commit is reviewed against its parent; merge commits are reviewed against their first parent, with merged lane commits reviewed separately.

## Overall verdict

**Request changes.** The branch tip has two CI-blocking defects and one additional debug-error invariant violation. Historical validation also found two non-compiling commits and four deterministic test-red commits that were repaired only by later changes.

### Unresolved findings

1. **P1 - `a1d20d27`: stale fuzz CI command.** The commit deletes both `tests/fuzz.rs` and `fuzz-tests` but leaves CI invoking them. The command fails immediately.
2. **P1 - `cabfc772`: capture-list diagnostics panic in debug builds.** The commit calls `BackendError::unsupported` with messages that violate its asserted contract. The branch CI test suite is currently 90/91 for `tests/talk_tests.rs`.
3. **P2 - `85750ccd`: mut-rvalue backend diagnostic has the same constructor/message mismatch.** The common frontend path masks it, but the backend invariant remains violated.

### Historical atomicity findings

- **P1 - `dbf5187a`:** six MIR-lowering fixtures fail after the verifier starts requiring complete cleanup; fixed by `b73ad318`.
- **P1 - `a1a0ba90`:** exact checkout fails with 46 Rust errors.
- **P1 - `fc289263`:** exact checkout fails with 4 Rust errors; fixed by `1fb9946b`.
- **P1 - `0a968e67`:** the lane-B merge enables a generic package fixture without updating its fail-closed test; fixed by `0a9ead59`.
- **P1 - `575c7f3b`:** enabling whole-program check mode leaves the measured flow remainder stale; fixed by `8150b4b8`.
- **P1 - `4cec14e4`:** new borrow-conflict wording lands before its exact error oracles; fixed by `aa3e820f`.

## Validation performed at branch tip

| Command | Result |
|---|---|
| `cargo build --workspace --all-targets --locked` | Pass |
| `cargo fmt --all -- --check` | Pass |
| `cargo test --workspace --all-targets` | Fail: `run_enforces_capture_list_modes` |
| `cargo test --test fuzz --features fuzz-tests --locked` | Fail: feature/target no longer exists |
| `cargo test -p talk-runtime --locked` | Pass: 30 tests |
| `cargo test -p talk-c --locked` | Pass: 3 tests |
| `cargo test -p talk-wasm --locked` | Pass |
| `cargo test -p talk-static --locked` | Pass |
| `swift test -Xlinker -L -Xlinker "$PWD/target/debug"` | Pass: 4 tests |
| `cargo run --quiet -- test` | Pass: 18 Talk package tests |
| `git diff --check main...HEAD` | One intentional exact-output trailing space; see commit 092 |

In addition, `cargo check --all-targets --locked --quiet` was run at every commit that changed Rust or Cargo inputs: 114 passed and 2 failed. Twenty-nine documentation/language-fixture-only commits were inspected without rebuilding. The default `cargo test --locked --quiet` suite was executed at all 145 historical checkouts: 81 passed and 64 failed. Most failures are inherited runs of the unresolved `cabfc772` capture-list defect; the per-commit documents identify the root or inherited failure and record one non-reproduced BrokenPipe race separately.

`cargo clippy --workspace --all-targets -- -D warnings` was also sampled at the tip and is not green (nine lint failures). Clippy is not configured as a CI gate, so those warnings are not elevated to commit-blocking findings here.

## Reviews

| # | Commit | Subject | Result |
|---:|---|---|---|
| 001 | [`fc4696b1`](001-fc4696b1-big-diff.md) | big diff | No commit-local blocker identified |
| 002 | [`d7943b78`](002-d7943b78-move-fuzz-tests.md) | move fuzz tests | No commit-local blocker identified |
| 003 | [`eb22cb0c`](003-eb22cb0c-lol.md) | lol | No commit-local blocker identified |
| 004 | [`96249e71`](004-96249e71-fix-never-valued-match-arm-lowering.md) | fix never-valued match arm lowering | No commit-local blocker identified |
| 005 | [`a1d20d27`](005-a1d20d27-reset-compiler-to-frontend-only.md) | reset compiler to frontend-only | Request changes |
| 006 | [`f2b1d759`](006-f2b1d759-stabilize-typedprogram-semantic-seam.md) | stabilize TypedProgram semantic seam | No commit-local blocker identified |
| 007 | [`5f70a6f2`](007-5f70a6f2-stage-0-checkpoint.md) | stage 0 checkpoint | No commit-local blocker identified |
| 008 | [`7b876a65`](008-7b876a65-lower-copy-only-mir-to-talk-ir.md) | lower copy-only MIR to Talk IR | No commit-local blocker identified |
| 009 | [`bdb74959`](009-bdb74959-generate-verified-copy-only-mir-cfgs.md) | generate verified Copy-only MIR CFGs | No commit-local blocker identified |
| 010 | [`fad56b6a`](010-fad56b6a-test-typed-to-talk-ir-copy-handshake.md) | test typed to Talk IR Copy handshake | No commit-local blocker identified |
| 011 | [`4c541321`](011-4c541321-track-backend-implementation-and-contract-gaps.md) | track backend implementation and contract gaps | No commit-local blocker identified |
| 012 | [`761a7994`](012-761a7994-close-callable-copy-and-ownership-contract-gaps.md) | close callable copy and ownership contract gaps | No commit-local blocker identified |
| 013 | [`74b9fc9e`](013-74b9fc9e-cleanup.md) | cleanup | No commit-local blocker identified |
| 014 | [`7ecba6b3`](014-7ecba6b3-lower-verified-mir-forms-to-talk-ir.md) | lower verified MIR forms to Talk IR | No commit-local blocker identified |
| 015 | [`1e22b4c7`](015-1e22b4c7-fix-talk-ir-close-entry-and-indirect-call-gaps.md) | fix(talk-ir): close entry and indirect call gaps | No commit-local blocker identified |
| 016 | [`dbf5187a`](016-dbf5187a-add-narrow-affine-mir-ownership-checking.md) | add narrow affine MIR ownership checking | Standalone defect, repaired later |
| 017 | [`266ba155`](017-266ba155-fix-mir-close-affine-ownership-verifier-gaps.md) | fix(mir): close affine ownership verifier gaps | No new finding; inherited red state |
| 018 | [`4ac8368e`](018-4ac8368e-fix-mir-close-ownership-state-bypasses.md) | fix(mir): close ownership state bypasses | No new finding; inherited red state |
| 019 | [`b73ad318`](019-b73ad318-test-ir-align-lowering-fixtures-with-checked-mir-cleanup.md) | test(ir): align lowering fixtures with checked MIR cleanup | No commit-local blocker identified |
| 020 | [`14691b54`](020-14691b54-docs-add-cross-artifact-integration-laws.md) | docs: add cross-artifact integration laws | No commit-local blocker identified |
| 021 | [`a1a0ba90`](021-a1a0ba90-implement-canonical-typedprogram-types-lane.md) | implement canonical TypedProgram types lane | Standalone defect, repaired later |
| 022 | [`fc289263`](022-fc289263-close-canonical-callable-and-copy-evidence-seam.md) | close canonical callable and Copy evidence seam | Standalone defect, repaired later |
| 023 | [`1fb9946b`](023-1fb9946b-fix-typed-program-review-blockers.md) | fix typed program review blockers | No commit-local blocker identified |
| 024 | [`a364a34b`](024-a364a34b-complete-typed-program-integration-laws.md) | complete typed program integration laws | No commit-local blocker identified |
| 025 | [`4f890f2c`](025-4f890f2c-enforce-semantic-occurrence-completeness.md) | enforce semantic occurrence completeness | No commit-local blocker identified |
| 026 | [`d84fe589`](026-d84fe589-align-occurrence-lookup-and-initializer-completeness.md) | align occurrence lookup and initializer completeness | No commit-local blocker identified |
| 027 | [`03128941`](027-03128941-validate-exact-initializer-ownership.md) | validate exact initializer ownership | No commit-local blocker identified |
| 028 | [`48f2956b`](028-48f2956b-docs-mark-typed-program-cutover-integrated.md) | docs: mark typed program cutover integrated | No commit-local blocker identified |
| 029 | [`8e79d3fe`](029-8e79d3fe-docs-add-backend-feature-parity-roadmap.md) | docs: add backend feature parity roadmap | No commit-local blocker identified |
| 030 | [`1ccb324c`](030-1ccb324c-test-freeze-backend-parity-corpus-oracles.md) | test: freeze backend parity corpus oracles | No commit-local blocker identified |
| 031 | [`8fb25e57`](031-8fb25e57-docs-disposition-archived-backend-tests.md) | docs: disposition archived backend tests | No commit-local blocker identified |
| 032 | [`f74b9ae6`](032-f74b9ae6-docs-specify-e1-scalar-execution-slice.md) | docs: specify E1 scalar execution slice | No commit-local blocker identified |
| 033 | [`536e3efb`](033-536e3efb-compiler-add-target-neutral-scalar-intrinsics.md) | compiler: add target-neutral scalar intrinsics | No commit-local blocker identified |
| 034 | [`e179fb70`](034-e179fb70-frontend-canonicalize-scalar-inline-ir.md) | frontend: canonicalize scalar inline IR | No commit-local blocker identified |
| 035 | [`bca268e7`](035-bca268e7-frontend-publish-scalar-intrinsic-copy-evidence.md) | frontend: publish scalar intrinsic copy evidence | No commit-local blocker identified |
| 036 | [`b7dc18fb`](036-b7dc18fb-mir-generate-and-verify-scalar-intrinsics.md) | mir: generate and verify scalar intrinsics | No commit-local blocker identified |
| 037 | [`3f36db1f`](037-3f36db1f-talk-ir-lower-and-verify-scalar-intrinsics.md) | talk-ir: lower and verify scalar intrinsics | No commit-local blocker identified |
| 038 | [`9ba7c06a`](038-9ba7c06a-frontend-validate-signed-integer-literals.md) | frontend: validate signed integer literals | No commit-local blocker identified |
| 039 | [`872ba1ea`](039-872ba1ea-runtime-validate-fail-closed-scalar-bytecode.md) | runtime: validate fail-closed scalar bytecode | No commit-local blocker identified |
| 040 | [`5409bf41`](040-5409bf41-bytecode-execute-verified-scalar-talk-ir.md) | bytecode: execute verified scalar talk ir | No commit-local blocker identified |
| 041 | [`17700926`](041-17700926-cli-run-validated-scalar-bytecode.md) | cli: run validated scalar bytecode | No commit-local blocker identified |
| 042 | [`2f55dc3c`](042-2f55dc3c-frontend-publish-protocol-static-witnesses.md) | frontend: publish protocol static witnesses | No commit-local blocker identified |
| 043 | [`3d7f8247`](043-3d7f8247-talk-ir-link-exact-scalar-suppliers.md) | talk-ir: link exact scalar suppliers | No commit-local blocker identified |
| 044 | [`481f2c2a`](044-481f2c2a-talk-ir-link-real-scalar-source-modules.md) | talk-ir: link real scalar source modules | No commit-local blocker identified |
| 045 | [`bd5ac7c0`](045-bd5ac7c0-e2-initialize-linked-scalar-globals.md) | e2: initialize linked scalar globals | No commit-local blocker identified |
| 046 | [`fe6b8686`](046-fe6b8686-docs-parallelize-backend-parity-work.md) | docs: parallelize backend parity work | No commit-local blocker identified |
| 047 | [`813c21c8`](047-813c21c8-e2-execute-scalar-package-graphs.md) | e2: execute scalar package graphs | No commit-local blocker identified |
| 048 | [`c4ece55f`](048-c4ece55f-e2-enforce-exact-package-supply.md) | e2: enforce exact package supply | No commit-local blocker identified |
| 049 | [`88618ddd`](049-88618ddd-merge-integrate-lane-a-package-graph.md) | merge: integrate lane A package graph | No commit-local blocker identified |
| 050 | [`4ec07011`](050-4ec07011-l1-specialize-local-scalar-calls.md) | l1: specialize local scalar calls | No commit-local blocker identified |
| 051 | [`d3553154`](051-d3553154-l1-harden-specialization-contracts.md) | l1: harden specialization contracts | No commit-local blocker identified |
| 052 | [`79086d6e`](052-79086d6e-typed-program-reject-monomorphic-instantiation-mappings.md) | typed-program: reject monomorphic instantiation mappings | No commit-local blocker identified |
| 053 | [`0a968e67`](053-0a968e67-merge-integrate-lane-b-local-specialization.md) | merge: integrate lane B local specialization | Standalone defect, repaired later |
| 054 | [`e3958d0a`](054-e3958d0a-mir-verify-and-query-borrow-provenance-graphs.md) | mir: verify and query borrow provenance graphs | No commit-local blocker identified |
| 055 | [`ebf07ef7`](055-ebf07ef7-lsp-render-verified-borrow-provenance.md) | lsp: render verified borrow provenance | No commit-local blocker identified |
| 056 | [`bdbcb1a3`](056-bdbcb1a3-mir-bind-provenance-verification-to-structure.md) | mir: bind provenance verification to structure | No commit-local blocker identified |
| 057 | [`535678c8`](057-535678c8-mir-tighten-provenance-relevance-checks.md) | mir: tighten provenance relevance checks | No commit-local blocker identified |
| 058 | [`3d6a736f`](058-3d6a736f-mir-scope-ownership-diagnostics-to-functions.md) | mir: scope ownership diagnostics to functions | No commit-local blocker identified |
| 059 | [`7685abc5`](059-7685abc5-merge-integrate-lane-c-borrow-provenance.md) | merge: integrate lane C borrow provenance | No new finding; inherited red state |
| 060 | [`3a7638a2`](060-3a7638a2-docs-accept-r1-managed-storage-design.md) | docs: accept R1 managed-storage design | No new finding; inherited red state |
| 061 | [`0a9ead59`](061-0a9ead59-integration-prove-package-specialization-coexistence.md) | integration: prove package specialization coexistence | No commit-local blocker identified |
| 062 | [`fc437c88`](062-fc437c88-docs-synchronize-integrated-backend-status.md) | docs: synchronize integrated backend status | No commit-local blocker identified |
| 063 | [`961038ba`](063-961038ba-l1-materialize-imported-scalar-intrinsic-implementations.md) | l1: materialize imported scalar intrinsic implementations | No commit-local blocker identified |
| 064 | [`97d3b16c`](064-97d3b16c-e2-read-immutable-dependency-scalar-globals.md) | e2: read immutable dependency scalar globals | No commit-local blocker identified |
| 065 | [`889992f6`](065-889992f6-restore-scalar-execution-in-talk-c.md) | Restore scalar execution in talk-c | No commit-local blocker identified |
| 066 | [`73759ae6`](066-73759ae6-wasm-run-programs-through-scalar-compiler.md) | wasm: run programs through scalar compiler | No commit-local blocker identified |
| 067 | [`de06bd37`](067-de06bd37-compile-shared-scalar-borrows-with-source-provenance.md) | Compile shared scalar borrows with source provenance | No commit-local blocker identified |
| 068 | [`65c93acf`](068-65c93acf-commit-lean-rebuild-plan.md) | commit lean rebuild plan | No commit-local blocker identified |
| 069 | [`ee03e896`](069-ee03e896-rebuild-the-backend-lean-one-seam-full-corpus-parity.md) | Rebuild the backend lean: one seam, full corpus parity | No commit-local blocker identified |
| 070 | [`ab86dd90`](070-ab86dd90-close-the-group-a-soundness-gaps.md) | Close the group-A soundness gaps | No commit-local blocker identified |
| 071 | [`5329de53`](071-5329de53-close-every-remaining-required-ledger-row-group-b.md) | Close every remaining Required ledger row (group B) | No commit-local blocker identified |
| 072 | [`95d1f6cf`](072-95d1f6cf-close-group-c-surface-ergonomics-fail-closed-fixes-swift-smoke.md) | Close group C: surface ergonomics, fail-closed fixes, Swift smoke | No commit-local blocker identified |
| 073 | [`8957d04d`](073-8957d04d-close-the-remaining-parity-gaps-group-d.md) | Close the remaining parity gaps (group D) | No commit-local blocker identified |
| 074 | [`3ea4f4dd`](074-3ea4f4dd-fix-structural-glue-misfiring-on-nested-rigid-params.md) | Fix structural glue misfiring on nested rigid params | No commit-local blocker identified |
| 075 | [`6dfabcc2`](075-6dfabcc2-compile-generic-effect-payloads-via-witness-passing-group-e.md) | Compile generic effect payloads via witness passing (group E) | No commit-local blocker identified |
| 076 | [`d5e822df`](076-d5e822df-close-every-reachable-backend-gap-group-f.md) | Close every reachable backend gap (group F) | No commit-local blocker identified |
| 077 | [`f6e21959`](077-f6e21959-write-back-mut-requirements-through-dynamic-dispatch.md) | Write back mut requirements through dynamic dispatch | No commit-local blocker identified |
| 078 | [`c76f8431`](078-c76f8431-consolidate-the-writeback-convention-into-one-mechanism.md) | Consolidate the writeback convention into one mechanism | No commit-local blocker identified |
| 079 | [`a936bb64`](079-a936bb64-land-mut-parameters-through-dynamic-dispatch.md) | Land mut parameters through dynamic dispatch | No commit-local blocker identified |
| 080 | [`1fe77809`](080-1fe77809-harden-the-writeback-convention-against-silent-skew-group-g.md) | Harden the writeback convention against silent skew (group G) | No commit-local blocker identified |
| 081 | [`2c018644`](081-2c018644-fix-cross-program-symbol-stamping-and-five-backend-gaps-from-talk-syntax.md) | Fix cross-program symbol stamping and five backend gaps from talk-syntax | No commit-local blocker identified |
| 082 | [`e251f80b`](082-e251f80b-write-back-mut-receivers-through-projection-places.md) | Write back mut receivers through projection places | No commit-local blocker identified |
| 083 | [`cf43effe`](083-cf43effe-owned-match-destructuring-and-implicit-mut-argument-writeback.md) | Owned-match destructuring and implicit mut-argument writeback | No commit-local blocker identified |
| 084 | [`31cf410e`](084-31cf410e-make-talk-test-green-in-the-repo-itself.md) | Make `talk test` green in the repo itself | No commit-local blocker identified |
| 085 | [`ebd8c120`](085-ebd8c120-rewrite-the-plan-around-true-parity.md) | Rewrite the plan around true parity | No commit-local blocker identified |
| 086 | [`4da3e060`](086-4da3e060-audit-the-reference-column-restore-the-baseline-assertmessage-name.md) | Audit the reference column; restore the baseline assertMessage name | No commit-local blocker identified |
| 087 | [`fe4663bf`](087-fe4663bf-audit-the-reference-test-suites-vendor-the-examples-corpus-as-gate-g5.md) | Audit the reference test suites; vendor the examples corpus as gate G5 | No commit-local blocker identified |
| 088 | [`fc1f6943`](088-fc1f6943-refile-the-audit-gaps-into-their-owning-execution-waves.md) | Refile the audit gaps into their owning execution waves | No commit-local blocker identified |
| 089 | [`c8c4d005`](089-c8c4d005-bind-each-reopened-wave-to-a-deepening-obligation.md) | Bind each reopened wave to a deepening obligation | No commit-local blocker identified |
| 090 | [`40593fdf`](090-40593fdf-wave-2-record-patterns-and-record-destructuring.md) | Wave 2: record patterns and record destructuring | No commit-local blocker identified |
| 091 | [`cabfc772`](091-cabfc772-wave-5-cells-capture-lists-letrec-inferred-generic-recursion.md) | Wave 5: cells, capture lists, letrec, inferred-generic recursion | Request changes |
| 092 | [`233dcc49`](092-233dcc49-wave-6-lexical-capability-capture-port-the-reference-effects-suite.md) | Wave 6: lexical capability capture; port the reference effects suite | No new finding; inherited red state |
| 093 | [`a56136fa`](093-a56136fa-fix-arm-owned-temp-lifetimes-watermark-flushes-non-destructive-exits.md) | Fix arm-owned temp lifetimes: watermark flushes, non-destructive exits | No new finding; inherited red state |
| 094 | [`edd2130f`](094-edd2130f-construction-arguments-donate-references-like-call-arguments.md) | Construction arguments donate references like call arguments | No new finding; inherited red state |
| 095 | [`3a635858`](095-3a635858-wave-7-initialize-imported-files-before-their-importers.md) | Wave 7: initialize imported files before their importers | No new finding; inherited red state |
| 096 | [`075a5659`](096-075a5659-make-file-initialization-order-insertion-stable.md) | Make file initialization order insertion-stable | No new finding; inherited red state |
| 097 | [`d471beb9`](097-d471beb9-plan-close-wave-7-and-the-sixteen-failure-burn-down.md) | Plan: close wave 7 and the sixteen-failure burn-down | No new finding; inherited red state |
| 098 | [`21e56b9b`](098-21e56b9b-wave-4-port-the-strings-collections-drops-reference-clusters.md) | Wave 4: port the strings/collections/drops reference clusters | No new finding; inherited red state |
| 099 | [`bdc7190e`](099-bdc7190e-plan-close-wave-4-gates-g3-g5-g6-at-full-green.md) | Plan: close wave 4; gates G3/G5/G6 at full green | No new finding; inherited red state |
| 100 | [`6ab0c3ec`](100-6ab0c3ec-wave-3-port-the-reference-flow-rule-corpus-as-a-measured-gate.md) | Wave 3: port the reference flow-rule corpus as a measured gate | No new finding; inherited red state |
| 101 | [`4ca19271`](101-4ca19271-plan-record-wave-3-s-gate-and-measured-burn-down.md) | Plan: record wave 3's gate and measured burn-down | No new finding; inherited red state |
| 102 | [`6edd8e81`](102-6edd8e81-run-deinit-hooks-scope-exit-drops-and-heap-region-finalizers.md) | Run Deinit hooks: scope-exit drops and 'heap region finalizers | No new finding; inherited red state |
| 103 | [`86ed9da7`](103-86ed9da7-support-explicit-initializers-on-heap-structs-fix-heap-retain-glue.md) | Support explicit initializers on 'heap structs; fix heap retain glue | No new finding; inherited red state |
| 104 | [`34fe5105`](104-34fe5105-balance-region-claims-and-heap-teardown-donate-on-returns.md) | Balance region claims and heap teardown; donate on returns | No new finding; inherited red state |
| 105 | [`7f6f4d0a`](105-7f6f4d0a-donate-at-global-init-sinks-restore-honest-pins-for-move-rejects.md) | Donate at global-init sinks; restore honest pins for move rejects | No new finding; inherited red state |
| 106 | [`ccd405fc`](106-ccd405fc-merge-break-path-ownership-states-at-loop-exits.md) | Merge break-path ownership states at loop exits | No new finding; inherited red state |
| 107 | [`1775a442`](107-1775a442-deconstruction-transfers-ownership-to-the-extracted-elements.md) | Deconstruction transfers ownership to the extracted elements | No new finding; inherited red state |
| 108 | [`83f4f630`](108-83f4f630-flow-burn-down-the-reassignment-and-field-restore-accepts-pass.md) | Flow burn-down: the reassignment and field-restore accepts pass | No new finding; inherited red state |
| 109 | [`21393363`](109-21393363-plan-record-the-wave-3-burn-down-progress.md) | Plan: record the wave-3 burn-down progress | No new finding; inherited red state |
| 110 | [`ea797ead`](110-ea797ead-plan-date-the-audit-time-g3-snapshot.md) | Plan: date the audit-time G3 snapshot | No new finding; inherited red state |
| 111 | [`2476d132`](111-2476d132-track-global-moves-honor-the-explicit-copy-marker.md) | Track global moves; honor the explicit copy marker | No new finding; inherited red state |
| 112 | [`575c7f3b`](112-575c7f3b-check-mode-compiles-every-declaration-fix-three-checker-precision-bugs.md) | Check mode compiles every declaration; fix three checker precision bugs | Standalone defect, repaired later |
| 113 | [`8150b4b8`](113-8150b4b8-flow-gate-under-check-mode-123-of-183-enforced.md) | Flow gate under check mode: 123 of 183 enforced | No new finding; inherited red state |
| 114 | [`f274e6a4`](114-f274e6a4-borrow-provenance-view-owners-invalidation-and-escape-checks.md) | Borrow provenance: view owners, invalidation, and escape checks | No new finding; inherited red state |
| 115 | [`4ef76ade`](115-4ef76ade-flow-burn-down-the-provenance-families-pass-47-remain.md) | Flow burn-down: the provenance families pass — 47 remain | No new finding; inherited red state |
| 116 | [`85750ccd`](116-85750ccd-structural-ownership-rules-stored-borrows-markers-copy-cloneability.md) | Structural ownership rules: stored borrows, markers, copy cloneability | Request changes |
| 117 | [`4cec14e4`](117-4cec14e4-nll-last-use-liveness-loans-conflicts-and-view-invalidation.md) | NLL last-use liveness: loans, conflicts, and view invalidation | Standalone defect, repaired later |
| 118 | [`aa3e820f`](118-aa3e820f-flow-gate-the-borrow-conflict-family-lands-146-of-183-enforced.md) | Flow gate: the borrow-conflict family lands; 146 of 183 enforced | No new finding; inherited red state |
| 119 | [`42128034`](119-42128034-plan-provenance-and-liveness-state-146-of-183.md) | Plan: provenance and liveness state — 146 of 183 | No new finding; inherited red state |
| 120 | [`183ef7d3`](120-183ef7d3-loop-carried-moves-consume-through-borrow-heap-placement-mut-rvalues.md) | Loop-carried moves, consume-through-borrow, heap placement, mut rvalues | No new finding; inherited red state |
| 121 | [`449d0a0d`](121-449d0a0d-unique-types-t-owned-values-satisfy-unique-parameters.md) | Unique types (*T): owned values satisfy unique parameters | No new finding; inherited red state |
| 122 | [`bbacd632`](122-bbacd632-linear-path-sensitivity-consuming-methods-and-abort-cleanup.md) | Linear path-sensitivity: consuming methods and abort cleanup | No new finding; inherited red state |
| 123 | [`6cb99c99`](123-6cb99c99-close-wave-3-enforce-the-final-flow-corpus-batch.md) | Close wave 3: enforce the final flow-corpus batch | No new finding; inherited red state |
| 124 | [`149a13d7`](124-149a13d7-wave-8-final-sweep-remove-probes-and-dead-root-library-compile.md) | Wave 8: final sweep — remove probes and dead root-library compile | No new finding; inherited red state |
| 125 | [`e1b38381`](125-e1b38381-anchor-talk-test-path-at-the-path-s-enclosing-package-root.md) | Anchor `talk test <path>` at the path's enclosing package root | No new finding; inherited red state |
| 126 | [`c2677e35`](126-c2677e35-cut-talk-test-wall-time-4x-8-3s-2-1s-on-talk-syntax.md) | Cut `talk test` wall time 4x (8.3s -> 2.1s on talk-syntax) | No new finding; inherited red state |
| 127 | [`155fbf8d`](127-155fbf8d-inline-small-functions-and-reuse-registers-talk-test-2-1s-1-3s.md) | Inline small functions and reuse registers: talk test 2.1s -> 1.3s | No new finding; inherited red state |
| 128 | [`d31a88a9`](128-d31a88a9-design-wave-9-drop-emission-rework.md) | Design wave 9: drop emission rework | No new finding; inherited red state |
| 129 | [`e09a28b7`](129-e09a28b7-9a-index-deinit-lookups-memoize-structural-drop-queries.md) | 9a: index Deinit lookups, memoize structural drop queries | No new finding; inherited red state |
| 130 | [`8350e3b7`](130-8350e3b7-9b-share-one-drop-function-per-type-across-drop-sites.md) | 9b: share one drop function per type across drop sites | No new finding; inherited red state |
| 131 | [`a01c59d9`](131-a01c59d9-9c-one-unwind-cleanup-chain-per-frame.md) | 9c: one unwind cleanup chain per frame | No new finding; inherited red state |
| 132 | [`aa132b56`](132-aa132b56-close-wave-9-in-the-plan-with-measured-results.md) | Close wave 9 in the plan with measured results | No new finding; inherited red state |
| 133 | [`43c6c050`](133-43c6c050-wave-10-coalesce-copies-bitset-liveness-flat-alias-table-block-constants.md) | Wave 10: coalesce copies, bitset liveness, flat alias table, block constants | No new finding; inherited red state |
| 134 | [`46ac3079`](134-46ac3079-record-wave-10-closure-and-design-wave-11-ssa-form-mir.md) | Record wave 10 closure and design wave 11: SSA-form MIR | No new finding; inherited red state |
| 135 | [`1d20c13b`](135-1d20c13b-11a-bind-names-to-their-rvalue-temporaries-without-a-copy.md) | 11a: bind names to their rvalue temporaries without a copy | No new finding; inherited red state |
| 136 | [`352ec127`](136-352ec127-record-the-constants-experiment-falsified-and-reverted.md) | Record the constants experiment: falsified and reverted | No new finding; inherited red state |
| 137 | [`af7f9817`](137-af7f9817-register-or-constant-operands-constants-stop-costing-an-instruction.md) | Register-or-constant operands: constants stop costing an instruction | No new finding; inherited red state |
| 138 | [`a3efe2c2`](138-a3efe2c2-11b-block-parameters-on-goto-edges-coalesced-at-allocation.md) | 11b: block parameters on Goto edges, coalesced at allocation | No new finding; inherited red state |
| 139 | [`88489ff7`](139-88489ff7-close-11b-11c-in-the-plan.md) | Close 11b/11c in the plan | No new finding; inherited red state |
| 140 | [`48d5f512`](140-48d5f512-compress-solved-chains-in-varstore-s-shallow-resolution.md) | Compress solved chains in VarStore's shallow resolution | No new finding; inherited red state |
| 141 | [`d2531192`](141-d2531192-record-checker-findings-in-the-plan.md) | Record checker findings in the plan | No new finding; inherited red state |
| 142 | [`1566a24a`](142-1566a24a-build-memberwise-constructions-directly.md) | Build memberwise constructions directly | No new finding; inherited red state |
| 143 | [`be16cf9f`](143-be16cf9f-add-the-benchmark-corpus-eight-archetypes-with-pinned-outputs.md) | Add the benchmark corpus: eight archetypes with pinned outputs | No new finding; inherited red state |
| 144 | [`7bc48b90`](144-7bc48b90-fix-the-bench-corpus-findings-fusion-affinity-rpo-layout-tag-cache-jump-.md) | Fix the bench-corpus findings: fusion, affinity, RPO layout, tag cache, jump threading | No new finding; inherited red state |
| 145 | [`6b0d32ee`](145-6b0d32ee-record-the-profiling-findings.md) | Record the profiling findings | No new finding; inherited red state |

