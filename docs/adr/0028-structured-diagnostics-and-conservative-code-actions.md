# 0028 - Structured diagnostics and conservative code actions

Status: implemented for parser, name-resolution, and type diagnostics; ownership portions superseded by ADR 0031 (2026-07-13)

## Context

The compiler represents parser, name-resolution, type, and ownership failures as
structured diagnostic enums. Editor analysis currently flattens those values to
a range, severity, and rendered message. The LSP then reconstructs diagnostic
identity by matching message prefixes such as `Missing '` and `Ambiguous
member`.

That loses information at the seam where editor behavior needs it most:

- code actions cannot exhaustively match diagnostic variants;
- payloads such as an undeclared effect, missing witness, or variant candidates
  must be parsed back out of prose;
- the originating `NodeID` is unavailable, so actions rediscover syntax from a
  range start;
- most parser variants have no precise range and fall back to byte range
  `0..0`;
- warning diagnostics cannot be attached faithfully because quick fixes
  reconstruct every diagnostic with error severity; and
- message wording has accidentally become an interface used by tooling.

The current LSP has code actions for undefined-name imports and three type
errors: ambiguous members, missing protocol witnesses, and non-exhaustive
matches. It has no parser code actions. An audit found 15 parser error variants
and 42 type error variants. Some are good candidates for deterministic source
edits, while others require the editor to invent a type, value, ownership
choice, or larger redesign.

Code actions should be conservative. A quick fix may choose among alternatives
that are already proven valid by compiler information. Destructive fixes must
say what they remove, and placeholder-producing fixes must use visible,
syntactically valid source rather than pretending to infer a runtime value.
Message wording alone is never evidence for an edit.

## Decision

### 1. Preserve diagnostic identity through analysis

The editor-facing diagnostic retains:

- its structured compiler diagnostic kind and payload;
- its originating `NodeID` when one exists;
- its byte range;
- its severity; and
- its rendered message.

The LSP publishes a stable string code derived from the structured kind. The
rendered message remains user-facing prose and is not an interface for code
actions.

Manifest and other analysis-only diagnostics that do not originate in the
compiler diagnostic enums may remain unstructured, but they do not participate
in compiler quick fixes.

### 2. Match code actions structurally

`src/lsp/code_actions.rs` owns action selection and source edits behind one
`compute_code_actions` interface. The server only routes the request and
translates document state into that call, keeping diagnostic policy local to
one module.

Code-action dispatch matches the diagnostic enum variant. Existing actions for
undefined names, ambiguous members, missing witnesses, and non-exhaustive
matches use their payloads directly instead of parsing rendered messages.

An action is attached with the original range, severity, source, message, and
stable code. Requested ranges use full position overlap, not line-only overlap.

### 3. Make fixable parser expectations structured

`UnexpectedToken` distinguishes a concrete expected `TokenKind` from a prose
description. Parser recovery can therefore offer insertion only for concrete
syntax.

Parser variants that identify source syntax carry its span. In particular,
`ExplicitSelfParameterNotAllowed` carries the explicit parameter span so the
LSP can remove it even when lenient parsing substitutes an empty AST after the
fatal parse error.

A missing-token action is offered only when the parser produced a recovered AST
or when the diagnostic is the required `else` of an `if` expression. This
avoids treating a fatal `expected ')'` after another argument as proof that a
closing parenthesis, rather than a comma, was intended.

### 4. Eligibility rule

A compiler diagnostic receives a code action when all of the following hold:

1. the compiler payload or semantic catalog determines the replacement;
2. the edit is local or has symbol-precise references;
3. applying the edit produces syntactically valid Talk source;
4. the action does not pretend to infer a type-correct runtime value; inserted
   placeholders are explicit and expected to be replaced; and
5. an action that removes a potentially evaluated expression explicitly says
   so in its title and removes only syntax proven excess by the diagnostic.

Multiple compiler-proven alternatives may be offered. An alternative is
preferred only when it is unique.

### 5. Parser actions

The accepted parser actions are:

- insert a missing `)`, `]`, or `}` reported by parser recovery;
- insert the required `else {}` branch of an `if` expression; and
- remove an explicit `self` parameter from an instance method.

Closing unterminated literals is deferred until lexer errors distinguish the
literal kind and carry an exact byte span. Extracting a forbidden conformance
list into an `extend` declaration is deferred because generic heads and where
clauses make it a declaration transformation rather than a local repair.

### 6. Type actions

Existing actions remain for:

- `AmbiguousMember`;
- `MissingWitness`; and
- `NonExhaustiveMatch`.

The accepted additional actions are:

- `ArityMismatch` at a value-call site: insert `{}` for missing arguments,
  including constructor or variant labels when known, or remove trailing
  arguments beyond the expected arity; other arity diagnostics receive no
  action;
- `UndeclaredEffect`: add the effect to the enclosing closed effect annotation;
- `UnknownMember`: replace the label with members proven valid for the receiver;
- `UnresolvedVariant`: qualify the leading-dot variant with each enum that
  declares it;
- `DuplicatePredicate`: remove the duplicate where predicate;
- `RedundantVariantResultType`: remove the redundant explicit result;
- `DuplicateAssociatedTypeBinding`: remove the duplicate binding;
- `UnknownAssociatedTypeBinding`: replace the name with declared associated
  type names;
- `GenericShadowing`: rename the inner generic and its symbol references to a
  fresh name;
- `InvalidVariantPayloadLabels`: rewrite labels to the declaration's labels
  when payload arity already matches;
- `IncompatibleOrPatternRefinements`: split the or-pattern into separate match
  arms with the same body;
- `InvalidVariantResultType`: repair the enclosing enum head only when the
  existing type-argument arity is already valid;
- `UnreachableMatchArm`: remove the unreachable arm; and
- `UnreachableCode`: remove the unreachable tail of its enclosing block.

Unknown-member replacements reuse the same receiver-aware member catalog as
completion. Unresolved variants are preferred only when one enum declares the
label. Removal actions expand over adjacent separators so they do not leave
invalid commas or `&&` tokens.

### 7. Deferred and rejected actions

The following remain possible non-preferred actions, but are not part of this
decision's implementation: removing invalid where predicates, removing `any`
from a non-protocol existential, choosing which overlapping or impossible
conformance to remove, and globally guessing a member for an unresolved
receiver type.

No generic action is added for mismatches, non-call arity mismatches, infinite
types, non-functions, invalid assignment targets, failed conformances,
ambiguous type parameters, escaping existentials, duplicate variant payload
labels, ambiguous GADT results, missing associated type bindings, object-safety failures,
existential upcasts, unhandled effects, recursive conformances, solver
overflow, or unsupported features. Those diagnostics do not determine a valid
local edit under the eligibility rule.

Unused parser/type error variants are not treated as action candidates. They
should be removed separately when doing so does not obscure an unfinished
compiler path.

## Consequences

- Diagnostic wording can improve without silently breaking editor behavior.
- The analysis diagnostic interface becomes slightly larger, but gains
  leverage: publishing, code actions, tests, and future editor features share
  one diagnostic identity instead of reconstructing it independently.
- Parser fixes require better source payloads from the parser rather than LSP
  text heuristics.
- Some useful-looking fixes remain intentionally unavailable because
  correctness is preferred over making every diagnostic actionable.
- Warning fixes are associated with warning diagnostics correctly.
- A missing-argument action fixes call shape but may leave type mismatches at
  its `{}` placeholders until the author supplies values.
- Removing excess arguments can remove their effects; the action title makes
  that destructive edit explicit.

## Validation

The implementation is complete when tests cover:

1. stable LSP diagnostic codes and preserved warning severity;
2. existing actions without message parsing;
3. insertion of each accepted missing delimiter and a required `else`;
4. removal of an explicit `self` parameter;
5. every accepted type action, including missing and excess call arguments and
   unique and ambiguous candidate cases;
6. UTF-16 ranges for edits after non-ASCII source text;
7. separator removal for first, middle, last, and only list elements where
   applicable; and
8. no action for representative mismatch, non-call arity,
   missing-associated-type, and fatal ambiguous-parser diagnostics.
