# How parsing works

This directory takes source text to an AST: a hand-written lexer
(`lexing/`), a recursive-descent parser (`parser.rs`), the node types
themselves (`node_kinds/`), and the supporting machinery every later
stage leans on — node identity, spans, and metadata. The formatter and
syntax highlighter live here too, since they're the other two
consumers of raw syntax.

## The lexer (`lexing/`)

Hand-written, character-by-character with lookahead. Tokens carry
their kind, byte offsets, and line/column. Points worth knowing:

- **Newlines are tokens.** Talk has no semicolons; statement
  boundaries come from newlines, so the lexer emits them (collapsing
  runs into one) and the parser decides where they matter — it skips
  them at points where nothing can end (before an expression starts,
  between match arms, after commas) and treats them as boundaries
  everywhere else. There is no indentation sensitivity.
- String literals handle the usual escapes plus `\u{…}` and
  line continuations; `lexing/mod.rs` owns unescaping.
- Effect names are their own token shape (`'io`), and comments are
  either skipped or preserved depending on who's asking (the
  formatter and hover want them; the compiler doesn't).

## The parser (`parser.rs`, `precedence.rs`)

Recursive descent for declarations and statements; expressions use a
precedence table (`precedence.rs` maps each token kind to an optional
prefix rule, an optional infix rule, and a binding strength — the
classic Pratt arrangement). Parsing an expression is: run the prefix
rule for the current token, then repeatedly let stronger-binding
infix rules consume what's been built so far.

Errors are immediate: the parser reports the first problem
(`parser_error.rs`) and stops — there are no error-recovery
placeholder nodes in the AST. Tooling still works on broken files
because the *driver* can run in a lenient mode where a file that
failed to parse contributes an empty AST and a diagnostic instead of
aborting the pipeline (see `src/compiling`).

One bit of context-sensitivity: trailing blocks. `transform(10) { n in
n * 2 }` is a call with a function literal attached, but `if cond {`
must not parse `cond {` as a call-with-block — so the parser threads a
small context (top-level / inside an `if` condition / inside a `match`
scrutinee, …) that says whether a `{` after an expression can belong
to it.

## Node identity, spans, and metadata

Every node gets a `NodeID` — a pair of file id and a counter within
that file — assigned at parse time and **stable for the node's whole
life**. The entire compiler is keyed on these: the checker's per-node
types, instantiation tables, member resolutions, diagnostics, hover —
all of them are maps from `NodeID`. Synthesized and specialized code
gets reserved file ids so generated nodes can't collide with real
ones.

Spans (`span.rs`) are byte ranges plus the file id; `span_index.rs`
builds a by-line index so position→node lookups (hover, go to
definition) don't scan the tree. `node_meta.rs` /
`node_meta_storage.rs` keep per-node extras that aren't part of the
tree proper — boundary tokens and identifier lists — which is how the
formatter and hover recover exact source text for a node.

`node.rs` is the umbrella enum over all node categories (expression,
statement, declaration, pattern, …), each defined in `node_kinds/`
with a struct + kind-enum pair (`Expr` + `ExprKind`, …). All of them
derive a visitor so passes can walk the tree without hand-written
traversals. Nodes are built once and never mutated in place; the
phases that need to change the tree (the desugaring transforms in
`src/name_resolution/transforms/`) rebuild the affected nodes.

`name.rs` is worth a note: an identifier starts life as
`Name::Raw("foo")` and becomes `Name::Resolved(symbol, "foo")` during
name resolution — so the AST after resolution carries its symbols
inline, and any stage can ask a name for its symbol without a side
table.

## The formatter and highlighter

`formatter.rs` is a document-algebra pretty-printer (build a tree of
text / line-break / indent / group nodes, then render at a width) —
`talk format` uses it. `highlighter.rs` classifies nodes into semantic
token kinds; both the terminal HTML output and the LSP's semantic
tokens come from it.

## Further reading

The expression parser is Pratt's *Top Down Operator Precedence*
(1973) in its table-driven form. The formatter follows the
Wadler/Prettier line of document-algebra printers (Wadler, *A
Prettier Printer*, 2003).
