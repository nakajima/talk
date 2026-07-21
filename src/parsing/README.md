# How parsing works

This directory takes source text to a surface AST: a hand-written lexer
(`lexing/`), a recursive-descent parser (`parser.rs`), the AST node types
(`node_kinds/` plus `node.rs`/`ast.rs`), and the supporting machinery later
stages lean on — node identity, spans, and metadata. The formatter and
syntax highlighter live here too because they are the other consumers of
raw syntax and comments.

## The lexer (`lexing/`)

The lexer is hand-written, character-by-character with lookahead. Tokens
carry their kind, byte offsets, and line/column. Points worth knowing:

- **Newlines are tokens.** Talk has no semicolons; statement boundaries
  come from newlines, so the lexer emits them (collapsing runs into one)
  and the parser decides where they matter. It skips them where nothing
  can end (before an expression starts, between match arms, after commas)
  and treats them as boundaries elsewhere. There is no indentation
  sensitivity.
- String literals handle the usual escapes plus `\u{...}` and line
  continuations; `lexing/mod.rs` owns unescaping and rejects malformed
  escapes.
- Effect names are their own token shape (`'io`). Line comments are
  skipped by default or preserved when the caller asks (`Lexer::preserving_comments`),
  which is what formatting, highlighting, and editor analysis need.

## The parser (`parser.rs`, `precedence.rs`)

Declarations and statements are recursive descent. Expressions use a
Pratt-style precedence table (`precedence.rs` maps each token kind to an
optional prefix rule, optional infix rule, and binding strength). Parsing
an expression means running the current token's prefix rule, then letting
stronger-binding infix rules consume the expression built so far.

The parser returns an AST plus parser diagnostics when it can recover, and
returns a `ParserError` when it cannot. Recovery is intentionally narrow:
missing closers and a few editor-oriented incomplete constructs can produce
diagnostics and placeholder syntax (`IncompleteExpr` for cases such as a
trailing dot), while unrecoverable structure errors still stop parsing.
Tooling remains useful on broken files because the *driver* can run in
lenient mode: a file that fails to parse contributes an empty AST plus a
diagnostic instead of aborting the pipeline (see `src/compiling`).

One bit of context-sensitivity is trailing blocks. `transform(10) { n in
n * 2 }` is a call with a function literal attached, but `if cond {` must
not parse `cond {` as a call-with-block. The parser threads a small
context (top-level, inside an `if` condition, inside a `match` scrutinee,
inside a loop/for condition, ...) that says whether a `{` after an
expression may belong to a call.

## Node identity, spans, and metadata

Every parsed node gets a `NodeID` — a file id plus a counter within that
file. Later generated nodes use the same file id with fresh counters or
reserved synthesized ids, so generated nodes cannot collide with source
nodes. The type checker, flow checker, lowerer, diagnostics, hover,
semantic tokens, go-to-definition, and rename all use these ids as their
join key.

Spans (`span.rs`) are byte ranges plus the file id; `span_index.rs` builds
a by-line index for position-to-node lookups. `node_meta.rs` /
`node_meta_storage.rs` keep source trivia that is not part of the tree
proper — boundary tokens and identifier lists — so the formatter and hover
can recover exact source text.

`node.rs` is the umbrella enum over all node categories (expression,
statement, declaration, pattern, type annotation, ...), each defined in
`node_kinds/` with a struct plus a kind enum (`Expr` + `ExprKind`, etc.).
They derive visitors so passes can walk the tree without hand-written
traversals.

The AST is a surface tree. It includes first-cut macro declarations and
`#name(...)` expression placeholders; `src/macro_expansion.rs` removes or
expands them before desugaring. The desugaring pass in `src/desugar` then
mutates the tree before name resolution while preserving node identity where a
source node still represents the same source construct and minting fresh ids
for synthesized nodes. After type checking, the compile pipeline builds a
`TypedProgram`; editor analysis keeps a clone of the source-faithful AST
because the typed compiler tree deliberately strips syntax-only detail.

`name.rs` is worth a note: an identifier starts as `Name::Raw("foo")` and
becomes `Name::Resolved(symbol, "foo")` during name resolution. After
resolution the AST carries symbols inline, and any later stage can ask a
name for its symbol without consulting a side table.

## The formatter and highlighter

`formatter.rs` is a document-algebra pretty-printer (build a tree of
text / line-break / indent / group nodes, then render at a width) —
`talk format` uses it and it preserves line comments by lexing with
comments enabled. `highlighter.rs` classifies syntax into semantic token
kinds; both terminal/HTML highlighting and the LSP's semantic tokens come
from it.

## Further reading

The expression parser is Pratt's *Top Down Operator Precedence* (1973) in
its table-driven form. The formatter follows the Wadler/Prettier line of
document-algebra printers (Wadler, *A Prettier Printer*, 2003).
