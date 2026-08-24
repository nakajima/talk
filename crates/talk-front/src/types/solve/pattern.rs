use super::*;

/// One-way structural match binding rigid params in `pattern` to the
/// corresponding pieces of `actual` (matching a conformance row's head
/// application against a concrete type).
/// One-way structural matching of a declared pattern type (over rigid
/// `Param`s) against a concrete actual: the binding a conformance row or
/// member owner performs at discharge. Shared with the lowerer, which
/// re-derives the same bindings when demanding specializations.
pub(crate) fn bind_param_pattern(pattern: &Ty, actual: &Ty, bindings: &mut FxHashMap<Symbol, Ty>) {
    // The boolean (head mismatch) is irrelevant here: callers consume only the
    // bindings, and a conformance head is already known to match its receiver.
    match_pattern(pattern, actual, bindings);
}
