//! The frontend's pipeline-driving test suite (ADR 0057 slice 3b).
//! These tests parse real source through the toolchain, so they live as
//! integration tests linking both `talk-front` and `talk` — the
//! dev-dependency cycle Cargo sanctions. Unit tests that need no parser
//! (the solver harness, the adaptation judgment, hygiene) stay inside
//! the library.

pub mod dump;
pub mod formatter_tests;
pub mod lower_funcs_to_lets_tests;
pub mod lower_if_to_match_tests;
pub mod lower_operators_tests;
pub mod lower_subscripts_tests;
pub mod lower_trailing_blocks_tests;
pub mod lower_unreachable_tests;
pub mod macro_expansion_tests;
pub mod name_resolver_tests;
pub mod parser_tests;
pub mod prepend_self_to_methods_tests;
pub mod resolve_param_modes_tests;
pub mod typed_ast_tests;
pub mod types_tests;

/// `assert_eq_diff!`-shaped adapter over [`assert_fixture_eq`].
#[macro_export]
macro_rules! fixture_eq_args {
    ($left:expr, $right:expr $(,)?) => {
        $crate::assert_fixture_eq(&$left, &$right)
    };
    ($left:expr, $right:expr, $($message:tt)+) => {
        $crate::assert_fixture_eq(&$left, &$right)
    };
}

/// Fixture comparison with sentinel wildcards: the `any_*!` fixtures
/// carry `NodeID(ANY)` ids and `u32::MAX` spans, which unit tests match
/// through `cfg(test)` wildcard equality. Integration tests build the
/// library without that cfg, so this compares Debug renderings instead,
/// treating the sentinel tokens as wildcards.
#[track_caller]
pub fn assert_fixture_eq<T: std::fmt::Debug>(actual: &T, expected: &T) {
    let actual = format!("{actual:#?}");
    let expected = format!("{expected:#?}");
    let sentinels = ["NodeID(ANY)", "4294967295..4294967295", "4294967295"];
    let a_lines: Vec<&str> = actual.lines().collect();
    let e_lines: Vec<&str> = expected.lines().collect();
    let mut ok = a_lines.len() == e_lines.len();
    if ok {
        'lines: for (a, e) in a_lines.iter().zip(&e_lines) {
            // Split the expected line at sentinel tokens; the literal
            // segments must appear in order and cover the whole line.
            let mut segments: Vec<&str> = vec![e];
            for sentinel in sentinels {
                segments = segments
                    .into_iter()
                    .flat_map(|s| s.split(sentinel))
                    .collect();
            }
            if segments.len() == 1 {
                if a != e {
                    ok = false;
                    break 'lines;
                }
                continue;
            }
            let mut rest: &str = a;
            for (i, segment) in segments.iter().enumerate() {
                if i == 0 {
                    let Some(r) = rest.strip_prefix(segment) else {
                        ok = false;
                        break 'lines;
                    };
                    rest = r;
                } else if let Some(pos) = rest.find(segment) {
                    rest = &rest[pos + segment.len()..];
                } else {
                    ok = false;
                    break 'lines;
                }
            }
            if !segments.last().is_none_or(|s| s.is_empty()) && !rest.is_empty() {
                // A trailing literal segment must end the line.
                if !a.ends_with(segments.last().copied().unwrap_or_default()) {
                    ok = false;
                    break 'lines;
                }
            }
        }
    }
    assert!(
        ok,
        "fixture mismatch\n--- actual ---\n{actual}\n--- expected (sentinels wildcard) ---\n{expected}"
    );
}
