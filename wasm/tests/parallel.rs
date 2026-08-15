//! The threads-WASM validation harness (ADR 0058/0059): the parallel
//! corpus programs run in Chrome on real Web-Worker-backed threads over
//! shared wasm memory, against the same pins the native backends hold.
//!
//! Topology matters here. Every `wasm_thread` worker must be a child of
//! the main thread — a worker's own spawn request is relayed to its
//! parent by message, and only the main thread holds the relay handler.
//! A browser also only starts a worker once its spawning thread returns
//! to the event loop. So each test is async ON the main thread: it
//! spawns the whole program into one worker and awaits it, which keeps
//! the main event loop free to start that worker and to relay every
//! task-spawn the program makes while it blocks in joins and parks.
#![cfg(target_arch = "wasm32")]

use talk::repl::{ReplEvalResult, ReplSession};
use wasm_bindgen_test::wasm_bindgen_test;

wasm_bindgen_test::wasm_bindgen_test_configure!(run_in_browser);

async fn run_pinned(source: &'static str, pinned: &'static str) {
    let outcome = wasm_thread::spawn(move || {
        let session = ReplSession::with_source_path(std::path::PathBuf::from("corpus.tlk"));
        match session.eval_program(source) {
            ReplEvalResult::Output { stdout, stderr, .. } => (stdout, stderr),
            other => panic!("program failed: {other:?}"),
        }
    })
    .join_async()
    .await;
    let (stdout, stderr) = outcome.expect("program thread panicked");
    assert_eq!(stdout, pinned, "diverged from the frozen pin");
    assert!(stderr.is_empty(), "stderr not empty: {stderr}");
}

#[wasm_bindgen_test]
async fn parallel_workers_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/parallel_workers.tlk"),
        include_str!("../../tests/parity/programs/parallel_workers.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn coop_scheduler_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/coop_interleave.tlk"),
        include_str!("../../tests/parity/programs/coop_interleave.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn parallel_strings_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/parallel_strings.tlk"),
        include_str!("../../tests/parity/programs/parallel_strings.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn parallel_nested_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/parallel_nested.tlk"),
        include_str!("../../tests/parity/programs/parallel_nested.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn parallel_channels_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/parallel_channels.tlk"),
        include_str!("../../tests/parity/programs/parallel_channels.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn select_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/select_channels.tlk"),
        include_str!("../../tests/parity/programs/select_channels.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn bounded_channel_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/bounded_channel.tlk"),
        include_str!("../../tests/parity/programs/bounded_channel.stdout"),
    )
    .await;
}

#[wasm_bindgen_test]
async fn timers_corpus_matches_pin() {
    run_pinned(
        include_str!("../../tests/programs/timers.tlk"),
        include_str!("../../tests/parity/programs/timers.stdout"),
    )
    .await;
}
