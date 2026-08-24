#![cfg(target_arch = "wasm32")]

use talk::repl::{ReplEvalResult, ReplSession};
use wasm_bindgen_test::wasm_bindgen_test;

wasm_bindgen_test::wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
async fn repl_sleep_and_instant_use_browser_time() {
    let result = wasm_thread::spawn(|| {
        let session = ReplSession::with_source_path(std::path::PathBuf::from("time.tlk"));
        session.eval_program(
            "use task::{ sleep }\n\
             let start = Instant.now()\n\
             sleep(.milliseconds(5))\n\
             Instant.now().since(start).as_milliseconds() >= 5",
        )
    })
    .join_async()
    .await
    .expect("time test worker panicked");
    assert_eq!(
        result,
        ReplEvalResult::Output {
            stdout: String::new(),
            stderr: String::new(),
            value: Some("true".to_string()),
        }
    );
}

#[wasm_bindgen_test]
async fn streaming_repl_reads_preloaded_stdin() {
    let result = wasm_thread::spawn(|| {
        let session = ReplSession::with_source_path(std::path::PathBuf::from("stdin.tlk"));
        session.eval_program_streaming(
            "#unsafe {\n\
             let buf = _alloc<Byte>(count: 4)\n\
             print(_io_read(fd: STDIN_FD, buf: buf, count: 4))\n\
             _free(ptr: buf)\n\
           }",
            b"test".to_vec(),
            |_, _| {},
        )
    })
    .join_async()
    .await
    .expect("stdin test worker panicked");
    assert!(matches!(
        result,
        ReplEvalResult::Output { stdout, .. } if stdout == "4\n"
    ));
}
