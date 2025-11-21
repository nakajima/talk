import init, { debug_html, run_program, version as wasmVersion } from "../pkg/talk_wasm.js";

/**
 * Loads the WebAssembly bundle and returns helpers that mirror the talk CLI.
 */
export async function loadTalk() {
  await init();

  return {
    /** Runs a talk program and returns the interpreter result as a string. */
    runProgram: (source) => run_program(source),
    /** Formats the parsed program with debug HTML decorations. */
    debugHtml: (source) => debug_html(source),
    /**
     * Returns the version of the compiled WebAssembly package. This mirrors the
     * Rust crate version embedded in the generated bindings.
     */
    version: () => wasmVersion(),
  };
}
