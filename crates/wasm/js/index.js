import init, {
  Repl,
  debug_html,
  hover as wasmHover,
  poll_program_threaded,
  start_program_threaded,
  version as wasmVersion,
} from "../pkg/talk_wasm.js";

/**
 * Loads the WebAssembly bundle and returns helpers that mirror the talk CLI.
 */
export async function loadTalk() {
  if (!globalThis.crossOriginIsolated || !globalThis.SharedArrayBuffer) {
    throw new Error(
      "Talk WASM requires cross-origin isolation and SharedArrayBuffer",
    );
  }
  await init();

  return {
    /** Creates a persistent REPL session. */
    newRepl: () => new Repl(),
    /** Runs a talk program and returns the interpreter result as a string. */
    runProgram: async (source, stdin = new Uint8Array()) => {
      if (typeof stdin === "string") stdin = new TextEncoder().encode(stdin);
      if (!(stdin instanceof Uint8Array)) {
        throw new TypeError("stdin must be a string or Uint8Array");
      }
      const handle = start_program_threaded(source, stdin);
      for (;;) {
        const state = poll_program_threaded(handle);
        if (state.done) return state.result;
        await new Promise((resolve) => setTimeout(resolve, 4));
      }
    },
    /** Formats the parsed program with debug HTML decorations. */
    debugHtml: (source) => debug_html(source),
    /**
     * Returns hover info for a source location.
     * Options: { byteOffset, line, column, nodeId }
     */
    hover: (source, options = {}) => {
      const { byteOffset, line, column, nodeId } = options;
      return wasmHover(
        source,
        byteOffset ?? undefined,
        line ?? undefined,
        column ?? undefined,
        nodeId ?? undefined
      );
    },
    /**
     * Returns the version of the compiled WebAssembly package. This mirrors the
     * Rust crate version embedded in the generated bindings.
     */
    version: () => wasmVersion(),
  };
}
