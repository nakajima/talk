const cacheKey = new URL(import.meta.url).search;
const {
  default: init,
  check,
  format,
  highlight,
  hover,
  run_program,
  show_ir,
  version,
} = await import(`/pkg/talk_wasm.js${cacheKey}`);

await init({ module_or_path: `/pkg/talk_wasm_bg.wasm${cacheKey}` });
run_program("0");
self.postMessage({ type: "ready" });

self.addEventListener("message", (event) => {
  const message = event.data;
  if (message.type !== "request") return;

  const { id, operation, payload } = message;
  try {
    self.postMessage({
      type: "result",
      id,
      value: perform(operation, payload),
    });
  } catch (error) {
    self.postMessage({
      type: "result",
      id,
      error: {
        message: error instanceof Error ? error.message : String(error),
        stack: error instanceof Error ? error.stack : undefined,
      },
    });
  }
});

function perform(operation, payload) {
  switch (operation) {
    case "runProgram":
      return run_program(payload.source);
    case "format":
      return format(payload.source);
    case "showIr":
      return show_ir(payload.source);
    case "analyze":
      return {
        checkResult: check(payload.source),
        highlightedSource: highlight(payload.currentSource),
      };
    case "hover":
      return hover(payload.source, payload.byteOffset);
    case "version":
      return version();
    default:
      throw new Error(`Unknown WASM operation: ${operation}`);
  }
}
