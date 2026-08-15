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
      error: describeError(error),
    });
  }
});

function describeError(error) {
  if (error instanceof Error) {
    return { message: error.message, stack: error.stack };
  }
  if (typeof error === "string") {
    return { message: error };
  }
  if (error && typeof error === "object") {
    const messages = [];
    if (typeof error.message === "string" && error.message.trim()) {
      messages.push(error.message.trim());
    }
    if (Array.isArray(error.diagnostics)) {
      for (const diagnostic of error.diagnostics) {
        if (typeof diagnostic?.message !== "string") continue;
        const message = diagnostic.message.trim();
        if (message && !messages.includes(message)) messages.push(message);
      }
    }
    if (messages.length) return { message: messages.join("\n") };

    try {
      const serialized = JSON.stringify(error);
      if (serialized && serialized !== "{}") return { message: serialized };
    } catch {}
  }
  return { message: "Unknown WASM error" };
}

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
