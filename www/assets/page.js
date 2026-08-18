function initIntroExamples() {
  const introText = document.querySelector(".intro-text, .intro-txt");
  const introCode = document.querySelector(".intro-code pre");
  if (!introText || !introCode) return;

  let currentExample = introText.querySelector("span[data-example]");
  currentExample?.setAttribute("data-displayed", "true");

  introText.addEventListener("pointerover", (event) => {
    if (!(event.target instanceof Element)) return;
    const example = event.target.closest("span[data-example]");
    if (!example || !introText.contains(example)) return;

    const template = document.querySelector(
      `template[data-example="${example.dataset.example}"]`,
    );
    if (!(template instanceof HTMLTemplateElement)) return;

    currentExample?.removeAttribute("data-displayed");
    example.setAttribute("data-displayed", "true");
    currentExample = example;
    introCode.replaceChildren(template.content.cloneNode(true));
  });
}

initIntroExamples();

const wasmCacheKey = new URL(import.meta.url).search;
const threadedTalkReady = loadThreadedTalk();
const talk = createWasmClient();
talk.onFailure(disableFailedActionButtons);
talk.ready.then(enableActionButtons).catch(() => {});

async function loadThreadedTalk() {
  if (!globalThis.crossOriginIsolated || !globalThis.SharedArrayBuffer) {
    throw new Error(
      "The Talk playground requires cross-origin isolation and SharedArrayBuffer",
    );
  }
  const wasm = await import(`/pkg/talk_wasm.js${wasmCacheKey}`);
  await wasm.default({
    module_or_path: `/pkg/talk_wasm_bg.wasm${wasmCacheKey}`,
  });
  return wasm;
}

function runThreadedProgram(source, stdin) {
  let stdoutController;
  let stderrController;
  let stdoutOpen = true;
  let stderrOpen = true;
  const stdout = new ReadableStream({
    start(controller) {
      stdoutController = controller;
    },
    cancel() {
      stdoutOpen = false;
    },
  });
  const stderr = new ReadableStream({
    start(controller) {
      stderrController = controller;
    },
    cancel() {
      stderrOpen = false;
    },
  });
  const failStreams = (error) => {
    if (stdoutOpen) stdoutController.error(error);
    if (stderrOpen) stderrController.error(error);
    stdoutOpen = false;
    stderrOpen = false;
  };
  const result = (async () => {
    const wasm = await threadedTalkReady;
    const handle = wasm.start_program_threaded(source, stdin);
    for (;;) {
      const state = wasm.poll_program_threaded(handle);
      for (const chunk of state.output) {
        if (chunk.fd === 1 && stdoutOpen) stdoutController.enqueue(chunk.bytes);
        if (chunk.fd === 2 && stderrOpen) stderrController.enqueue(chunk.bytes);
      }
      if (state.done) {
        if (stdoutOpen) stdoutController.close();
        if (stderrOpen) stderrController.close();
        stdoutOpen = false;
        stderrOpen = false;
        return state.result;
      }
      await new Promise((resolve) => setTimeout(resolve, 4));
    }
  })();
  result.catch(failStreams);
  return { stdout, stderr, result };
}

function createWasmClient() {
  const worker = new Worker(`/wasm-worker.js${wasmCacheKey}`, {
    type: "module",
  });
  const pending = new Map();
  const failureListeners = new Set();
  let nextId = 0;
  let fatalError = null;
  let resolveReady;
  let rejectReady;
  const workerReady = new Promise((resolve, reject) => {
    resolveReady = resolve;
    rejectReady = reject;
  });
  const ready = Promise.all([workerReady, threadedTalkReady]).then(() => undefined);

  const fail = (error) => {
    if (fatalError) return;
    fatalError = error;
    rejectReady(error);
    for (const { reject } of pending.values()) reject(error);
    pending.clear();
    for (const listener of failureListeners) listener(error);
  };
  ready.catch(fail);

  worker.addEventListener("message", (event) => {
    const message = event.data;
    if (message.type === "ready") {
      resolveReady();
      return;
    }

    const request = pending.get(message.id);
    if (!request) return;
    if (message.type !== "result") return;

    pending.delete(message.id);
    if (message.error) {
      const error = new Error(message.error.message);
      if (message.error.stack) error.stack = message.error.stack;
      request.reject(error);
    } else {
      request.resolve(message.value);
    }
  });
  worker.addEventListener("error", (event) => {
    fail(new Error(event.message || "WASM worker failed"));
  });

  const request = async (operation, payload = {}) => {
    await ready;
    if (fatalError) throw fatalError;

    const id = nextId++;
    return new Promise((resolve, reject) => {
      pending.set(id, { resolve, reject });
      worker.postMessage({ type: "request", id, operation, payload });
    });
  };

  return {
    ready,
    get failed() {
      return fatalError !== null;
    },
    onFailure(listener) {
      failureListeners.add(listener);
      if (fatalError) listener(fatalError);
    },
    runProgram(source, { stdin = new Uint8Array() } = {}) {
      if (typeof stdin === "string") stdin = new TextEncoder().encode(stdin);
      if (!(stdin instanceof Uint8Array)) {
        throw new TypeError("stdin must be a string or Uint8Array");
      }
      return runThreadedProgram(source, stdin);
    },
    format: (source) => request("format", { source }),
    showIr: (source) => request("showIr", { source }),
    analyze: (source, currentSource) =>
      request("analyze", { source, currentSource }),
    hover: (source, byteOffset) =>
      request("hover", { source, byteOffset }),
    version: () => request("version"),
  };
}

function enableActionButtons() {
  for (const button of document.querySelectorAll(".actions button")) {
    const control = button.closest(".action-control");
    button.disabled = false;
    control?.removeAttribute("data-tooltip");
    control?.removeAttribute("aria-label");
    control?.removeAttribute("tabindex");
  }
}

function disableFailedActionButtons(error) {
  console.error(error);
  for (const button of document.querySelectorAll(".actions button")) {
    button.disabled = true;
    const control = button.closest(".action-control");
    control?.setAttribute(
      "data-tooltip",
      "WASM bundle failed to initialize",
    );
    control?.setAttribute(
      "aria-label",
      "WASM bundle failed to initialize",
    );
  }
}

function createHoverTooltips() {
  const tooltipEl = document.createElement("div");
  tooltipEl.className = "code-hover-popover";
  tooltipEl.hidden = true;
  document.body.appendChild(tooltipEl);

  const encoder = new TextEncoder();
  let pending = false;
  let lastPointer = null;
  let currentEditor = null;
  let currentToken = null;
  let hoverTimer = null;

  const cancelHoverTimer = () => {
    if (hoverTimer === null) return;
    clearTimeout(hoverTimer);
    hoverTimer = null;
  };

  const hide = () => {
    cancelHoverTimer();
    lastPointer = null;
    currentEditor = null;
    currentToken = null;
    tooltipEl.hidden = true;
  };

  const showAt = (rect, content) => {
    tooltipEl.textContent = content;
    tooltipEl.style.left = "0px";
    tooltipEl.style.top = "0px";
    tooltipEl.style.transform = "none";
    tooltipEl.hidden = false;

    const pop = tooltipEl.getBoundingClientRect();
    const centerX = Math.min(
      Math.max(rect.left + rect.width / 2, pop.width / 2 + 4),
      window.innerWidth - pop.width / 2 - 4,
    );
    const above = rect.top - 8 - pop.height >= 0;
    tooltipEl.style.left = `${centerX}px`;
    tooltipEl.style.top = above ? `${rect.top - 8}px` : `${rect.bottom + 8}px`;
    tooltipEl.style.transform = above
      ? "translate(-50%, -100%)"
      : "translate(-50%, 0)";
  };

  const utf8Length = (text) => encoder.encode(text).length;

  const charOffsetForToken = (highlightEl, tokenEl) => {
    const walker = document.createTreeWalker(
      highlightEl,
      NodeFilter.SHOW_TEXT,
    );
    let offset = 0;
    let node = walker.nextNode();
    while (node) {
      if (tokenEl.contains(node)) break;
      offset += node.nodeValue.length;
      node = walker.nextNode();
    }
    return offset;
  };

  const showHover = async (editor, highlightEl, tokenEl) => {
    if (!tokenEl.isConnected) return;

    const { source, currentSource } = getHoverSource(editor);
    const tokenText = tokenEl.textContent || "";
    const charOffset =
      charOffsetForToken(highlightEl, tokenEl) +
      Math.floor(tokenText.length / 2);
    const byteOffset =
      utf8Length(source) -
      utf8Length(currentSource) +
      utf8Length(currentSource.slice(0, charOffset));

    let result;
    try {
      result = await talk.hover(source, byteOffset);
    } catch (error) {
      if (!talk.failed) console.error(error);
      return;
    }

    const contents = result?.hover?.contents;
    if (
      !contents ||
      currentEditor !== editor ||
      currentToken !== tokenEl
    ) {
      return;
    }
    showAt(tokenEl.getBoundingClientRect(), contents);
  };

  const scheduleHover = (editor, highlightEl, tokenEl) => {
    cancelHoverTimer();
    hoverTimer = setTimeout(() => {
      hoverTimer = null;
      showHover(editor, highlightEl, tokenEl);
    }, 200);
  };

  const tokenFromPoint = (editor, highlightEl, x, y) => {
    const editable = editor.matches(".code-editable");
    const previousPointerEvents = editor.style.pointerEvents;
    if (editable) editor.style.pointerEvents = "none";
    const elementsFromPoint = document.elementsFromPoint
      ? document.elementsFromPoint(x, y)
      : null;
    const topElement = document.elementFromPoint(x, y);
    if (editable) editor.style.pointerEvents = previousPointerEvents;

    if (Array.isArray(elementsFromPoint)) {
      for (const element of elementsFromPoint) {
        if (!(element instanceof HTMLElement)) continue;
        if (element.tagName !== "SPAN") continue;
        if (element.closest(".code-highlight") !== highlightEl) continue;
        return element;
      }
    }

    if (
      topElement instanceof HTMLElement &&
      topElement.tagName === "SPAN" &&
      topElement.closest(".code-highlight") === highlightEl
    ) {
      return topElement;
    }

    for (const span of highlightEl.querySelectorAll("span")) {
      const rect = span.getBoundingClientRect();
      if (
        x >= rect.left &&
        x <= rect.right &&
        y >= rect.top &&
        y <= rect.bottom
      ) {
        return span;
      }
    }

    return null;
  };

  const update = () => {
    if (!lastPointer) return;
    const { editor, x, y, buttons } = lastPointer;
    if (!editor?.isConnected || buttons !== 0) {
      hide();
      return;
    }

    const highlightEl = editor.matches(".code-highlight")
      ? editor
      : editor.closest(".runnable")?.querySelector(".code-highlight");
    if (!highlightEl) {
      hide();
      return;
    }

    const highlightRect = highlightEl.getBoundingClientRect();
    if (
      x < highlightRect.left ||
      x > highlightRect.right ||
      y < highlightRect.top ||
      y > highlightRect.bottom
    ) {
      hide();
      return;
    }

    const token = tokenFromPoint(editor, highlightEl, x, y);
    if (!token) {
      hide();
      return;
    }
    if (editor === currentEditor && token === currentToken) return;

    currentEditor = editor;
    currentToken = token;
    tooltipEl.hidden = true;
    scheduleHover(editor, highlightEl, token);
  };

  document.addEventListener(
    "pointermove",
    (event) => {
      const editor =
        event.target instanceof Element
          ? event.target.closest(
              ".code-editable, .no-run .code-highlight",
            )
          : null;
      if (!editor) {
        hide();
        return;
      }

      lastPointer = {
        editor,
        x: event.clientX,
        y: event.clientY,
        buttons: event.buttons,
      };
      if (pending) return;
      pending = true;
      requestAnimationFrame(() => {
        pending = false;
        update();
      });
    },
    { passive: true },
  );
  document.addEventListener("pointerdown", hide, { passive: true });
  document.addEventListener("scroll", hide, {
    capture: true,
    passive: true,
  });
  document.documentElement.addEventListener("pointerleave", hide);
  window.addEventListener("blur", hide);

  return { hide };
}

const diagnosticsMeasureCache = new WeakMap();

function getDiagnosticsMeasureNode(highlightEl) {
  let node = diagnosticsMeasureCache.get(highlightEl);
  if (node) return node;

  const style = getComputedStyle(highlightEl);
  node = document.createElement("span");
  node.style.position = "absolute";
  node.style.visibility = "hidden";
  node.style.pointerEvents = "none";
  node.style.whiteSpace = "pre";
  node.style.top = "0";
  node.style.left = "-9999px";
  node.style.font = style.font;
  node.style.fontFamily = style.fontFamily;
  node.style.fontSize = style.fontSize;
  node.style.fontWeight = style.fontWeight;
  node.style.fontStyle = style.fontStyle;
  node.style.letterSpacing = style.letterSpacing;
  node.style.wordSpacing = style.wordSpacing;
  node.style.tabSize = style.tabSize;
  node.style.lineHeight = style.lineHeight;
  document.body.appendChild(node);

  diagnosticsMeasureCache.set(highlightEl, node);
  return node;
}

function measureText(highlightEl, text) {
  const node = getDiagnosticsMeasureNode(highlightEl);
  node.textContent = text;
  return node.getBoundingClientRect().width;
}

function getDiagnosticsLayer(container) {
  const diagnosticsEl = container.querySelector(".code-diagnostics");
  if (!diagnosticsEl) return null;
  let layer = diagnosticsEl.querySelector(".diagnostics-layer");
  if (!layer) {
    layer = document.createElement("div");
    layer.className = "diagnostics-layer";
    layer.style.position = "relative";
    layer.style.width = "0";
    layer.style.height = "0";
    diagnosticsEl.appendChild(layer);
  }
  return { diagnosticsEl, layer };
}

function ensureDiagnosticsList(container) {
  let list = container.querySelector(".diagnostics-list");
  if (list) return list;
  list = document.createElement("div");
  list.className = "diagnostics-list";
  const actions = container.querySelector(".actions");
  if (actions?.parentNode) {
    actions.parentNode.insertBefore(list, actions);
  } else {
    container.appendChild(list);
  }
  return list;
}

function renderDiagnostics(container, highlightEl, diagnosticsLayer, checkResult) {
  if (!diagnosticsLayer) return;
  const { diagnosticsEl, layer } = diagnosticsLayer;
  layer.textContent = "";

  const list = ensureDiagnosticsList(container);
  const entries =
    checkResult && Array.isArray(checkResult.diagnostics)
      ? checkResult.diagnostics
      : [];
  if (entries.length === 0) {
    list.textContent = "";
    list.style.display = "none";
    return;
  }

  list.textContent = "";
  list.style.display = "";

  const style = getComputedStyle(highlightEl);
  const fontSize = parseFloat(style.fontSize) || 0;
  const lineHeightValue = parseFloat(style.lineHeight);
  const lineHeight = Number.isFinite(lineHeightValue)
    ? lineHeightValue
    : fontSize * 1.5;
  const paddingTop = parseFloat(style.paddingTop) || 0;
  const paddingLeft = parseFloat(style.paddingLeft) || 0;
  const paddingRight = parseFloat(style.paddingRight) || 0;

  layer.style.width = `${highlightEl.scrollWidth}px`;
  layer.style.height = `${highlightEl.scrollHeight}px`;

  for (const diagnostic of entries) {
    const item = document.createElement("div");
    item.className = "diagnostic-item";
    if (diagnostic.severity) {
      item.dataset.severity = diagnostic.severity;
    }
    const message = document.createElement("div");
    message.className = "diagnostic-message";
    message.textContent = diagnostic.message || "Diagnostic";
    item.appendChild(message);
    list.appendChild(item);

    const line = Number.isFinite(diagnostic.line) ? diagnostic.line : 1;
    const underlineStart = Number.isFinite(diagnostic.underline_start)
      ? diagnostic.underline_start
      : 1;
    const underlineLen = Number.isFinite(diagnostic.underline_len)
      ? diagnostic.underline_len
      : 1;
    const lineText =
      typeof diagnostic.line_text === "string" ? diagnostic.line_text : "";

    const startIndex = Math.max(0, underlineStart - 1);
    const clampedStart = Math.min(startIndex, lineText.length);
    const clampedLen = Math.max(1, underlineLen);
    const prefix = lineText.slice(0, clampedStart);
    const segment = lineText.slice(clampedStart, clampedStart + clampedLen);

    let left = paddingLeft + measureText(highlightEl, prefix);
    let width = measureText(highlightEl, segment);
    if (!Number.isFinite(width) || width <= 0) {
      width = measureText(highlightEl, " ");
    }
    width = Math.max(4, width);

    const maxWidth = Math.max(
      0,
      highlightEl.scrollWidth - paddingLeft - paddingRight,
    );
    if (left + width > paddingLeft + maxWidth) {
      width = Math.max(2, paddingLeft + maxWidth - left);
    }

    const underline = document.createElement("div");
    underline.className = "diag-underline";
    if (diagnostic.severity) {
      underline.dataset.severity = diagnostic.severity;
    }
    underline.style.left = `${left}px`;
    underline.style.top = `${
      paddingTop + (Math.max(1, line) - 1) * lineHeight + lineHeight - 2
    }px`;
    underline.style.width = `${width}px`;
    layer.appendChild(underline);
  }

  diagnosticsEl.scrollTop = highlightEl.scrollTop;
  diagnosticsEl.scrollLeft = highlightEl.scrollLeft;
}

const hoverTooltips = createHoverTooltips();
const editorRenderers = new WeakMap();

for (const el of document.querySelectorAll(".actions .run")) {
  initRunnable(el);
}

for (const el of document.querySelectorAll(".code-editable")) {
  initEditable(el);
}

for (const el of document.querySelectorAll(".actions .lower")) {
  initLowerable(el);
}

for (const el of document.querySelectorAll(".actions .format")) {
  initFormattable(el);
}

function accumulateGroup(container) {
  return container?.dataset.accumulateGroup ?? "";
}

function sourceForContainer(container) {
  const editor = container?.querySelector(".code-editable");
  return (
    editor?.value ??
    container?.dataset.source ??
    container?.querySelector(".code-highlight")?.textContent ??
    ""
  );
}

function getAccumulatedSourceForContainer(currentContainer, currentSource) {
  const priorSources = [];

  if (currentContainer?.dataset.accumulates === "true") {
    const group = accumulateGroup(currentContainer);
    const containers = Array.from(
      document.querySelectorAll(".runnable, .no-run"),
    );
    for (const candidate of containers) {
      if (candidate === currentContainer) break;
      if (
        candidate.dataset.accumulates === "true" &&
        accumulateGroup(candidate) === group
      ) {
        const candidateSource = sourceForContainer(candidate);
        if (candidateSource.trim().length > 0) {
          priorSources.push(candidateSource);
        }
      }
    }
  }

  const prefix = priorSources.join("\n\n");
  const source = prefix ? `${prefix}\n\n${currentSource}` : currentSource;

  return {
    source,
    currentSource,
    lineOffset: prefix ? prefix.split("\n").length + 1 : 0,
  };
}

function getAccumulatedSource(editor) {
  const currentContainer = editor.closest(".runnable");
  return getAccumulatedSourceForContainer(
    currentContainer,
    editor.value || "",
  );
}

function getHoverSource(editor) {
  const currentContainer = editor.closest(".runnable, .no-run");
  const currentSource = editor.matches(".code-editable")
    ? editor.value || ""
    : sourceForContainer(currentContainer);
  return getAccumulatedSourceForContainer(currentContainer, currentSource);
}

function diagnosticsForCurrentExample(checkResult, lineOffset, currentSource) {
  if (!checkResult || !Array.isArray(checkResult.diagnostics)) {
    return checkResult;
  }

  const lastLine = lineOffset + currentSource.split("\n").length;
  return {
    ...checkResult,
    diagnostics: checkResult.diagnostics
      .filter(
        (diagnostic) =>
          diagnostic.line > lineOffset && diagnostic.line <= lastLine,
      )
      .map((diagnostic) => ({
        ...diagnostic,
        line: diagnostic.line - lineOffset,
      })),
  };
}

function renderFollowingAccumulatedExamples(editor) {
  const currentContainer = editor.closest(".runnable");
  if (currentContainer?.dataset.accumulates !== "true") return;

  const group = accumulateGroup(currentContainer);
  const containers = Array.from(
    document.querySelectorAll(".runnable, .no-run"),
  );
  const currentIndex = containers.indexOf(currentContainer);

  for (const candidate of containers.slice(currentIndex + 1)) {
    if (
      candidate.dataset.accumulates === "true" &&
      accumulateGroup(candidate) === group
    ) {
      const candidateEditor = candidate.querySelector(".code-editable");
      if (candidateEditor) {
        editorRenderers.get(candidateEditor)?.();
      }
    }
  }
}

function initLowerable(el) {
  el.addEventListener("click", async function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let result = container.querySelector(".result");
    let { source } = getAccumulatedSource(editor);
    el.disabled = true;

    try {
      let output = await talk.showIr(source);
      result.innerHTML = `<pre class="output ir">${output.highlightedIr}</pre>`;
      result.classList.add("active");
    } catch (error) {
      showActionError(result, error);
    } finally {
      if (!talk.failed) el.disabled = false;
    }
  });
}

function initFormattable(el) {
  el.addEventListener("click", async function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let result = container.querySelector(".result");
    let content = editor.value || "";
    el.disabled = true;

    try {
      let formatted = await talk.format(content);
      editor.value = formatted;
      editor.dispatchEvent(new Event("input", { bubbles: true }));
    } catch (error) {
      showActionError(result, error);
    } finally {
      if (!talk.failed) el.disabled = false;
    }
  });
}

async function renderOutputStream(stream, element) {
  const decoder = new TextDecoder();
  const reader = stream.getReader();

  try {
    while (true) {
      const { value, done } = await reader.read();
      if (done) break;

      const text = decoder.decode(value, { stream: true });
      if (text) {
        element.hidden = false;
        element.append(document.createTextNode(text));
      }
    }

    const text = decoder.decode();
    if (text) {
      element.hidden = false;
      element.append(document.createTextNode(text));
    }
  } finally {
    reader.releaseLock();
  }
}

function initRunnable(el) {
  el.addEventListener("click", async function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let result = container.querySelector(".result");
    let { source } = getAccumulatedSource(editor);
    el.disabled = true;

    try {
      const run = talk.runProgram(source);
      const stdout = document.createElement("pre");
      stdout.className = "output";
      stdout.hidden = true;
      const stderr = document.createElement("pre");
      stderr.className = "output error";
      stderr.hidden = true;
      const value = document.createElement("pre");
      value.className = "value";
      value.hidden = true;
      result.replaceChildren(stdout, stderr, value);
      result.classList.add("active");

      const streamsDone = Promise.all([
        renderOutputStream(run.stdout, stdout),
        renderOutputStream(run.stderr, stderr),
      ]);
      const [output] = await Promise.all([run.result, streamsDone]);
      value.innerHTML = `<span class="arrow">=> </span>${output.highlightedValue}`;
      value.hidden = false;
    } catch (error) {
      showActionError(result, error);
    } finally {
      if (!talk.failed) el.disabled = false;
    }
  });
}

function showActionError(result, error) {
  console.error(error);
  result.textContent = error.message || String(error);
  result.classList.add("active");
}

function setEditorValue(el, value, selectionStart, selectionEnd = selectionStart) {
  el.value = value;
  el.setSelectionRange(selectionStart, selectionEnd);
  el.dispatchEvent(new Event("input", { bubbles: true }));
}

function indentSelection(el) {
  let { value, selectionStart, selectionEnd } = el;

  if (selectionStart === selectionEnd) {
    el.setRangeText("\t", selectionStart, selectionEnd, "end");
    el.dispatchEvent(new Event("input", { bubbles: true }));
    return;
  }

  let lineStart = value.lastIndexOf("\n", Math.max(0, selectionStart - 1)) + 1;
  let lineEndIndex = value.indexOf("\n", selectionEnd);
  let lineEnd = lineEndIndex === -1 ? value.length : lineEndIndex;
  let selectedBlock = value.slice(lineStart, lineEnd);
  let indentedBlock = `\t${selectedBlock.replace(/\n/g, "\n\t")}`;
  let indentedLineCount = selectedBlock.split("\n").length;

  setEditorValue(
    el,
    `${value.slice(0, lineStart)}${indentedBlock}${value.slice(lineEnd)}`,
    selectionStart + 1,
    selectionEnd + indentedLineCount,
  );
}

function unindentSelection(el) {
  let { value, selectionStart, selectionEnd } = el;
  let lineStart = value.lastIndexOf("\n", Math.max(0, selectionStart - 1)) + 1;
  let lineEndIndex = value.indexOf("\n", selectionEnd);
  let lineEnd = lineEndIndex === -1 ? value.length : lineEndIndex;
  let selectedBlock = value.slice(lineStart, lineEnd);
  let lines = selectedBlock.split("\n");
  let removedBeforeSelectionStart = 0;
  let removedBeforeSelectionEnd = 0;

  let unindentedBlock = lines
    .map((line, index) => {
      if (!line.startsWith("\t")) return line;
      if (index === 0 && selectionStart > lineStart) {
        removedBeforeSelectionStart = 1;
      }
      removedBeforeSelectionEnd += 1;
      return line.slice(1);
    })
    .join("\n");

  if (unindentedBlock === selectedBlock) return;

  setEditorValue(
    el,
    `${value.slice(0, lineStart)}${unindentedBlock}${value.slice(lineEnd)}`,
    Math.max(lineStart, selectionStart - removedBeforeSelectionStart),
    Math.max(lineStart, selectionEnd - removedBeforeSelectionEnd),
  );
}

function initEditable(el) {
  let container = el.closest(".runnable");
  if (!container) return;
  let highlight = container.querySelector(".code-highlight");
  if (!highlight) return;
  let diagnosticsLayer = getDiagnosticsLayer(container);

  let isComposing = false;
  let renderVersion = 0;

  let resizeEditor = () => {
    el.style.height = "auto";
    el.style.height = `${el.scrollHeight}px`;
  };

  let renderHighlight = async () => {
    const version = ++renderVersion;
    let { source, currentSource, lineOffset } = getAccumulatedSource(el);

    try {
      const analysis = await talk.analyze(source, currentSource);
      if (version !== renderVersion || el.value !== currentSource) return;

      const checkResult = diagnosticsForCurrentExample(
        analysis.checkResult,
        lineOffset,
        currentSource,
      );
      highlight.innerHTML = analysis.highlightedSource;
      hoverTooltips.hide();
      syncScroll();
      renderDiagnostics(container, highlight, diagnosticsLayer, checkResult);
    } catch (error) {
      if (!talk.failed) console.error(error);
    }
  };

  editorRenderers.set(el, renderHighlight);

  let handleInput = () => {
    resizeEditor();
    if (isComposing) return;
    hoverTooltips.hide();
    renderHighlight();
    renderFollowingAccumulatedExamples(el);
  };

  let syncScroll = () => {
    highlight.scrollTop = el.scrollTop;
    highlight.scrollLeft = el.scrollLeft;
    if (diagnosticsLayer) {
      diagnosticsLayer.diagnosticsEl.scrollTop = el.scrollTop;
      diagnosticsLayer.diagnosticsEl.scrollLeft = el.scrollLeft;
    }
  };

  el.addEventListener("input", handleInput);
  el.addEventListener("scroll", syncScroll);
  el.addEventListener("keydown", (event) => {
    if (event.key !== "Tab" || event.ctrlKey || event.metaKey || event.altKey) {
      return;
    }

    event.preventDefault();
    if (event.shiftKey) {
      unindentSelection(el);
    } else {
      indentSelection(el);
    }
  });
  el.addEventListener("compositionstart", () => {
    isComposing = true;
  });
  el.addEventListener("compositionend", () => {
    isComposing = false;
    handleInput();
  });

  resizeEditor();
}
