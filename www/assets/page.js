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
const {
  default: init,
  highlight,
  format,
  run_program,
  version: wasmVersion,
  show_ir,
  check,
  hover,
} = await import(`/pkg/talk_wasm.js${wasmCacheKey}`);

function createTooltip() {
  const tooltipEl = document.createElement("div");
  tooltipEl.className = "code-hover-popover";
  tooltipEl.hidden = true;
  document.body.appendChild(tooltipEl);

  return {
    showAt: (rect, content) => {
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
    },
    hide: () => {
      tooltipEl.hidden = true;
    },
  };
}

function initHoverTooltips(el, highlightEl) {
  const tooltip = createTooltip();
  const encoder = new TextEncoder();

  let pending = false;
  let lastPointer = null;
  let currentToken = null;
  let hoverTimer = null;

  const cancelHoverTimer = () => {
    if (hoverTimer === null) return;
    clearTimeout(hoverTimer);
    hoverTimer = null;
  };

  const hideTooltip = () => {
    cancelHoverTimer();
    currentToken = null;
    tooltip.hide();
  };

  const utf8Length = (text) => encoder.encode(text).length;

  const charOffsetForToken = (tokenEl) => {
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

  const showHover = (tokenEl) => {
    if (!tokenEl.isConnected) return;

    const { source, currentSource } = getAccumulatedSource(el);
    const tokenText = tokenEl.textContent || "";
    const charOffset =
      charOffsetForToken(tokenEl) + Math.floor(tokenText.length / 2);
    const byteOffset =
      utf8Length(source) -
      utf8Length(currentSource) +
      utf8Length(currentSource.slice(0, charOffset));

    let result;
    try {
      result = hover(source, byteOffset);
    } catch (err) {
      console.error(err);
      return;
    }

    const contents = result?.hover?.contents;
    if (!contents || currentToken !== tokenEl) return;
    tooltip.showAt(tokenEl.getBoundingClientRect(), contents);
  };

  const scheduleHover = (tokenEl) => {
    cancelHoverTimer();
    hoverTimer = setTimeout(() => {
      hoverTimer = null;
      showHover(tokenEl);
    }, 200);
  };

  const tokenFromPoint = (x, y) => {
    const previousPointerEvents = el.style.pointerEvents;
    el.style.pointerEvents = "none";
    const elementsFromPoint = document.elementsFromPoint
      ? document.elementsFromPoint(x, y)
      : null;
    const topElement = document.elementFromPoint(x, y);
    el.style.pointerEvents = previousPointerEvents;

    if (Array.isArray(elementsFromPoint)) {
      for (const element of elementsFromPoint) {
        if (!(element instanceof HTMLElement)) continue;
        if (element.tagName !== "SPAN") continue;
        if (element.closest(".code-highlight") !== highlightEl) continue;
        return element;
      }
    }

    if (topElement instanceof HTMLElement) {
      if (
        topElement.tagName === "SPAN" &&
        topElement.closest(".code-highlight") === highlightEl
      ) {
        return topElement;
      }
    }

    const spans = highlightEl.querySelectorAll("span");
    for (const span of spans) {
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

  const updateTooltip = () => {
    if (!lastPointer) return;
    if (typeof lastPointer.buttons === "number" && lastPointer.buttons !== 0) {
      hideTooltip();
      return;
    }
    const highlightRect = highlightEl.getBoundingClientRect();
    if (
      lastPointer.x < highlightRect.left ||
      lastPointer.x > highlightRect.right ||
      lastPointer.y < highlightRect.top ||
      lastPointer.y > highlightRect.bottom
    ) {
      hideTooltip();
      return;
    }
    const token = tokenFromPoint(lastPointer.x, lastPointer.y);
    if (!token) {
      hideTooltip();
      return;
    }
    if (token === currentToken) return;
    currentToken = token;
    tooltip.hide();
    scheduleHover(token);
  };

  const scheduleUpdate = (event) => {
    lastPointer = {
      x: event.clientX,
      y: event.clientY,
      buttons: event.buttons,
    };
    if (pending) return;
    pending = true;
    requestAnimationFrame(() => {
      pending = false;
      updateTooltip();
    });
  };

  el.addEventListener("pointermove", scheduleUpdate);
  el.addEventListener("mousemove", scheduleUpdate);
  window.addEventListener("pointermove", scheduleUpdate, { passive: true });
  window.addEventListener("mousemove", scheduleUpdate, { passive: true });
  el.addEventListener("pointerleave", hideTooltip);
  el.addEventListener("mouseleave", hideTooltip);
  el.addEventListener("pointerdown", hideTooltip);
  el.addEventListener("scroll", hideTooltip);
  el.addEventListener("blur", hideTooltip);

  return { hide: hideTooltip };
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
  if (actions && actions.parentNode === container) {
    container.insertBefore(list, actions);
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

export async function loadTalk() {
  await init({
    module_or_path: `/pkg/talk_wasm_bg.wasm${wasmCacheKey}`,
  });

  return {
    runProgram: (source) => run_program(source),
    highlight: (source) => highlight(source),
    format: (source) => format(source),
    check: (source) => check(source),
    show_ir: (source) => show_ir(source),
    version: () => wasmVersion(),
  };
}

const talk = await loadTalk();
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

function getAccumulatedSource(editor) {
  const currentContainer = editor.closest(".runnable");
  const currentSource = editor.value || "";
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
        const candidateEditor = candidate.querySelector(".code-editable");
        const candidateSource =
          candidateEditor?.value ?? candidate.dataset.source ?? "";
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
  el.addEventListener("click", function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let { source } = getAccumulatedSource(editor);
    let output = talk.show_ir(source);
    let result = container.querySelector(".result");
    result.innerHTML = `<pre class="output ir">${output.highlightedIr}</pre>`;
    result.classList.add("active");
  });
}

function initFormattable(el) {
  el.addEventListener("click", function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let content = editor.value || "";
    let formatted = "";
    try {
      formatted = talk.format(content);
    } catch (err) {
      console.error(err);
      return;
    }
    editor.value = formatted;
    editor.dispatchEvent(new Event("input", { bubbles: true }));
  });
}

function initRunnable(el) {
  el.addEventListener("click", async function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let { source } = getAccumulatedSource(editor);
    let output = await talk.runProgram(source);
    console.log(output);
    let result = container.querySelector(".result");
    result.innerHTML = `
      <pre class="output">${output.output}</pre>
      <pre class="value"><span class="arrow">=> </span>${output.highlightedValue}</pre>`;
    result.classList.add("active");
  });
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
  let hoverTooltips = initHoverTooltips(el, highlight);

  let resizeEditor = () => {
    el.style.height = "auto";
    el.style.height = `${el.scrollHeight}px`;
  };

  let renderHighlight = () => {
    let { source, currentSource, lineOffset } = getAccumulatedSource(el);
    let checkResult = null;
    try {
      checkResult = diagnosticsForCurrentExample(
        check(source),
        lineOffset,
        currentSource,
      );
    } catch (err) {
      console.error(err);
    }
    highlight.innerHTML = talk.highlight(currentSource);
    hoverTooltips.hide();
    syncScroll();
    renderDiagnostics(container, highlight, diagnosticsLayer, checkResult);
  };

  editorRenderers.set(el, renderHighlight);

  let handleInput = () => {
    resizeEditor();
    if (isComposing) return;
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
  renderHighlight();
}

console.log(await talk.runProgram("1 + 2 + 3"));
