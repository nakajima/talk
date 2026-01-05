import init, {
  highlight,
  format,
  run_program,
  version as wasmVersion,
  show_ir,
  check,
} from "/pkg/talk_wasm.js?123";

function getTooltipContent(tokenEl) {
  return `Token: ${tokenEl.textContent || ""}`;
}

const DEFAULT_HUD_TEXT = "Token: (none)";
let tokenHud = null;
let tokenHudOwner = null;

function getHudContent(tokenEl) {
  const tokenText = (tokenEl.textContent || "").replace(/\s+/g, " ").trim();
  const tokenType = tokenEl.className ? tokenEl.className.trim() : "token";
  if (!tokenText) {
    return `${tokenType}: (whitespace)`;
  }
  return `${tokenType}: ${tokenText}`;
}

function getTokenHud() {
  if (tokenHud) return tokenHud;

  const hudEl = document.createElement("div");
  hudEl.className = "token-hud";
  hudEl.setAttribute("aria-live", "polite");
  hudEl.dataset.active = "false";
  hudEl.textContent = DEFAULT_HUD_TEXT;
  document.body.appendChild(hudEl);

  tokenHud = {
    setToken: (owner, tokenEl) => {
      tokenHudOwner = owner;
      hudEl.textContent = getHudContent(tokenEl);
      hudEl.dataset.active = "true";
    },
    clear: (owner) => {
      if (tokenHudOwner !== owner) return;
      tokenHudOwner = null;
      hudEl.textContent = DEFAULT_HUD_TEXT;
      hudEl.dataset.active = "false";
    },
  };

  return tokenHud;
}

function createTooltip(el) {
  const tippyApi = window.tippy;
  if (typeof tippyApi !== "function") {
    const tooltipEl = document.createElement("div");
    tooltipEl.style.position = "fixed";
    tooltipEl.style.zIndex = "9999";
    tooltipEl.style.background = "rgb(30, 28, 36)";
    tooltipEl.style.color = "white";
    tooltipEl.style.padding = "4px 8px";
    tooltipEl.style.borderRadius = "4px";
    tooltipEl.style.fontSize = "12px";
    tooltipEl.style.lineHeight = "1.4";
    tooltipEl.style.pointerEvents = "none";
    tooltipEl.style.whiteSpace = "pre";
    tooltipEl.style.display = "none";
    document.body.appendChild(tooltipEl);

    return {
      showAt: (rect, content) => {
        tooltipEl.textContent = content;
        tooltipEl.style.left = `${rect.left + rect.width / 2}px`;
        tooltipEl.style.top = `${rect.top - 8}px`;
        tooltipEl.style.transform = "translate(-50%, -100%)";
        tooltipEl.style.display = "block";
      },
      hide: () => {
        tooltipEl.style.display = "none";
      },
    };
  }

  let tooltip = tippyApi(el, {
    trigger: "manual",
    placement: "top",
    offset: [0, 6],
    animation: false,
    duration: 0,
  });
  if (Array.isArray(tooltip)) {
    tooltip = tooltip[0];
  }

  return {
    showAt: (rect, content) => {
      tooltip.setProps({ getReferenceClientRect: () => rect });
      tooltip.setContent(content);
      tooltip.show();
    },
    hide: () => {
      tooltip.hide();
    },
  };
}

function initHoverTooltips(el, highlightEl) {
  const tooltip = createTooltip(el);
  const hud = getTokenHud();
  const hudOwner = {};

  let pending = false;
  let lastPointer = null;

  const hideTooltip = () => {
    tooltip.hide();
    hud.clear(hudOwner);
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
    const rect = token.getBoundingClientRect();
    tooltip.showAt(rect, getTooltipContent(token));
    hud.setToken(hudOwner, token);
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
  await init();

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

function initLowerable(el) {
  el.addEventListener("click", function (e) {
    let container = e.target.closest(".runnable");
    if (!container) return;
    let editor = container.querySelector(".code-editable");
    if (!editor) return;
    let content = editor.value || "";
    let output = talk.show_ir(content);
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
    let content = editor.value || "";
    let output = await talk.runProgram(content);
    console.log(output);
    let result = container.querySelector(".result");
    result.innerHTML = `
      <pre class="output">${output.output}</pre>
      <pre class="value"><span class="arrow">=> </span>${output.highlightedValue}</pre>`;
    result.classList.add("active");
  });
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
    let source = el.value || "";
    let checkResult = null;
    try {
      checkResult = check(source);
    } catch (err) {
      console.error(err);
    }
    highlight.innerHTML = talk.highlight(source);
    hoverTooltips.hide();
    syncScroll();
    renderDiagnostics(container, highlight, diagnosticsLayer, checkResult);
  };

  let handleInput = () => {
    resizeEditor();
    if (isComposing) return;
    renderHighlight();
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
