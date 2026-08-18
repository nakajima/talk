const response = await fetch("/playground-examples.json");
if (!response.ok) {
  throw new Error(`Failed to load playground examples: ${response.status}`);
}

const exampleList = await response.json();
const examples = new Map(exampleList.map((example) => [example.id, example]));

for (const container of document.querySelectorAll("[data-example-catalog]")) {
  const initial = container.dataset.initialExample || exampleList[0]?.id;
  for (const example of exampleList) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "example-button";
    button.dataset.example = example.id;
    button.textContent = example.title;
    button.title = example.summary;
    if (example.id === initial) button.setAttribute("aria-current", "true");
    container.appendChild(button);
  }
}

function setNativeOnly(runner, nativeOnly) {
  runner.dataset.nativeOnly = String(nativeOnly);
  const runButton = runner.querySelector("button.run");
  const control = runButton?.closest(".action-control");
  if (!runButton || !control) return;

  if (nativeOnly) {
    runButton.disabled = true;
    control.dataset.nativeExample = "true";
    control.dataset.tooltip = "This example requires the native Talk CLI";
    control.setAttribute("aria-label", control.dataset.tooltip);
    control.setAttribute("tabindex", "0");
  } else if (control.dataset.nativeExample === "true") {
    delete control.dataset.nativeExample;
    control.removeAttribute("data-tooltip");
    control.removeAttribute("aria-label");
    control.removeAttribute("tabindex");
    runButton.disabled = false;
  }
}

function loadExample(button, focus = true) {
  const example = examples.get(button.dataset.example || "");
  const runner = button.closest(".playground-scope")?.querySelector(".playground-runner");
  const editor = runner?.querySelector(".code-editable");
  if (!example || !runner || !editor) return;

  editor.value = example.source;
  const highlight = runner.querySelector(".code-highlight");
  if (highlight) highlight.textContent = example.source;
  editor.dispatchEvent(new Event("input", { bubbles: true }));
  runner.querySelector(".result")?.replaceChildren();

  const empty = runner.querySelector(".output-empty");
  if (empty) {
    empty.textContent = example.nativeOnly
      ? `${example.summary} Run this one with the native Talk CLI.`
      : example.summary;
  }
  setNativeOnly(runner, example.nativeOnly);

  for (const candidate of button.parentElement?.querySelectorAll("[data-example]") ?? []) {
    candidate.removeAttribute("aria-current");
  }
  button.setAttribute("aria-current", "true");

  if (focus) {
    editor.focus();
    editor.setSelectionRange(0, 0);
  }
}

for (const button of document.querySelectorAll("[data-example]")) {
  button.addEventListener("click", () => loadExample(button));
}

const initialButton = document.querySelector("[data-example][aria-current=\"true\"]");
if (initialButton) loadExample(initialButton, false);

for (const editor of document.querySelectorAll(".playground-runner .code-editable")) {
  editor.addEventListener("keydown", (event) => {
    if (event.key !== "Enter" || !(event.ctrlKey || event.metaKey)) return;
    event.preventDefault();
    editor.closest(".playground-runner")?.querySelector("button.run")?.click();
  });
}

for (const runButton of document.querySelectorAll(".playground-runner button.run")) {
  new MutationObserver(() => {
    const runner = runButton.closest(".playground-runner");
    if (runner?.dataset.nativeOnly === "true" && !runButton.disabled) {
      runButton.disabled = true;
    }
  }).observe(runButton, {
    attributes: true,
    attributeFilter: ["disabled"],
  });
}

for (const status of document.querySelectorAll(".runtime-status")) {
  const runButton = document.querySelector(".playground-runner button.run");
  if (!runButton) continue;

  const update = () => {
    const control = runButton.closest(".action-control");
    const ready = !control?.hasAttribute("data-tooltip")
      || control?.dataset.nativeExample === "true";
    status.dataset.ready = String(ready);
    status.textContent = ready ? "runtime ready" : "runtime loading";
  };

  new MutationObserver(update).observe(runButton.closest(".action-control"), {
    attributes: true,
  });
  update();
}
