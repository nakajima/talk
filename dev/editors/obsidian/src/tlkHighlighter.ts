import { Extension, RangeSetBuilder } from "@codemirror/state";
import {
  Decoration,
  DecorationSet,
  EditorView,
  ViewPlugin,
  ViewUpdate,
} from "@codemirror/view";

// Same grammar as the Prism definition in main.ts and the TextMate grammar in
// dev/editors/vscode/syntax/talktalk.tmLanguage.json, hand-rolled so we can
// apply it to fenced code blocks in the editor. Decorations use the cm-*
// classes that Obsidian themes already style.

export const KEYWORDS = new Set([
  "func",
  "let",
  "if",
  "else",
  "true",
  "false",
  "loop",
  "enum",
  "case",
  "match",
  "return",
  "struct",
  "extend",
  "break",
  "init",
  "protocol",
  "import",
]);

interface Token {
  from: number;
  to: number;
  cls: string;
}

export function matchOpeningFence(text: string): { char: string; len: number } | null {
  const m = /^\s*(`{3,}|~{3,})[ \t]*tlk(?:[ \t]+.*)?$/.exec(text);
  if (!m) return null;
  return { char: m[1][0], len: m[1].length };
}

export function isClosingFence(text: string, char: string, len: number): boolean {
  const trimmed = text.trim();
  if (trimmed.length < len) return false;
  for (const c of trimmed) {
    if (c !== char) return false;
  }
  return true;
}

export function tokenizeLine(
  text: string,
  lineFrom: number,
  blockComment: { value: boolean },
  tokens: Token[],
): void {
  const n = text.length;
  let i = 0;
  const push = (from: number, to: number, cls: string) => {
    if (to > from) tokens.push({ from: lineFrom + from, to: lineFrom + to, cls });
  };

  while (i < n) {
    if (blockComment.value) {
      const end = text.indexOf("*/", i);
      if (end === -1) {
        push(i, n, "cm-comment");
        return;
      }
      push(i, end + 2, "cm-comment");
      i = end + 2;
      blockComment.value = false;
      continue;
    }

    const ch = text[i];
    const next = i + 1 < n ? text[i + 1] : "";

    if (ch === "/" && next === "/") {
      push(i, n, "cm-comment");
      return;
    }

    if (ch === "/" && next === "*") {
      const end = text.indexOf("*/", i + 2);
      if (end === -1) {
        push(i, n, "cm-comment");
        blockComment.value = true;
        return;
      }
      push(i, end + 2, "cm-comment");
      i = end + 2;
      continue;
    }

    // Quoted identifier: #"..." must be tried before plain strings.
    if (ch === "#" && next === '"') {
      let j = i + 2;
      while (j < n && text[j] !== '"') j++;
      j = Math.min(j + 1, n);
      push(i, j, "cm-variable");
      i = j;
      continue;
    }

    // String literal.
    if (ch === '"') {
      let j = i + 1;
      while (j < n) {
        if (text[j] === "\\") {
          j += 2;
          continue;
        }
        if (text[j] === '"') {
          j++;
          break;
        }
        j++;
      }
      push(i, j, "cm-string");
      i = j;
      continue;
    }

    // Char literal. A single quote is only a char literal when it closes
    // immediately after one character or escape; otherwise it marks an
    // effect label ('io, 'fizz(...)) and must not swallow the line.
    if (ch === "'") {
      const m = /^'(?:[^'\\]|\\(?:[ntr"'\\]|u\{[0-9A-Fa-f]{1,6}\}))'/.exec(
        text.slice(i),
      );
      if (m) {
        push(i, i + m[0].length, "cm-string");
        i += m[0].length;
        continue;
      }
      i++;
      continue;
    }

    if (ch >= "0" && ch <= "9") {
      const m = /^\d+(\.\d+)?/.exec(text.slice(i));
      const len = m ? m[0].length : 1;
      push(i, i + len, "cm-number");
      i += len;
      continue;
    }

    if (/[A-Za-z_]/.test(ch)) {
      const m = /^[A-Za-z_]\w*/.exec(text.slice(i));
      const word = m ? m[0] : ch;
      if (KEYWORDS.has(word)) push(i, i + word.length, "cm-keyword");
      i += word.length;
      continue;
    }

    i++;
  }
}

function buildDecorations(view: EditorView): DecorationSet {
  const builder = new RangeSetBuilder<Decoration>();
  const doc = view.state.doc;
  const tokens: Token[] = [];
  const blockComment = { value: false };
  let fence: { char: string; len: number } | null = null;

  for (let ln = 1; ln <= doc.lines; ln++) {
    const line = doc.line(ln);
    if (fence) {
      if (isClosingFence(line.text, fence.char, fence.len)) {
        fence = null;
        blockComment.value = false;
        continue;
      }
      tokenizeLine(line.text, line.from, blockComment, tokens);
    } else {
      fence = matchOpeningFence(line.text);
    }
  }

  const cache = new Map<string, Decoration>();
  for (const t of tokens) {
    let deco = cache.get(t.cls);
    if (!deco) {
      deco = Decoration.mark({ class: t.cls });
      cache.set(t.cls, deco);
    }
    builder.add(t.from, t.to, deco);
  }
  return builder.finish();
}

export const tlkHighlighter: Extension = ViewPlugin.fromClass(
  class {
    decorations: DecorationSet;

    constructor(view: EditorView) {
      this.decorations = buildDecorations(view);
    }

    update(update: ViewUpdate) {
      if (update.docChanged || update.viewportChanged) {
        this.decorations = buildDecorations(update.view);
      }
    }
  },
  { decorations: (v) => v.decorations },
);
