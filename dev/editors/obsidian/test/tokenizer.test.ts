import {
  matchOpeningFence,
  isClosingFence,
  tokenizeLine,
} from "../src/tlkHighlighter";

let failures = 0;
function check(name: string, cond: boolean) {
  if (!cond) {
    failures++;
    console.error("FAIL:", name);
  } else {
    console.log("ok:", name);
  }
}

// Fence detection
check("open ```tlk", matchOpeningFence("```tlk")?.len === 3);
check("open ~~~~tlk", matchOpeningFence("~~~~tlk")?.char === "~");
check("open with indent", matchOpeningFence("  ```tlk") !== null);
check("open with info", matchOpeningFence("```tlk some info") !== null);
check("reject js", matchOpeningFence("```js") === null);
check("reject tlkx", matchOpeningFence("```tlkx") === null);
check("close exact", isClosingFence("```", "`", 3));
check("close longer", isClosingFence("`````", "`", 3));
check("reject shorter", !isClosingFence("``", "`", 3));
check("reject mixed", !isClosingFence("`~`", "`", 3));
check("reject text", !isClosingFence("``` x", "`", 3));

// Tokenizer
function toks(text: string, blockComment = { value: false }) {
  const out: { from: number; to: number; cls: string }[] = [];
  tokenizeLine(text, 0, blockComment, out);
  return out.map((t) => [t.cls, text.slice(t.from, t.to)]);
}

check(
  "keywords",
  JSON.stringify(toks("func main() -> Int {")) ===
    JSON.stringify([["cm-keyword", "func"]]),
);
check(
  "string with escape",
  JSON.stringify(toks('let s = "he\\"llo" // tail')) ===
    JSON.stringify([
      ["cm-keyword", "let"],
      ["cm-string", '"he\\"llo"'],
      ["cm-comment", "// tail"],
    ]),
);
check(
  "quoted identifier is not a string",
  JSON.stringify(toks('#"quoted id"')) ===
    JSON.stringify([["cm-variable", '#"quoted id"']]),
);
check(
  "unterminated quoted identifier runs to EOL",
  JSON.stringify(toks('#"abc')) === JSON.stringify([["cm-variable", '#"abc']]),
);
check(
  "char literal",
  JSON.stringify(toks("let c = 'x'")) ===
    JSON.stringify([
      ["cm-keyword", "let"],
      ["cm-string", "'x'"],
    ]),
);
check(
  "char literal with escape",
  JSON.stringify(toks("let c = '\\n'")) ===
    JSON.stringify([
      ["cm-keyword", "let"],
      ["cm-string", "'\\n'"],
    ]),
);
check(
  "effect labels are not strings",
  JSON.stringify(toks("effect 'fizz(fn: () 'buzz -> ())")) ===
    JSON.stringify([]),
);
check(
  "effect label then real string",
  JSON.stringify(toks("effect 'io let s = \"hi\"")) ===
    JSON.stringify([
      ["cm-keyword", "let"],
      ["cm-string", '"hi"'],
    ]),
);
check(
  "numbers",
  JSON.stringify(toks("return 42 + 3.14")) ===
    JSON.stringify([
      ["cm-keyword", "return"],
      ["cm-number", "42"],
      ["cm-number", "3.14"],
    ]),
);

// Block comments across lines
const bc = { value: false };
check(
  "block comment opens",
  JSON.stringify(toks("/* a */ code /* b", bc)) ===
    JSON.stringify([
      ["cm-comment", "/* a */"],
      ["cm-comment", "/* b"],
    ]) && bc.value === true,
);
check(
  "block comment continues next line",
  JSON.stringify(toks("still comment */ let", bc)) ===
    JSON.stringify([
      ["cm-comment", "still comment */"],
      ["cm-keyword", "let"],
    ]) && bc.value === false,
);
check(
  "comment hides string",
  JSON.stringify(toks('// "not a string"')) ===
    JSON.stringify([["cm-comment", '// "not a string"']]),
);
check(
  "true/false are keywords",
  JSON.stringify(toks("true false")) ===
    JSON.stringify([
      ["cm-keyword", "true"],
      ["cm-keyword", "false"],
    ]),
);

if (failures > 0) process.exit(1);
console.log("all tests passed");
