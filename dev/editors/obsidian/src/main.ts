import { Plugin, loadPrism } from "obsidian";
import { tlkHighlighter } from "./tlkHighlighter";

// Mirrors dev/editors/vscode/syntax/talktalk.tmLanguage.json.
// Token order matters: quoted identifiers (#"...") must be tried before
// strings, since #"..."" would otherwise open a plain string.
export default class TalkTalkPlugin extends Plugin {
  async onload() {
    const prism = await loadPrism();

    prism.languages.tlk = {
      comment: [
        { pattern: /\/\*[\s\S]*?\*\//, greedy: true },
        { pattern: /\/\/.*/, greedy: true },
      ],
      "quoted-identifier": {
        pattern: /#"[^"\\\r\n]+"/,
        greedy: true,
        alias: "variable",
        inside: {
          punctuation: /^#"|"$/,
        },
      },
      string: {
        pattern: /"(?:\\[\s\S]|[^"\\\r\n])*"/,
        greedy: true,
        inside: {
          escape: /\\./,
        },
      },
      char: {
        pattern: /'(?:[^'\\\r\n]|\\(?:[ntr"'\\]|u\{[0-9A-Fa-f]{1,6}\}))'/,
        greedy: true,
        alias: "string",
      },
      keyword:
        /\b(?:func|let|if|else|true|false|loop|enum|case|match|return|struct|extend|break|init|protocol|import)\b/,
      number: /\b\d+(?:\.\d+)?\b/,
    };

    this.registerEditorExtension(tlkHighlighter);
  }
}
