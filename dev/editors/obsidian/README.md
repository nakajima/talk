# TalkTalk Obsidian plugin

Syntax highlighting for TalkTalk code in ` ```tlk ` code blocks.

## How it works

Reading mode: Obsidian highlights code blocks with Prism.js. The plugin waits
for Obsidian's Prism instance (`loadPrism()`) and registers
`Prism.languages.tlk`, mirroring the TextMate grammar in
`dev/editors/vscode/syntax/talktalk.tmLanguage.json`.

Source mode and Live Preview (while editing inside a fence): Obsidian's
editor is CodeMirror 6, which knows nothing about Prism. The plugin registers
a small CM6 ViewPlugin (`src/tlkHighlighter.ts`) that scans for ` ```tlk `
fences and decorates tokens with the `cm-*` classes Obsidian themes already
style (`cm-keyword`, `cm-string`, `cm-comment`, `cm-number`, `cm-variable`).

Known parity gap: inside the editor, string escapes (e.g. `\n`) are not
highlighted separately from the surrounding string, unlike in Reading mode.

## Build

```sh
npm install
npm run build   # production bundle -> main.js
npm run dev     # watch mode
npm test        # tokenizer unit tests
```

## Install in a vault

Copy (or symlink) `manifest.json` and `main.js` into
`<vault>/.obsidian/plugins/talktalk/`, then enable "TalkTalk" under
Settings -> Community plugins (with Restricted Mode off).

For development, symlink the whole directory so `npm run dev` rebuilds are
picked up after an Obsidian reload:

```sh
mkdir -p <vault>/.obsidian/plugins
ln -s "$PWD" <vault>/.obsidian/plugins/talktalk
```

## Test

Open a note with:

    ```tlk
    // line comment
    /* block comment */
    import "std/io"
    let greeting = "hello\n"
    let c = 'x'
    func main() -> Int {
        #"quoted identifier"
        return 42
    }
    ```
