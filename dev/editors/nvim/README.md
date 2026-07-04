# TalkTalk Neovim runtime files

Plain Neovim runtime support for `.tlk` files. This does not configure LSP.

## Contents

- `ftdetect/talktalk.lua`: detects `*.tlk` as `talktalk`
- `ftplugin/talktalk.lua`: buffer-local editing defaults
- `syntax/talktalk.vim`: regex syntax highlighting
- `indent/talktalk.vim`: brace, bracket, and paren indentation

## Install

Add this directory to Neovim's runtime path.

Using a plugin manager that accepts local directories:

```lua
{
  dir = "~/apps/talk/dev/editors/nvim",
  name = "talktalk.nvim",
}
```

Or directly:

```lua
vim.opt.runtimepath:prepend(vim.fn.expand("~/apps/talk/dev/editors/nvim"))
```

Then open a `.tlk` file. Neovim should set `filetype=talktalk`.

## Notes

- Comments are line comments: `// comment`.
- Indentation uses tabs to match `talk format` output.
- If `talk` is on `$PATH`, `formatprg` is set to `talk format -`.
- LSP setup is intentionally left to user config.
