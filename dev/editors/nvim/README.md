# TalkTalk Neovim runtime files

Plain Neovim runtime support for `.tlk` files. This does not configure LSP.

## Contents

- `ftdetect/talktalk.lua`: detects `*.tlk` as `talktalk`
- `ftplugin/talktalk.lua`: buffer-local editing defaults
- `syntax/talktalk.vim`: regex syntax highlighting
- `indent/talktalk.vim`: brace, bracket, and paren indentation
- `lua/neotest-talk/init.lua`: Neotest adapter for `.test.tlk` files

## Install

The `talk` CLI can download and install these runtime files into Neovim's data/site runtime directory:

```sh
talk setup nvim
```

Use `talk setup nvim --force` to overwrite older TalkTalk runtime files if they differ.

For development, add this directory to Neovim's runtime path instead.

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

## Neotest

After adding this directory to `runtimepath`, configure Neotest with:

```lua
require("neotest").setup({
  adapters = {
    require("neotest-talk")({
      command = "talk",
    }),
  },
})
```

The adapter discovers `test "name" { ... }` and `test("name") { ... }` in `*.test.tlk` files. File runs use `talk test --json`; single-test runs add `--filter NAME`.

## Notes

- Comments are line comments: `// comment`.
- Indentation uses tabs to match `talk format` output.
- If `talk` is on `$PATH`, `formatprg` is set to `talk format -`.
- LSP setup is intentionally left to user config.
