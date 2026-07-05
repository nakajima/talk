vim.bo.commentstring = "// %s"
vim.bo.comments = "://"
vim.bo.expandtab = false
vim.bo.tabstop = 4
vim.bo.shiftwidth = 4
vim.bo.softtabstop = 0
vim.bo.autoindent = true
vim.bo.smartindent = false
vim.bo.suffixesadd = ".tlk"
vim.bo.matchpairs = "(:),{:},[:]"

if vim.fn.executable("talk") == 1 then
  vim.bo.formatprg = "talk format -"
end

vim.b.undo_ftplugin = table.concat({
  "setlocal commentstring<",
  "setlocal comments<",
  "setlocal expandtab<",
  "setlocal tabstop<",
  "setlocal shiftwidth<",
  "setlocal softtabstop<",
  "setlocal autoindent<",
  "setlocal smartindent<",
  "setlocal suffixesadd<",
  "setlocal matchpairs<",
  "setlocal formatprg<",
}, " | ")
