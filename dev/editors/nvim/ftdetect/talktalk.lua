vim.api.nvim_create_autocmd({ "BufRead", "BufNewFile" }, {
  group = vim.api.nvim_create_augroup("talktalk_filetype", { clear = true }),
  pattern = "*.tlk",
  command = "setfiletype talktalk",
})
