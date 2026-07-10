local lib = require("neotest.lib")
local ResultStatus = require("neotest.types").ResultStatus

local M = { name = "neotest-talk" }

local function is_word_char(char)
  return char:match("[%w_]") ~= nil
end

local function unescape_string(raw)
  local out = {}
  local index = 1
  while index <= #raw do
    local char = raw:sub(index, index)
    if char ~= "\\" then
      out[#out + 1] = char
      index = index + 1
    else
      local escaped = raw:sub(index + 1, index + 1)
      if escaped == "n" then
        out[#out + 1] = "\n"
        index = index + 2
      elseif escaped == "r" then
        out[#out + 1] = "\r"
        index = index + 2
      elseif escaped == "t" then
        out[#out + 1] = "\t"
        index = index + 2
      elseif escaped == "\"" then
        out[#out + 1] = "\""
        index = index + 2
      elseif escaped == "\\" then
        out[#out + 1] = "\\"
        index = index + 2
      elseif escaped == "u" and raw:sub(index + 2, index + 2) == "{" then
        local close = raw:find("}", index + 3, true)
        if close then
          local codepoint = tonumber(raw:sub(index + 3, close - 1), 16)
          if codepoint then
            out[#out + 1] = vim.fn.nr2char(codepoint)
          end
          index = close + 1
        else
          out[#out + 1] = escaped
          index = index + 2
        end
      else
        out[#out + 1] = escaped
        index = index + 2
      end
    end
  end
  return table.concat(out)
end

local function test_name_on_line(line)
  if line:match("^%s*//") then
    return nil
  end

  local _, finish = line:find("^%s*test")
  if not finish then
    return nil
  end

  local next_char = line:sub(finish + 1, finish + 1)
  if next_char ~= "" and is_word_char(next_char) then
    return nil
  end

  local index = finish + 1
  while line:sub(index, index):match("%s") do
    index = index + 1
  end
  if line:sub(index, index) == "(" then
    index = index + 1
    while line:sub(index, index):match("%s") do
      index = index + 1
    end
  end
  if line:sub(index, index) ~= "\"" then
    return nil
  end

  local raw = {}
  index = index + 1
  while index <= #line do
    local char = line:sub(index, index)
    if char == "\\" then
      raw[#raw + 1] = line:sub(index, index + 1)
      index = index + 2
    elseif char == "\"" then
      return unescape_string(table.concat(raw))
    else
      raw[#raw + 1] = char
      index = index + 1
    end
  end
  return nil
end

local function test_end_range(lines, start_lnum)
  local depth = 0
  local saw_open = false
  local in_string = false
  local escaped = false

  for lnum = start_lnum, #lines do
    local line = lines[lnum]
    local index = 1
    while index <= #line do
      local char = line:sub(index, index)
      local next_char = line:sub(index + 1, index + 1)

      if in_string then
        if escaped then
          escaped = false
        elseif char == "\\" then
          escaped = true
        elseif char == "\"" then
          in_string = false
        end
      elseif char == "/" and next_char == "/" then
        break
      elseif char == "\"" then
        in_string = true
      elseif char == "{" then
        depth = depth + 1
        saw_open = true
      elseif char == "}" then
        depth = depth - 1
        if saw_open and depth <= 0 then
          return lnum - 1, #line
        end
      end

      index = index + 1
    end
  end

  return start_lnum - 1, #(lines[start_lnum] or "")
end

local function position_id(position)
  if position.type == "file" then
    return position.path
  end
  return table.concat({ position.path, position.name, tostring(position.range[1] + 1) }, "::")
end

local function adapter_config(opts)
  opts = opts or {}
  return {
    command = opts.command or "talk",
    args = opts.args or {},
    cwd = opts.cwd,
    env = opts.env,
  }
end

local current_config = adapter_config({})

local function output_file(text)
  local path = vim.fn.tempname()
  vim.fn.writefile(vim.split(text or "", "\n", { plain = true }), path)
  return path
end

local function decode_json(text)
  if vim.json and vim.json.decode then
    local ok, decoded = pcall(vim.json.decode, text)
    if ok then
      return decoded
    end
  end
  local ok, decoded = pcall(vim.fn.json_decode, text)
  if ok then
    return decoded
  end
  return nil
end

local function collect_test_nodes(tree)
  local nodes = {}
  for _, node in tree:iter_nodes() do
    local position = node:data()
    if position.type == "test" then
      nodes[position.name] = nodes[position.name] or {}
      table.insert(nodes[position.name], node)
    end
  end
  return nodes
end

local function mark_container_results(tree, results, status, output_path, short)
  for _, node in tree:iter_nodes() do
    local position = node:data()
    if position.type == "file" or position.type == "dir" then
      results[position.id] = {
        status = status,
        output = output_path,
        short = short,
      }
    end
  end
end

local function result_errors(test)
  local errors = {}
  for _, failure in ipairs(test.failures or {}) do
    errors[#errors + 1] = { message = failure }
  end
  if #errors == 0 then
    return nil
  end
  return errors
end

function M.is_test_file(file_path)
  return vim.endswith(file_path, ".test.tlk")
end

M.root = lib.files.match_root_pattern("package.tlk", "package.lock", ".git")

function M.filter_dir(name)
  return name ~= "target" and name ~= ".git"
end

function M.discover_positions(file_path)
  local lines = lib.files.read_lines(file_path)
  local last_line = lines[#lines] or ""
  local positions = {
    {
      type = "file",
      path = file_path,
      name = vim.fn.fnamemodify(file_path, ":t"),
      range = { 0, 0, math.max(#lines - 1, 0), #last_line },
    },
  }

  for lnum, line in ipairs(lines) do
    local name = test_name_on_line(line)
    if name then
      local end_row, end_col = test_end_range(lines, lnum)
      positions[#positions + 1] = {
        type = "test",
        path = file_path,
        name = name,
        range = { lnum - 1, 0, end_row, end_col },
      }
    end
  end

  return lib.positions.parse_tree(positions, { position_id = position_id })
end

function M.build_spec(args)
  local config = current_config
  local position = args.tree:data()
  local command = { config.command, "test", "--json" }
  vim.list_extend(command, config.args)
  vim.list_extend(command, args.extra_args or {})
  table.insert(command, position.path)

  return {
    command = command,
    cwd = args.cwd or config.cwd,
    env = config.env,
    context = {
      path = position.path,
    },
  }
end

function M.results(_, result, tree)
  local ok, lines = pcall(lib.files.read_lines, result.output)
  local raw_output = ok and table.concat(lines, "\n") or ""
  local report = decode_json(raw_output)
  local output_text = report and report.output or raw_output
  local output_path = output_file(output_text ~= "" and output_text or raw_output)
  local results = {}

  if not report then
    results[tree:data().id] = {
      status = ResultStatus.failed,
      output = output_path,
      short = raw_output,
      errors = { { message = "talk test --json did not produce valid JSON" } },
    }
    return results
  end

  if report.status == "error" then
    local message = report.error and report.error.message or "talk test failed"
    results[tree:data().id] = {
      status = ResultStatus.failed,
      output = output_path,
      short = message,
      errors = { { message = message } },
    }
    mark_container_results(tree, results, ResultStatus.failed, output_path, message)
    return results
  end

  if report.status == "no_tests" then
    results[tree:data().id] = {
      status = ResultStatus.skipped,
      output = output_path,
      short = "no .test.tlk files found",
    }
    return results
  end

  mark_container_results(tree, results, ResultStatus.passed, output_path, output_text)

  local nodes_by_name = collect_test_nodes(tree)
  local mapped = false
  local any_failed = false
  for _, test in ipairs(report.tests or {}) do
    local queue = nodes_by_name[test.name]
    local node = queue and table.remove(queue, 1)
    if node then
      mapped = true
      local status = test.status == "failed" and ResultStatus.failed or ResultStatus.passed
      if status == ResultStatus.failed then
        any_failed = true
      end
      local short = table.concat(test.failures or {}, "\n")
      results[node:data().id] = {
        status = status,
        output = output_path,
        short = short ~= "" and short or output_text,
        errors = result_errors(test),
      }
    end
  end

  if any_failed then
    mark_container_results(tree, results, ResultStatus.failed, output_path, output_text)
  elseif not mapped and tree:data().type == "test" then
    results[tree:data().id] = {
      status = (report.failures or 0) > 0 and ResultStatus.failed or ResultStatus.passed,
      output = output_path,
      short = output_text,
    }
  end

  return results
end

setmetatable(M, {
  __call = function(_, opts)
    current_config = adapter_config(opts)
    return M
  end,
})

return M
