if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal autoindent
setlocal indentexpr=GetTalktalkIndent(v:lnum)
setlocal indentkeys=0{,0},0),0],0=else,!^F,o,O

let b:undo_indent = "setlocal autoindent< indentexpr< indentkeys<"

if exists("*GetTalktalkIndent")
  finish
endif

function! GetTalktalkIndent(lnum) abort
  let l:prevnum = prevnonblank(a:lnum - 1)
  if l:prevnum == 0
    return 0
  endif

  let l:sw = shiftwidth()
  if l:sw == 0
    let l:sw = &tabstop
  endif

  let l:prev = s:CodePart(getline(l:prevnum))
  let l:line = s:CodePart(getline(a:lnum))
  let l:ind = indent(l:prevnum)

  let l:opens = s:CountChars(l:prev, '{[(')
  let l:closes = s:CountChars(l:prev, '}])')
  let l:delta = l:opens - l:closes

  if l:delta > 0
    let l:ind += l:delta * l:sw
  elseif l:prev =~# '[{[(]\s*$'
    let l:ind += l:sw
  endif

  let l:leading_closers = matchstr(l:line, '^\s*\zs[]})]\+')
  if !empty(l:leading_closers)
    let l:ind -= strlen(l:leading_closers) * l:sw
  endif

  return max([l:ind, 0])
endfunction

function! s:CodePart(line) abort
  let l:out = ''
  let l:in_string = v:false
  let l:escaped = v:false
  let l:i = 0

  while l:i < strlen(a:line)
    let l:ch = a:line[l:i]
    let l:next = l:i + 1 < strlen(a:line) ? a:line[l:i + 1] : ''

    if l:in_string
      if l:escaped
        let l:escaped = v:false
      elseif l:ch ==# '\\'
        let l:escaped = v:true
      elseif l:ch ==# '"'
        let l:in_string = v:false
      endif
      let l:out .= ' '
    else
      if l:ch ==# '/' && l:next ==# '/'
        break
      elseif l:ch ==# '"'
        let l:in_string = v:true
        let l:out .= ' '
      else
        let l:out .= l:ch
      endif
    endif

    let l:i += 1
  endwhile

  return l:out
endfunction

function! s:CountChars(text, chars) abort
  let l:count = 0
  for l:char in split(a:text, '\zs')
    if stridx(a:chars, l:char) >= 0
      let l:count += 1
    endif
  endfor
  return l:count
endfunction
