if exists("b:current_syntax")
  finish
endif

syntax case match

syntax keyword talktalkControl if else loop for in match return break continue unreachable
syntax keyword talktalkDeclaration func let init struct enum case protocol extend associated typealias effect import use macro where
syntax keyword talktalkModifier pub public linear static mut consuming any as handling
syntax keyword talktalkBoolean true false

syntax match talktalkType "\<[A-Z][A-Za-z0-9_]*\>"
syntax match talktalkFunction "\<[a-z_][A-Za-z0-9_]*\ze\s*("
syntax match talktalkEnumMember "\.\zs[A-Za-z_][A-Za-z0-9_]*\>"

syntax match talktalkNumber "\<\d\%(\d\|_\)*\%(\.\d\%(\d\|_\)*\)\?\>"

syntax match talktalkOperator "\V->"
syntax match talktalkOperator "\V=="
syntax match talktalkOperator "\V!="
syntax match talktalkOperator "\V<="
syntax match talktalkOperator "\V>="
syntax match talktalkOperator "\V+="
syntax match talktalkOperator "\V-="
syntax match talktalkOperator "\V*="
syntax match talktalkOperator "\V/="
syntax match talktalkOperator "\V&&"
syntax match talktalkOperator "\V||"
syntax match talktalkOperator "\V&="
syntax match talktalkOperator "\V^="
syntax match talktalkOperator "\V~="
syntax match talktalkOperator "\V::"
syntax match talktalkOperator "\V..."
syntax match talktalkOperator "\V.."
syntax match talktalkOperator "[-+*/%=!<>~^|&?:.]"

" Sigil forms come after the operators so they win the same-position tie
" against single-character operator matches (e.g. `%` modulo vs `%1`).
syntax match talktalkAttribute "@[A-Za-z0-9_][A-Za-z0-9_]*"
syntax match talktalkBoundVar "\$[A-Za-z0-9_][A-Za-z0-9_]*"
syntax match talktalkIRRegister "%[0-9?][0-9?]*"
syntax match talktalkQuotedIdentifier '#"[^"\\]\+"'
" A #[name] declaration wrapper marker (ADR 0026); the bracketed name
" highlights like the @attribute sigil form.
syntax match talktalkWrapperMarker "#\[[A-Za-z0-9_]\+\ze[(\]]"

syntax match talktalkEscape "\\\(n\|t\|r\|\"\|\\\|u{[0-9A-Fa-f]\{1,6}}\)" contained
syntax match talktalkCharEscape "\\\(n\|t\|r\|\"\|'\|\\\|u{[0-9A-Fa-f]\{1,6}}\)" contained
syntax match talktalkCharacter #\'\%([^\'\\\r\n]\|\\\%([ntr"\'\\]\|u{[0-9A-Fa-f]\{1,6}}\)\)\+\'# contains=talktalkCharEscape
" An effect name is a tick-prefixed identifier run NOT closed by a second
" tick; a closed run is a character literal. Defined after talktalkCharacter
" so it wins when both match at the same position (e.g. foo('io, 'x')).
syntax match talktalkEffect "'[A-Za-z0-9_]\+\>'\@!"
syntax region talktalkString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=talktalkEscape

syntax match talktalkComment "//.*$" contains=@Spell

highlight default link talktalkControl Keyword
highlight default link talktalkDeclaration Keyword
highlight default link talktalkModifier StorageClass
highlight default link talktalkBoolean Keyword
highlight default link talktalkAttribute PreProc
highlight default link talktalkEffect Special
highlight default link talktalkBoundVar Identifier
highlight default link talktalkIRRegister Identifier
highlight default link talktalkType Type
highlight default link talktalkFunction Function
highlight default link talktalkEnumMember Constant
highlight default link talktalkNumber Number
highlight default link talktalkOperator Operator
highlight default link talktalkEscape SpecialChar
highlight default link talktalkCharEscape SpecialChar
highlight default link talktalkQuotedIdentifier Identifier
highlight default link talktalkWrapperMarker PreProc
highlight default link talktalkCharacter Character
highlight default link talktalkString String
highlight default link talktalkComment Comment

" Keep LSP semantic token colors consistent with the syntax file above.
highlight default link @lsp.type.modifier.talktalk StorageClass
highlight default link @lsp.type.event.talktalk Special

syntax sync minlines=50

let b:current_syntax = "talktalk"
