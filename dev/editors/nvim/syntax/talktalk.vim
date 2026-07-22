if exists("b:current_syntax")
  finish
endif

syntax case match

syntax keyword talktalkControl if else loop for in match return break continue
syntax keyword talktalkDeclaration func let init struct enum case protocol extend associated typealias effect import use from where
syntax keyword talktalkModifier public linear static mut consuming any as handling
syntax keyword talktalkBoolean true false

syntax match talktalkAttribute "@[A-Za-z0-9_][A-Za-z0-9_]*"
syntax match talktalkEffect "'[A-Za-z0-9_][A-Za-z0-9_]*"
syntax match talktalkBoundVar "\$[A-Za-z0-9_][A-Za-z0-9_]*"
syntax match talktalkIRRegister "%[0-9?][0-9?]*"

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

syntax match talktalkEscape "\\\(n\|t\|r\|\"\|'\|\\\|u{[0-9A-Fa-f]\{1,6}}\)" contained
syntax match talktalkCharacter #\'\%([^\'\\\r\n]\|\\\%([ntr"\'\\]\|u{[0-9A-Fa-f]\{1,6}}\)\)\+\'# contains=talktalkEscape
syntax region talktalkString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=talktalkEscape

syntax match talktalkComment "//.*$" contains=@Spell

highlight default link talktalkControl Keyword
highlight default link talktalkDeclaration Keyword
highlight default link talktalkModifier StorageClass
highlight default link talktalkBoolean Boolean
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
highlight default link talktalkCharacter Character
highlight default link talktalkString String
highlight default link talktalkComment Comment

syntax sync minlines=50

let b:current_syntax = "talktalk"
