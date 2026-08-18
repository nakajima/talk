# 10. Macros

Macros write TalkTalk code for you before the compiler checks the program. Simple macros substitute pieces of syntax into a template. More advanced macros can inspect syntax and build a result. Either way, the generated code is checked like code you wrote yourself.

## Declarative macros

A declarative macro is a balanced token template with `$` parameters:

```tlk
macro choose($condition, $yes, $no) {
	if $condition {
		$yes
	} else {
		$no
	}
}

let result = @choose(true, 1, 2)
result
```

A macro can introduce syntax and control flow that a function cannot:

```tlk
macro unless($condition, $body) {
    if $condition {
        ()
    } else {
        $body
    }
}

let done = false
@unless(done, print("still working"))
```

Rules can overload by arity. Macro invocations use `@name(...)`.

## Hygiene and evaluation

Names written in a template resolve in the macro's definition context. Spliced syntax keeps the caller's context. This prevents a helper binding in a macro from accidentally capturing, or being captured by, an unrelated caller name.

A caller-provided identifier spliced into binder position intentionally exposes the generated declaration. Repeating `$value` repeats its syntax and therefore may repeat evaluation; bind an expression once when that distinction matters.

## Expansion positions

The same invocation form can expand in expression, item, nominal-member, pattern, or type position. The invocation's location determines which grammar parses the result.

`@assert(condition)` is compiler-provided. It preserves the source text of the condition for useful failure messages and is also used by TalkTalk's test files.

## Procedural macros

A package may export a deterministic procedural expression macro from a `*.macro.tlk` service. Such a macro receives one balanced `(...)`, `[...]`, or `{...}` input tree and returns typed syntax. Services use syntax values and `quote { ... }`, run under fixed budgets, and cannot use inline IR or `#unsafe`.

The bundled HTML module is the main example:

```tlk norun
use html::{ html }

let name = "<Ada & friends>"
let page = @html {
    main #content .page {
        h1 { "Hello, " (name) }
        @for number in [1, 2, 3] {
            span { (number) }
        }
    }
}

print(page.into_string())
```

Interpolated values are escaped. The macro checks the markup while compiling and produces ordinary TalkTalk code.

## Further reading

TalkTalk's declarative macros use lexical hygiene: names introduced by a macro do not accidentally capture names at the call site. [Binding as sets of scopes](https://www.cs.utah.edu/plt/scope-sets/) explains the scope-set model that informs modern hygienic macro systems. TalkTalk's typed procedural services are its own constrained design, documented by [ADR 0026](../../docs/adr/0026-macros.md).
