# Install & getting started

three minutes, tops

```terminal
$ brew install talktalk/tap/talk
$ talk --version
talktalk 0.1.1 (interpreter, debug)

$ echo 'print("hi")' > hi.tlk
$ talk run hi.tlk
hi

$ talk --help
  run <file>     run a .tlk file
  lower <file>   print the lowered IR
  fmt <file>     format in place
  repl           a friend you can talk to
```

---

1. **Install the binary.** Homebrew on macOS, a prebuilt binary for Linux, or build from source with `cargo install --path .`
2. **Run the REPL.** `talk repl`. It's low-key my favorite part.
3. **Read the tour** above. Most of what the language does is covered in under five minutes.
4. **Open the docs** for reference: language spec, pipeline internals, effects, and (eventually) a standard library.
5. **File a bug** when something breaks. It will. That's how learning happens.
