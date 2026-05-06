# Install & getting started

how to get it running locally

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
2. **Run the REPL** with `talk repl`. It's the fastest way to try expressions and see inferred types.
3. **Read the tour** above for the feature set, or **read "how it works"** for the compiler internals.
4. **File a bug** when you hit one. Most of this is new code and there are edges that haven't been found yet.
