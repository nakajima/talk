# Custom commands

`talk` supports Git-style external subcommands. When a command is not built in,
`talk NAME ARGS...` searches `PATH` for `talk-NAME` and runs it with `ARGS...`.
Standard input, output, and error are inherited, and `talk` exits with the
external command's status.

For example, an executable named `talk-report` in `PATH` is available as:

```sh
talk report --format json
```

Built-in commands always take precedence over external executables.
