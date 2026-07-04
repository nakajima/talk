use talk::compiling::driver::DriverConfig;

#[cfg(feature = "cli")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use clap::{Args, CommandFactory, Parser, Subcommand, ValueHint};
    use clap_complete::{Shell, generate};

    /// Simple program to greet a person
    #[derive(Parser, Debug)]
    #[command(version, about, long_about = None)]
    struct Cli {
        #[command(subcommand)]
        command: Commands,
    }

    #[derive(Subcommand, Debug)]
    enum Commands {
        /// Show a parse tree of the input.
        Parse {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// Show the λ_G program produced by lowering ().
        Lower {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// Show the VM bytecode for the input: chunks,
        /// registers, instructions.
        Ir {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// Show the raw scheduled VM bytecode module for the input
        Bytecode {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// The Type at a position (byte offset, or 1-based
        /// line/column).
        Hover {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
            #[arg(long, value_name = "N")]
            byte_offset: Option<u32>,
            #[arg(long, value_name = "N")]
            line: Option<u32>,
            #[arg(long, value_name = "N")]
            column: Option<u32>,
            #[arg(long, value_name = "ID")]
            node_id: Option<String>,
        },
        /// Formats the input to stdout
        Format {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
            #[arg(long)]
            width: Option<usize>,
        },
        /// Syntax highlight the input as HTML
        Html {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: Option<String>,
        },
        /// Type-check the input
        Check {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long)]
            json: bool,
        },
        /// Run the input
        Run {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
        },
        /// Compile Talk source to bytecode or a standalone executable.
        Build(BuildArgs),
        /// Run a serialized Talk bytecode image.
        RunBytecode {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: String,
        },
        /// Read-eval-print-loop
        Repl,
        /// Print a dense Talk language reference for LLMs.
        Llm,
        /// Generate shell completions
        Completions {
            #[arg(value_enum)]
            shell: Shell,
        },
        /// Install editor support files.
        Setup {
            #[command(subcommand)]
            target: SetupTarget,
        },
        /// Language? Server. Protocol!
        Lsp(LspArgs),
    }

    #[derive(Subcommand, Debug)]
    enum SetupTarget {
        /// Install plain Neovim runtime support files.
        #[command(name = "nvim")]
        Nvim(NvimSetupArgs),
    }

    #[derive(Debug, Args)]
    struct NvimSetupArgs {
        /// Overwrite existing TalkTalk runtime files if they differ.
        #[arg(long)]
        force: bool,
        /// Install into this runtime root instead of Neovim's data/site dir.
        #[arg(long, value_hint = ValueHint::DirPath)]
        target_dir: Option<std::path::PathBuf>,
    }

    #[derive(Debug, Args)]
    struct BuildArgs {
        #[arg(value_hint = ValueHint::FilePath)]
        filenames: Vec<String>,
        #[arg(short, long, value_hint = ValueHint::FilePath)]
        output: String,
        #[arg(long)]
        emit_bytecode: bool,
        #[arg(long, value_hint = ValueHint::FilePath)]
        runtime: Option<String>,
        #[arg(long)]
        cc: Option<String>,
        #[arg(long)]
        keep_temps: bool,
        #[arg(long)]
        no_strip: bool,
    }

    #[derive(Debug, Args)]
    struct LspArgs {
        #[arg(long)]
        stdio: bool,
    }

    let cli = Cli::parse();

    // You can check for the existence of subcommands, and if found use their
    // matches just as you would the top level cmd
    match &cli.command {
        Commands::Parse { filename } => {
            use talk::compiling::driver::Driver;

            let (module_name, source) = single_source_for(filename.as_deref());
            let driver = Driver::new(vec![source], DriverConfig::new(module_name));
            match driver.parse() {
                Ok(parsed) => println!("{:#?}", parsed.phase.asts),
                Err(err) => {
                    eprintln!("failed to parse: {err:?}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Lower { filename } => {
            let (module_name, source) = single_source_for(filename.as_deref());
            let styles = talk::lambda_g::print::Styles::auto();
            match talk::compiling::driver::render_lowered_from(&module_name, source, &styles) {
                Ok(ir) => println!("{ir}"),
                Err(message) => {
                    eprintln!("{message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Ir { filename } => {
            let (module_name, source) = single_source_for(filename.as_deref());
            let styles = talk::lambda_g::print::Styles::auto();
            match talk::compiling::driver::render_bytecode_from(&module_name, source, &styles) {
                Ok(listing) => println!("{listing}"),
                Err(message) => {
                    eprintln!("{message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Bytecode { filename } => {
            let (module_name, source) = single_source_for(filename.as_deref());
            match talk::compiling::driver::render_raw_bytecode_from(&module_name, source) {
                Ok(listing) => println!("{listing}"),
                Err(message) => {
                    eprintln!("{message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Hover {
            filename,
            byte_offset,
            line,
            column,
            node_id,
        } => {
            use talk::analysis::{DocumentInput, Workspace, hover_at};

            let (module_name, text) = match filename.as_deref() {
                Some(name) if name != "-" => match std::fs::read_to_string(name) {
                    Ok(text) => (name.to_string(), text),
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                },
                _ => (STDIN_NAME.to_string(), read_stdin()),
            };
            let doc_id = module_name.clone();
            let doc = DocumentInput {
                id: doc_id.clone(),
                path: module_name,
                version: 0,
                text: text.clone(),
            };
            let Some(workspace) = Workspace::new(vec![doc]) else {
                eprintln!("error: failed to build workspace");
                std::process::exit(1);
            };
            let hover = match (byte_offset, line, column, node_id) {
                (_, _, _, Some(node_id)) => {
                    let Some(node_id) = talk::analysis::hover::parse_node_id(node_id) else {
                        eprintln!("error: node id must be \"index\" or \"file:index\"");
                        std::process::exit(1);
                    };
                    talk::analysis::hover::hover_for_node_id(&workspace, &doc_id, node_id)
                }
                (Some(offset), None, None, None) => hover_at(&workspace, &doc_id, *offset),
                (None, Some(line), Some(column), None) => {
                    match talk::common::text::byte_offset_for_line_column_utf8(
                        &text, *line, *column,
                    ) {
                        Some(offset) => hover_at(&workspace, &doc_id, offset),
                        None => {
                            eprintln!("error: line/column is past end of document");
                            std::process::exit(1);
                        }
                    }
                }
                _ => {
                    eprintln!("error: provide --byte-offset, --line and --column, or --node-id");
                    std::process::exit(1);
                }
            };
            match hover {
                Some(hover) => println!("{}", hover.contents),
                None => {
                    eprintln!("no hover information at that position");
                    std::process::exit(1);
                }
            }
        }
        Commands::Lsp(_) => {
            talk::lsp::server::start().await;
        }
        Commands::Setup { target } => {
            let result = match target {
                SetupTarget::Nvim(args) => {
                    NvimRuntimeInstaller::new(args.target_dir.as_deref(), args.force)
                        .and_then(|installer| installer.install())
                }
            };
            if let Err(err) = result {
                eprintln!("error: {err:#}");
                std::process::exit(1);
            }
        }
        Commands::Completions { shell } => {
            let mut cmd = Cli::command();
            let bin_name = cmd.get_name().to_string();
            generate(*shell, &mut cmd, bin_name, &mut std::io::stdout());
        }
        Commands::Repl => {
            talk::cli::repl::run();
        }
        Commands::Llm => {
            println!("{LLM_REFERENCE}");
        }
        Commands::RunBytecode { filename } => {
            let bytes = match std::fs::read(filename) {
                Ok(bytes) => bytes,
                Err(err) => {
                    eprintln!("error: {err}");
                    std::process::exit(1);
                }
            };
            let module = match talk::vm::Module::decode_bytecode(&bytes) {
                Ok(module) => module,
                Err(err) => {
                    eprintln!("error: {err}");
                    std::process::exit(1);
                }
            };
            let mut io = talk::vm::io::StdioIO;
            match talk::vm::interp::run(&module, &mut io) {
                Ok(talk::vm::interp::Value::Void) => {}
                Ok(value) => println!("{value:?}"),
                Err(err) => {
                    eprintln!("{err}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Build(args) => {
            let module_name = args
                .filenames
                .first()
                .cloned()
                .unwrap_or_else(|| STDIN_NAME.to_string());
            let sources = sources_for_filenames(&args.filenames);
            let bytecode =
                match talk::compiling::driver::compile_bytecode_sources(&module_name, sources) {
                    Ok(bytecode) => bytecode,
                    Err(err) => {
                        eprintln!("{err}");
                        std::process::exit(1);
                    }
                };
            if args.emit_bytecode {
                if let Err(err) = std::fs::write(&args.output, &bytecode) {
                    eprintln!("error: {err}");
                    std::process::exit(1);
                }
            } else if let Err(err) = build_static_executable(
                &bytecode,
                std::path::Path::new(&args.output),
                args.runtime.as_deref(),
                args.cc.as_deref(),
                args.keep_temps,
                !args.no_strip,
            ) {
                eprintln!("error: {err}");
                std::process::exit(1);
            }
        }
        Commands::Run { filenames } => {
            use talk::compiling::driver::Driver;

            let module_name = filenames
                .first()
                .cloned()
                .unwrap_or_else(|| STDIN_NAME.to_string());
            let sources = sources_for_filenames(filenames);
            let driver = Driver::new(sources, DriverConfig::new(module_name));
            let parsed = match driver.parse() {
                Ok(parsed) => parsed,
                Err(err) => {
                    eprintln!("error: {err:?}");
                    std::process::exit(1);
                }
            };
            let resolved = match parsed.resolve_names() {
                Ok(resolved) => resolved,
                Err(err) => {
                    eprintln!("error: {err:?}");
                    std::process::exit(1);
                }
            };
            let typed = resolved.type_check();
            if typed.has_errors() {
                for diagnostic in typed.diagnostics() {
                    eprintln!("{diagnostic:?}");
                }
                std::process::exit(1);
            }
            let mut lowered = typed.lower();
            if !lowered.phase.diagnostics.is_empty() {
                for diagnostic in &lowered.phase.diagnostics {
                    eprintln!("{diagnostic}");
                }
                std::process::exit(1);
            }
            match lowered.run_vm() {
                Ok(talk::vm::interp::Value::Void) => {}
                Ok(value) => println!("{value:?}"),
                Err(err) => {
                    eprintln!("{err}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Check { filenames, json } => {
            use talk::{
                analysis::{DocumentInput, Workspace},
                cli::diagnostics::{ColorMode, render_json_entry, render_json_output, render_text},
            };

            let sources = sources_for_filenames(filenames);
            let mut docs = Vec::with_capacity(sources.len());
            for source in sources {
                let path = source.path().to_string();
                let text = match source.read() {
                    Ok(text) => text,
                    Err(err) => {
                        eprintln!("failed to read {path}: {err:?}");
                        std::process::exit(1);
                    }
                };
                docs.push(DocumentInput {
                    id: path.clone(),
                    path,
                    version: 0,
                    text,
                });
            }

            let Some(workspace) = Workspace::new(docs) else {
                return;
            };

            let mut doc_ids: Vec<_> = workspace.diagnostics.keys().cloned().collect();
            doc_ids.sort();

            let mut has_errors = false;
            let mut json_entries = Vec::new();
            for doc_id in doc_ids {
                let text = workspace.text_for(&doc_id).unwrap_or("");
                if let Some(diagnostics) = workspace.diagnostics.get(&doc_id) {
                    for diagnostic in diagnostics {
                        if *json {
                            json_entries.push(render_json_entry(&doc_id, text, diagnostic));
                        } else {
                            print!(
                                "{}",
                                render_text(&doc_id, text, diagnostic, ColorMode::Auto)
                            );
                        }
                        // Warnings print but don't fail the check.
                        has_errors |=
                            diagnostic.severity == talk::analysis::DiagnosticSeverity::Error;
                    }
                }
            }

            if *json {
                println!("{}", render_json_output(&json_entries));
            }

            if has_errors {
                std::process::exit(1);
            }
        }
        Commands::Html { filename } => {
            init();
            use talk::highlighter::highlight_html;

            let source = input_text(filename.as_deref());
            let html = highlight_html(&source);
            println!("{html}");
        }
        Commands::Format { filename, width } => {
            use talk::formatter;

            init();
            let source = input_text(filename.as_deref());
            println!(
                "{}",
                formatter::format_string_with_width(&source, width.unwrap_or(80))
            );
        }
    }
}

#[cfg(feature = "cli")]
const STDIN_NAME: &str = "<stdin>";

#[cfg(feature = "cli")]
const LLM_REFERENCE: &str = r#"# Talk language reference for LLMs

Talk is a statically typed, Swift-flavored language with local type inference, generics, protocols, algebraic effects, value-semantics aggregates, and a bytecode VM backend. Files normally use `.tlk`; core library files live in `core/` and are implicitly imported unless a file starts with `// no-core`.

## CLI

    talk run [files...]       parse, resolve, typecheck, lower, and run; no file reads stdin
    talk check [--json] files typecheck and print diagnostics
    talk repl                 interactive declarations and expressions
    talk format [file]        format source from file or stdin
    talk hover file --line N --column N | --byte-offset N | --node-id ID
    talk lower file           print lowered lambda-G IR
    talk ir file              print scheduled VM bytecode listing
    talk bytecode file        print raw bytecode module
    talk html/debug/parse     development views
    talk lsp --stdio          language server
    talk setup nvim           install Neovim runtime support files
    talk completions SHELL    shell completion script
    talk llm                  print this reference

## Lexical and module basics

Comments are `//` line comments. Identifiers are ordinary words; type names are conventionally upper camel case. Semicolons are not used. Blocks are `{ ... }`. Top-level declarations may be prefixed with `public` to export them. Imports are explicit: `use { Foo, bar } from ./path.tlk`, `use { Foo: LocalFoo } from ./path.tlk`, `use _ from ./path.tlk`, or package-style `use { Foo } from package`.

## Declarations

    public let name: Type = expr
    func f<T>(x: T, y: Int) -> Result { body }
    struct Point {
        let x: Int
        let y: Int
        init(x: Int, y: Int) { self.x = x; self.y = y; self }
    }
    enum Optional<T> { case some(T) case none }
    protocol P { associated type Element func next() -> Element? }
    extend Type: P { typealias Element = Int func next() -> Int? { ... } }
    extend Type { func method() -> R { ... } static func make() -> Type { ... } }
    typealias Name = Type
    effect 'name(payload: Type) -> ReturnType

Function result annotations are optional when inferable. `init` bodies assign `self.field` and return `self`. Methods have implicit `self`; do not declare a self parameter. Receiver modes: plain `func` reads a shared value, `mut func` may update `self` and writes the receiver back at the call site, `consuming func` takes ownership. `static func` is called on the type/protocol namespace.

## Expressions and control flow

Literals: integers, floats, strings, `true`, `false`, arrays `[a, b]`, closures `func(x: Int) -> Int { x + 1 }`. Calls use labels only through ordinary parameter order: `f(a, b)`. Constructors look like calls: `Point(x: 1, y: 2)`, enum cases may be qualified or inferred: `Optional<Int>.some(1)` or `.some(1)`. Field/member access is `value.field` and `value.method(args)`. Generic arguments may be explicit: `id<Int>(1)`.

Bindings and mutation: `let x = expr`; assignment is `x = expr` or `self.field = expr`. `let` variables are mutable by assignment in current Talk. Type ascription is `let x: Type = expr`.

Blocks are expressions. `if cond { a } else { b }` is an expression; branches must agree. `loop { ... }` loops forever until `break`; `loop condition { ... }` is while-like. `break`, `continue`, and `return expr` are supported. `for x in iterable { ... }` uses the iterable/iterator protocols.

Pattern matching:

    match expr {
        .caseName(payload) -> result,
        .none -> other,
        0 -> zero,
        _ -> fallback
    }

Patterns can bind enum payloads. GADT-style enum cases may refine the result type, e.g. `case int(Int) -> Expr<Int>`.

Trailing block syntax passes a final closure argument: `f { body }` is `f(func() { body })`.

## Types

Builtin scalar/value types include `Int`, `Float`, `Bool`, `Byte`, `RawPtr`, `Void`/`()`, and `Never`. Core nominal types include `String`, `Substring`, `Array<T>`, and `Optional<T>`; `T?` is syntax for optional. Function types are `(A, B) -> R`; effectful functions write effects before the arrow, e.g. `(A) 'io -> R` or `func read() 'io -> Int`. Borrow types use `&T` and exclusive borrows use `&mut T`. Protocol existential types use `any P`; associated type constraints use `any Iterator<Element = Int>`. Protocol composition in constraints uses `&`; where clauses and qualified predicates are supported internally and in declarations where implemented.

Generics are written with angle brackets: `func id<T>(x: T) -> T`. Simple bounds use `T: Protocol`; associated types use `associated type Name` in protocols and `typealias Name = Type` in conforming extensions. Protocol requirements can include funcs, mut/consuming funcs, static funcs, associated types, and defaults in extensions.

## Operators and builtins

Common operators are library-backed or builtin-resolved: arithmetic `+ - * /`, comparison `== != < <= > >=`, boolean values, string concatenation via `+`, member calls, and casts/ascriptions using `as` for protocol existentials where supported. `print(x)` prints Showable-ish values; `sleep(ms)` and I/O live in core effects. The core library defines protocols such as `Showable`, `Add`, `Equatable`, `Iterable`, `Iterator`, `From`, `Into`, `Borrowed`, and `Owner`.

Low-level trusted IR escapes use `@_ir(args...) { ... }` and appear mainly in core. Operations include integer/float math, comparisons, `alloc`, `load`, `store`, `gep`, `copy`, and I/O shims. The type checker trusts the surrounding Talk type; keep `_ir` isolated.

## Effects

Effects are named with a leading tick: `effect 'throws(error: String) -> Never`. Calling an effect is expression syntax: `'throws("bad")`. Effect rows appear on functions before `->`: `func f() 'throws -> ()`. Handlers use `@handle 'effect { payload in body }` for abortive handling and handler forms can resume when the effect return type is not `Never`. Handlers are statically routed by name resolution/lowering rather than dynamically searched by the VM.

## Memory and value model

Source-level structs, enums, arrays, strings, records, and function values have value semantics. Struct/record updates rebuild values unless stored in a mutable cell; mutable locals/captures lower to cells when needed. Aggregates are represented in the VM as boxed handles; scalars are unboxed. Raw memory exists only through `RawPtr` and core `_alloc`, `_load`, `_store`, `_copy`, pointer arithmetic, and host I/O intrinsics. `Int` is 64-bit in raw memory; `Float` is 64-bit; `Bool` and `Byte` are one byte; `RawPtr` and boxed handles are pointer-sized. The backend uses copy-on-write-style mutable value semantics for source receivers; `mut func` receiver calls write the new self back to the original place.

Ownership checking is source-near: `&T` borrows, `&mut T` is exclusive, `consuming` moves, and marker protocols like `Owner`/`Borrowed` describe library-level ownership roles. The low-level allocator is an effect (`'alloc`); memory safety around `@_ir` is trusted code responsibility.

## Compiler model

Pipeline: parse -> name resolution/imports -> OutsideIn-style type checking with qualified predicates, protocols, associated types, existentials, and GADT refinements -> lambda-G CPS-like graph IR -> scheduling -> register bytecode VM. Useful inspection commands: `talk check`, `talk hover`, `talk lower`, `talk ir`, and `talk bytecode`.
"#;

#[cfg(feature = "cli")]
const NVIM_RUNTIME_RAW_BASE: &str =
    "https://raw.githubusercontent.com/nakajima/talk/main/dev/editors/nvim";

#[cfg(feature = "cli")]
const NVIM_RUNTIME_FILES: &[&str] = &[
    "ftdetect/talktalk.lua",
    "ftplugin/talktalk.lua",
    "indent/talktalk.vim",
    "syntax/talktalk.vim",
];

#[cfg(feature = "cli")]
struct NvimRuntimeInstaller {
    target_root: std::path::PathBuf,
    force: bool,
}

#[cfg(feature = "cli")]
impl NvimRuntimeInstaller {
    fn new(target_dir: Option<&std::path::Path>, force: bool) -> anyhow::Result<Self> {
        let target_root = match target_dir {
            Some(path) => path.to_path_buf(),
            None => Self::default_target_root()?,
        };

        Ok(Self { target_root, force })
    }

    fn install(&self) -> anyhow::Result<()> {
        use anyhow::Context as _;

        println!("Installing TalkTalk Neovim runtime files from github.com/nakajima/talk");
        println!("Target runtime root: {}", self.target_root.display());

        let mut downloads = Vec::with_capacity(NVIM_RUNTIME_FILES.len());
        for relative_path in NVIM_RUNTIME_FILES {
            let contents = Self::download_file(relative_path)?;
            downloads.push((*relative_path, contents));
        }

        for (relative_path, contents) in &downloads {
            let target = self.target_root.join(*relative_path);
            if target.exists() && !self.force {
                let existing = std::fs::read(&target)
                    .with_context(|| format!("failed to read {}", target.display()))?;
                if existing.as_slice() != contents.as_slice() {
                    anyhow::bail!(
                        "{} already exists and differs; rerun with --force to overwrite",
                        target.display()
                    );
                }
            }
        }

        for (relative_path, contents) in downloads {
            let target = self.target_root.join(relative_path);
            if target.exists() && !self.force {
                println!("up to date: {}", target.display());
                continue;
            }

            if let Some(parent) = target.parent() {
                std::fs::create_dir_all(parent)
                    .with_context(|| format!("failed to create {}", parent.display()))?;
            }
            std::fs::write(&target, contents)
                .with_context(|| format!("failed to write {}", target.display()))?;
            println!("installed: {}", target.display());
        }

        Ok(())
    }

    fn default_target_root() -> anyhow::Result<std::path::PathBuf> {
        if let Some(data_dir) = Self::nvim_data_dir() {
            return Ok(data_dir.join("site"));
        }

        Self::fallback_data_site_dir()
    }

    fn nvim_data_dir() -> Option<std::path::PathBuf> {
        let output = std::process::Command::new("nvim")
            .args([
                "--headless",
                "-u",
                "NONE",
                "-i",
                "NONE",
                "--noplugin",
                "+lua io.write(vim.fn.stdpath('data'))",
                "+qa!",
            ])
            .output()
            .ok()?;

        if !output.status.success() {
            return None;
        }

        let stdout = String::from_utf8(output.stdout).ok()?;
        let path = stdout.trim();
        if path.is_empty() {
            None
        } else {
            Some(std::path::PathBuf::from(path))
        }
    }

    fn fallback_data_site_dir() -> anyhow::Result<std::path::PathBuf> {
        let appname = std::env::var_os("NVIM_APPNAME")
            .filter(|value| !value.as_os_str().is_empty())
            .unwrap_or_else(|| "nvim".into());

        let data_home = match std::env::var_os("XDG_DATA_HOME")
            .filter(|value| !value.as_os_str().is_empty())
        {
            Some(path) => std::path::PathBuf::from(path),
            None => {
                let home = std::env::var_os("HOME").ok_or_else(|| {
                    anyhow::anyhow!("could not find Neovim data dir; set HOME or pass --target-dir")
                })?;
                std::path::PathBuf::from(home).join(".local/share")
            }
        };

        Ok(data_home.join(appname).join("site"))
    }

    fn download_file(relative_path: &str) -> anyhow::Result<Vec<u8>> {
        let url = format!("{NVIM_RUNTIME_RAW_BASE}/{relative_path}");
        Self::download_url(&url)
    }

    fn download_url(url: &str) -> anyhow::Result<Vec<u8>> {
        let attempts = [
            ("curl", vec!["-fsSL", url]),
            ("wget", vec!["-qO-", url]),
            ("fetch", vec!["-qo", "-", url]),
        ];
        let mut failures = Vec::new();

        for (program, args) in attempts {
            match std::process::Command::new(program).args(args).output() {
                Ok(output) if output.status.success() => return Ok(output.stdout),
                Ok(output) => {
                    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
                    if stderr.is_empty() {
                        failures.push(format!("{program} exited with {}", output.status));
                    } else {
                        failures.push(format!("{program} exited with {}: {stderr}", output.status));
                    }
                }
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
                Err(err) => failures.push(format!("{program}: {err}")),
            }
        }

        if failures.is_empty() {
            anyhow::bail!("could not download {url}; install curl, wget, or fetch");
        }

        anyhow::bail!(
            "could not download {url}; install curl, wget, or fetch; attempts failed: {}",
            failures.join("; ")
        );
    }
}

#[cfg(feature = "cli")]
fn build_static_executable(
    bytecode: &[u8],
    output: &std::path::Path,
    runtime: Option<&str>,
    cc: Option<&str>,
    keep_temps: bool,
    strip: bool,
) -> Result<(), String> {
    let runtime = match runtime {
        Some(path) => std::path::PathBuf::from(path),
        None => RuntimeArchive::locate()?,
    };
    let temp = BuildTemp::new(output)?;
    temp.write_launcher(bytecode)?;
    let compiler = cc.unwrap_or("cc");
    let status = std::process::Command::new(compiler)
        .arg(temp.launcher())
        .arg(&runtime)
        .arg("-o")
        .arg(output)
        .status()
        .map_err(|err| format!("failed to run {compiler}: {err}"))?;
    if !status.success() {
        return Err(format!("{compiler} failed with status {status}"));
    }
    if strip {
        Strip::run(output)?;
    }
    if !keep_temps {
        temp.clean()?;
    } else {
        eprintln!("kept temporary build files in {}", temp.dir().display());
    }
    Ok(())
}

#[cfg(feature = "cli")]
struct Strip;

#[cfg(feature = "cli")]
impl Strip {
    fn run(output: &std::path::Path) -> Result<(), String> {
        match std::process::Command::new("strip").arg(output).status() {
            Ok(status) if status.success() => Ok(()),
            Ok(status) => Err(format!(
                "strip failed with status {status}; pass --no-strip to keep the unstripped executable"
            )),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(err) => Err(format!("failed to run strip: {err}")),
        }
    }
}

#[cfg(feature = "cli")]
struct RuntimeArchive;

#[cfg(feature = "cli")]
impl RuntimeArchive {
    fn locate() -> Result<std::path::PathBuf, String> {
        let mut candidates = Vec::new();
        if let Ok(exe) = std::env::current_exe()
            && let Some(dir) = exe.parent()
        {
            if let Some(profile_dir) = dir.parent() {
                candidates.push(profile_dir.join("release/libtalk_static.a"));
            }
            candidates.push(dir.join("libtalk_static.a"));
            candidates.push(dir.join("../lib/libtalk_static.a"));
            if let Some(profile_dir) = dir.parent() {
                candidates.push(profile_dir.join("debug/libtalk_static.a"));
            }
        }
        candidates.push(std::path::PathBuf::from("target/release/libtalk_static.a"));
        candidates.push(std::path::PathBuf::from("target/debug/libtalk_static.a"));

        for candidate in candidates {
            if candidate.exists() {
                return Ok(candidate);
            }
        }
        Err(
            "could not find libtalk_static.a; run `cargo build -p talk-static` or pass --runtime"
                .into(),
        )
    }
}

#[cfg(feature = "cli")]
struct BuildTemp {
    dir: std::path::PathBuf,
    launcher: std::path::PathBuf,
}

#[cfg(feature = "cli")]
impl BuildTemp {
    fn new(output: &std::path::Path) -> Result<Self, String> {
        let stem = output
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("talk-build");
        let dir = std::env::temp_dir().join(format!("talk-static-{}-{stem}", std::process::id()));
        std::fs::create_dir_all(&dir).map_err(|err| format!("failed to create temp dir: {err}"))?;
        let launcher = dir.join("main.c");
        Ok(Self { dir, launcher })
    }

    fn dir(&self) -> &std::path::Path {
        &self.dir
    }

    fn launcher(&self) -> &std::path::Path {
        &self.launcher
    }

    fn write_launcher(&self, bytecode: &[u8]) -> Result<(), String> {
        let mut c = String::new();
        c.push_str("#include <stdint.h>\n#include <stddef.h>\n\n");
        c.push_str("extern int talk_runtime_run(const uint8_t *bytes, size_t len);\n\n");
        c.push_str("static const uint8_t TALK_PROGRAM[] = {\n");
        for (i, byte) in bytecode.iter().enumerate() {
            if i % 12 == 0 {
                c.push_str("    ");
            }
            c.push_str(&format!("0x{byte:02x}, "));
            if i % 12 == 11 {
                c.push('\n');
            }
        }
        if !bytecode.len().is_multiple_of(12) {
            c.push('\n');
        }
        c.push_str("};\n\n");
        c.push_str("int main(int argc, char **argv) {\n");
        c.push_str("    (void)argc;\n    (void)argv;\n");
        c.push_str("    return talk_runtime_run(TALK_PROGRAM, sizeof(TALK_PROGRAM));\n");
        c.push_str("}\n");
        std::fs::write(&self.launcher, c).map_err(|err| format!("failed to write launcher: {err}"))
    }

    fn clean(&self) -> Result<(), String> {
        std::fs::remove_dir_all(&self.dir)
            .map_err(|err| format!("failed to remove temp dir: {err}"))
    }
}

#[cfg(feature = "cli")]
fn read_stdin() -> String {
    use std::io::Read;

    let mut buffer = String::new();
    if let Err(err) = std::io::stdin().read_to_string(&mut buffer) {
        eprintln!("failed to read stdin: {err}");
        std::process::exit(1);
    }
    buffer
}

#[cfg(feature = "cli")]
fn single_source_for(filename: Option<&str>) -> (String, talk::compiling::driver::Source) {
    use std::path::PathBuf;
    use talk::compiling::driver::Source;

    let module_name = match filename {
        Some(name) if name != "-" => name.to_string(),
        _ => STDIN_NAME.to_string(),
    };

    let source = match filename {
        Some(name) if name != "-" => Source::from(PathBuf::from(name)),
        _ => Source::in_memory(PathBuf::from(STDIN_NAME), read_stdin()),
    };

    (module_name, source)
}

#[cfg(feature = "cli")]
fn sources_for_filenames(filenames: &[String]) -> Vec<talk::compiling::driver::Source> {
    use std::path::PathBuf;
    use talk::compiling::driver::Source;

    if filenames.is_empty() {
        return vec![Source::in_memory(PathBuf::from(STDIN_NAME), read_stdin())];
    }

    let mut stdin_text = None;
    let mut sources = Vec::with_capacity(filenames.len());
    for filename in filenames {
        if filename == "-" {
            let text = stdin_text.get_or_insert_with(read_stdin);
            sources.push(Source::in_memory(PathBuf::from(STDIN_NAME), text.clone()));
        } else {
            sources.push(Source::from(PathBuf::from(filename)));
        }
    }

    sources
}

#[cfg(feature = "cli")]
fn input_text(filename: Option<&str>) -> String {
    match filename {
        Some(name) if name != "-" => match std::fs::read_to_string(name) {
            Ok(text) => text,
            Err(err) => {
                eprintln!("failed to read {name}: {err}");
                std::process::exit(1);
            }
        },
        _ => read_stdin(),
    }
}

#[cfg(not(feature = "cli"))]
fn main() {
    eprintln!("talk was compiled without the 'cli' feature");
    std::process::exit(1);
}

pub fn init() {
    use tracing_subscriber::{EnvFilter, prelude::*, registry};
    let tree = tracing_tree::HierarchicalLayer::new(2).with_filter(EnvFilter::from_default_env()); // ordinary RUST_LOG filtering
    registry().with(tree).init();
}
