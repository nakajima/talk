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
        /// Rewrite call sites to match declared argument labels (ADR 0041).
        FixLabels {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<std::path::PathBuf>,
            /// Treat the given directory as the core corpus and fix it.
            #[arg(long, value_name = "DIR")]
            core: Option<std::path::PathBuf>,
            /// Fix each file as its own standalone program.
            #[arg(long)]
            each: bool,
        },
        /// Compile and execute the input (or the current package's binary
        /// when no filenames are given inside a package).
        Run {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            /// Execute this zero-parameter public function instead of the
            /// script's top-level statements.
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
            /// Select the package binary to run.
            #[arg(long, value_name = "NAME")]
            bin: Option<String>,
            /// Use only locally installed package sources.
            #[arg(long)]
            offline: bool,
        },
        /// Discover and execute `.test.tlk` Talk tests.
        Test {
            #[arg(value_hint = ValueHint::FilePath)]
            paths: Vec<String>,
            #[arg(long)]
            json: bool,
            /// Run only the test with this exact name.
            #[arg(long, value_name = "NAME")]
            filter: Option<String>,
        },
        /// Compile the input to a bytecode image.
        Build {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            /// Where to write the image, or the executable with --native.
            #[arg(short, long, value_name = "FILE")]
            output: String,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
            /// Compile ahead of time to a native executable through C
            /// instead of writing a bytecode image.
            #[arg(long)]
            native: bool,
            /// The C compiler to drive (default: $CC, else `cc`; with
            /// --target, `zig cc`).
            #[arg(long, value_name = "PROGRAM")]
            cc: Option<String>,
            /// Cross-compile for this target triple, which needs `zig`
            /// on PATH (for example aarch64-linux-musl).
            #[arg(long, value_name = "TRIPLE")]
            target: Option<String>,
            /// Extra arguments for the C compiler, after the defaults.
            #[arg(long = "cflag", value_name = "FLAG")]
            cflags: Vec<String>,
            /// Keep the generated C beside the executable.
            #[arg(long)]
            keep_c: bool,
        },
        /// Regenerate a service artifact and its manifest from a source
        /// directory, requiring the stage-1/stage-2 fixed point (ADR
        /// 0043). With no directory, regenerates the self-hosted
        /// frontend artifact (bootstrap/frontend.tbc) from stdlib/syntax/
        /// in the current directory. With --check, verifies the on-disk
        /// artifact and manifest are current instead of writing.
        Bootstrap {
            /// Directory of .tlk sources (non-recursive); omit for the
            /// frontend profile.
            #[arg(value_hint = ValueHint::DirPath)]
            dir: Option<String>,
            /// Where to write the artifact; the manifest lands beside
            /// it. Required with an explicit source directory.
            #[arg(short, long, value_name = "FILE")]
            output: Option<String>,
            /// Exported function names (repeatable).
            #[arg(long = "export", value_name = "NAME")]
            exports: Vec<String>,
            /// Effects the exports may perform (repeatable; default none).
            #[arg(long = "allow-effect", value_name = "EFFECT")]
            allow_effects: Vec<String>,
            /// Verify the existing artifact and manifest instead of writing.
            #[arg(long)]
            check: bool,
        },
        /// Validate and execute a bytecode image.
        RunImage {
            #[arg(value_hint = ValueHint::FilePath)]
            filename: String,
        },
        /// Render the bytecode compiled from the input.
        Bytecode {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
        },
        /// Emit C source for the input (the ahead-of-time target).
        C {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
        },
        /// Render the backend's middle representation for the input.
        Mir {
            #[arg(value_hint = ValueHint::FilePath)]
            filenames: Vec<String>,
            #[arg(long, value_name = "NAME")]
            entry: Option<String>,
        },
        /// Create a new package directory.
        New {
            #[arg(value_hint = ValueHint::DirPath)]
            name: String,
        },
        /// Install package dependencies in the current directory.
        Install {
            #[arg(long)]
            offline: bool,
        },
        /// Refresh the package lockfile in the current directory.
        Update {
            packages: Vec<String>,
            #[arg(long)]
            offline: bool,
        },
        /// Interactive frontend for declarations, type queries, and completion.
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
        Commands::New { name } => {
            let valid_name = matches!(
                std::path::Path::new(name).components().next(),
                Some(std::path::Component::Normal(_))
            ) && std::path::Path::new(name).components().count() == 1;
            if !valid_name {
                eprintln!("error: package name must be one directory name, not a path");
                std::process::exit(1);
            }
            let parent = match std::env::current_dir() {
                Ok(parent) => parent,
                Err(err) => {
                    eprintln!("error: failed to determine the current directory: {err}");
                    std::process::exit(1);
                }
            };
            let root = parent.join(name);
            match talk::compiling::package::PackageProject::create_executable_at(
                &root, name, "0.1.0", "main",
            ) {
                Ok(()) => println!("created package {}", root.display()),
                Err(err) => {
                    eprintln!("error: {err}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Install { offline } => match install_current_package(*offline, false) {
            Ok(_) => println!("installed package dependencies"),
            Err(err) => {
                eprintln!("error: {err}");
                std::process::exit(1);
            }
        },
        Commands::Update { packages, offline } => {
            match update_current_package(*offline, packages) {
                Ok(_) => println!("updated package dependencies"),
                Err(err) => {
                    eprintln!("error: {err}");
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
        Commands::FixLabels {
            filenames,
            core,
            each,
        } => match talk::cli::fix_labels::run(core.as_deref(), filenames, *each) {
            Ok(applied) => println!("applied {applied} label fixes"),
            Err(err) => {
                eprintln!("{err}");
                std::process::exit(1);
            }
        },
        Commands::Run {
            filenames,
            entry,
            bin,
            offline,
        } => {
            use talk::compiling::driver::{Driver, DriverConfig, execute_module};

            if *offline
                && (filenames.is_empty()
                    && !talk::compiling::package::PackageProject::exists_at(std::path::Path::new(
                        ".",
                    )))
            {
                eprintln!("error: --offline requires package execution");
                std::process::exit(1);
            }
            if filenames.is_empty()
                && talk::compiling::package::PackageProject::exists_at(std::path::Path::new("."))
            {
                let project = match talk::compiling::package::PackageProject::open_at(
                    std::path::PathBuf::from("."),
                    *offline,
                ) {
                    Ok(project) => project,
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                };
                let executable =
                    match project.compile_binary_entry(bin.as_deref(), entry.as_deref()) {
                        Ok(executable) => executable,
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    };
                let mut io = talk_runtime::io::StdioIO;
                match execute_module(&executable, &mut io) {
                    Ok(Some(rendered)) => println!("{rendered}"),
                    Ok(None) => {}
                    Err(message) => {
                        eprintln!("error: {message}");
                        std::process::exit(1);
                    }
                }
                return;
            }

            let sources = sources_for_filenames(filenames);
            let driver = Driver::new(sources, DriverConfig::new("Main"));
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
                    eprintln!("{diagnostic}");
                }
                std::process::exit(1);
            }

            let module = match typed.compile_executable(entry.as_deref()) {
                Ok(module) => module,
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            };
            let mut io = talk_runtime::io::StdioIO;
            match execute_module(&module, &mut io) {
                Ok(Some(rendered)) => println!("{rendered}"),
                Ok(None) => {}
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Test {
            paths,
            json,
            filter,
        } => {
            // A path argument names the project under test: anchor at its
            // enclosing package root (walking up from the first path), so
            // `package::` imports resolve the same from anywhere. With no
            // paths, the current directory is the project as before.
            let project_root = paths
                .first()
                .and_then(talk::compiling::package::PackageProject::enclosing_root)
                .unwrap_or_else(|| std::path::PathBuf::from("."));
            if talk::compiling::package::PackageProject::exists_at(&project_root) {
                let project =
                    match talk::compiling::package::PackageProject::open_at(project_root, false) {
                        Ok(project) => project,
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    };
                let package_paths: Vec<std::path::PathBuf> =
                    paths.iter().map(std::path::PathBuf::from).collect();
                if *json {
                    match project.run_tests_json_at_paths(&package_paths, filter.clone()) {
                        Ok(outcome) => {
                            println!("{}", outcome.to_json());
                            if let talk::testing::JsonOutcome::Finished(summary) = outcome
                                && summary.failed()
                            {
                                std::process::exit(1);
                            }
                        }
                        Err(talk::compiling::package::PackageError::Test(err)) => {
                            println!("{}", err.to_json());
                            std::process::exit(1);
                        }
                        Err(err) => {
                            println!(
                                "{}",
                                talk::testing::JsonOutcome::error_json("package", &err.to_string())
                            );
                            std::process::exit(1);
                        }
                    }
                } else {
                    match project.run_tests_at_paths_with_filter(&package_paths, filter.clone()) {
                        Ok(talk::testing::Outcome::NoTests) => {
                            eprintln!("no .test.tlk files found")
                        }
                        Ok(talk::testing::Outcome::Finished(summary)) => {
                            print!("{}", summary.output);
                            if summary.failed() {
                                eprintln!("{} test assertion(s) failed", summary.failures);
                                std::process::exit(1);
                            }
                        }
                        Err(talk::compiling::package::PackageError::Test(
                            talk::testing::TestError::CompileDiagnostics(diagnostics),
                        )) => {
                            eprint!(
                                "{}",
                                diagnostics.render_text(talk::cli::diagnostics::ColorMode::Auto)
                            );
                            std::process::exit(1);
                        }
                        Err(err) => {
                            eprintln!("error: {err}");
                            std::process::exit(1);
                        }
                    }
                }
                return;
            }
            let runner = talk::testing::Runner::new(paths.iter().map(std::path::PathBuf::from))
                .with_filter(filter.clone());
            if *json {
                match runner.run_json() {
                    Ok(outcome) => {
                        println!("{}", outcome.to_json());
                        if let talk::testing::JsonOutcome::Finished(summary) = outcome
                            && summary.failed()
                        {
                            std::process::exit(1);
                        }
                    }
                    Err(err) => {
                        println!(
                            "{}",
                            talk::testing::JsonOutcome::error_json(err.kind(), &err.to_string())
                        );
                        std::process::exit(1);
                    }
                }
            } else {
                match runner.run() {
                    Ok(talk::testing::Outcome::NoTests) => {
                        eprintln!("no .test.tlk files found")
                    }
                    Ok(talk::testing::Outcome::Finished(summary)) => {
                        print!("{}", summary.output);
                        if summary.failed() {
                            eprintln!("{} test assertion(s) failed", summary.failures);
                            std::process::exit(1);
                        }
                    }
                    Err(talk::testing::TestError::CompileDiagnostics(diagnostics)) => {
                        eprint!(
                            "{}",
                            diagnostics.render_text(talk::cli::diagnostics::ColorMode::Auto)
                        );
                        std::process::exit(1);
                    }
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                }
            }
        }
        Commands::Build {
            filenames,
            output,
            entry,
            native,
            cc,
            target,
            cflags,
            keep_c,
        } => {
            // These only mean anything to the ahead-of-time path; taking
            // them and quietly writing a bytecode image instead would be
            // a silent no-op.
            if !*native && target.is_none() {
                let ignored = [
                    ("--cc", cc.is_some()),
                    ("--cflag", !cflags.is_empty()),
                    ("--keep-c", *keep_c),
                ];
                let given: Vec<&str> = ignored
                    .iter()
                    .filter(|(_, present)| *present)
                    .map(|(flag, _)| *flag)
                    .collect();
                if !given.is_empty() {
                    eprintln!(
                        "error: {} only applies with --native or --target",
                        given.join(", ")
                    );
                    std::process::exit(1);
                }
            }
            if *native || target.is_some() {
                build_native(
                    filenames,
                    output,
                    entry.as_deref(),
                    cc.as_deref(),
                    target.as_deref(),
                    cflags,
                    *keep_c,
                );
                return;
            }
            let executable = compile_or_exit(filenames, entry.as_deref());
            let bytes = match executable.encode_bytecode() {
                Ok(bytes) => bytes,
                Err(err) => {
                    eprintln!("error: failed to encode bytecode: {err:?}");
                    std::process::exit(1);
                }
            };
            if let Err(err) = std::fs::write(output, bytes) {
                eprintln!("error: failed to write {output}: {err}");
                std::process::exit(1);
            }
        }
        Commands::Bootstrap {
            dir,
            output,
            exports,
            allow_effects,
            check,
        } => {
            // With no source directory, this is the frontend profile:
            // the export list, allowed effects, and artifact paths all
            // come from one place (ADR 0043).
            let (outcome, output) = if let Some(dir) = dir {
                let Some(output) = output.clone() else {
                    eprintln!("error: --output is required with an explicit source directory");
                    std::process::exit(1);
                };
                let mut files: Vec<std::path::PathBuf> = match std::fs::read_dir(dir) {
                    Ok(entries) => entries
                        .filter_map(|entry| entry.ok())
                        .map(|entry| entry.path())
                        .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
                        .collect(),
                    Err(err) => {
                        eprintln!("error: failed to read {dir}: {err}");
                        std::process::exit(1);
                    }
                };
                files.sort();
                if files.is_empty() {
                    eprintln!("error: {dir} contains no .tlk sources");
                    std::process::exit(1);
                }
                let mut sources = Vec::new();
                for path in &files {
                    let name = path
                        .file_name()
                        .map(|name| name.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    match std::fs::read_to_string(path) {
                        Ok(text) => sources.push((name, text)),
                        Err(err) => {
                            eprintln!("error: failed to read {}: {err}", path.display());
                            std::process::exit(1);
                        }
                    }
                }
                match talk::compiling::bootstrap::bootstrap(&sources, exports, allow_effects, None) {
                    Ok(outcome) => (outcome, output),
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                }
            } else {
                if !exports.is_empty() || !allow_effects.is_empty() || output.is_some() {
                    eprintln!(
                        "error: the frontend profile fixes its own output, exports, and effects; pass a source directory to override them"
                    );
                    std::process::exit(1);
                }
                let root = std::env::current_dir().unwrap_or_else(|err| {
                    eprintln!("error: cannot resolve current directory: {err}");
                    std::process::exit(1);
                });
                match talk::compiling::frontend::regenerate(&root) {
                    Ok(outcome) => (
                        outcome,
                        talk::compiling::frontend::artifact_path(&root)
                            .to_string_lossy()
                            .into_owned(),
                    ),
                    Err(err) => {
                        eprintln!("error: {err}");
                        std::process::exit(1);
                    }
                }
            };
            let manifest_path = std::path::Path::new(&output).with_extension("manifest");
            let abi_path = std::path::Path::new(&output).with_extension("abi");
            if *check {
                let abi_current = match &outcome.abi {
                    Some(abi) => std::fs::read_to_string(&abi_path)
                        .ok()
                        .is_some_and(|existing| existing == *abi),
                    None => !abi_path.exists(),
                };
                let current = std::fs::read(&output).ok().is_some_and(|existing| {
                    existing == outcome.image
                }) && std::fs::read_to_string(&manifest_path)
                    .ok()
                    .is_some_and(|existing| existing == outcome.manifest.to_text())
                    && abi_current;
                if !current {
                    eprintln!(
                        "error: {output} is stale; regenerate with `talk bootstrap` (without --check)"
                    );
                    std::process::exit(1);
                }
                println!("{output} is up to date");
            } else {
                if let Some(parent) = std::path::Path::new(&output).parent()
                    && !parent.as_os_str().is_empty()
                    && let Err(err) = std::fs::create_dir_all(parent)
                {
                    eprintln!("error: failed to create {}: {err}", parent.display());
                    std::process::exit(1);
                }
                if let Err(err) = std::fs::write(&output, &outcome.image) {
                    eprintln!("error: failed to write {output}: {err}");
                    std::process::exit(1);
                }
                if let Err(err) = std::fs::write(&manifest_path, outcome.manifest.to_text()) {
                    eprintln!("error: failed to write {}: {err}", manifest_path.display());
                    std::process::exit(1);
                }
                if let Some(abi) = &outcome.abi
                    && let Err(err) = std::fs::write(&abi_path, abi)
                {
                    eprintln!("error: failed to write {}: {err}", abi_path.display());
                    std::process::exit(1);
                }
            }
        }
        Commands::RunImage { filename } => {
            use talk::compiling::driver::execute_image;
            let bytes = match std::fs::read(filename) {
                Ok(bytes) => bytes,
                Err(err) => {
                    eprintln!("error: failed to read {filename}: {err}");
                    std::process::exit(1);
                }
            };
            let mut io = talk_runtime::io::StdioIO;
            match execute_image(&bytes, &mut io) {
                Ok(Some(rendered)) => println!("{rendered}"),
                Ok(None) => {}
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Bytecode { filenames, entry } => {
            let executable = compile_or_exit(filenames, entry.as_deref());
            print!("{}", executable.render_bytecode());
        }
        Commands::C { filenames, entry } => {
            let typed = check_or_exit(filenames);
            match typed.render_c(entry.as_deref()) {
                Ok(rendered) => print!("{rendered}"),
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
            }
        }
        Commands::Mir { filenames, entry } => {
            let typed = check_or_exit(filenames);
            match typed.render_mir(entry.as_deref()) {
                Ok(rendered) => print!("{rendered}"),
                Err(message) => {
                    eprintln!("error: {message}");
                    std::process::exit(1);
                }
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
            print!(
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

Talk is a statically typed, Swift-flavored language with local type inference, generics, protocols, algebraic effects, and value-semantics aggregates. This build compiles and executes programs through a register-bytecode backend, with ownership checking (implicit sharing: consumes retain when a value has later uses; exclusivity, linearity, and the intrinsic `'unsafe` effect remain static errors). Files normally use `.tlk`; core library files live in `core/` and are implicitly imported unless a file starts with `// no-core`.

## CLI

    talk run [--entry NAME] files   compile and execute (or the current package's binary; --bin selects one, --offline skips fetches)
    talk test [paths]               discover and run `.test.tlk` tests
    talk build files -o FILE        compile to a bytecode image
    talk run-image FILE             validate and execute a bytecode image
    talk check [--json] files       typecheck, ownership-check, print diagnostics
    talk bytecode / talk mir files  render lowered output
    talk new / install / update     package management
    talk repl                       interactive type queries and completion
    talk format [file]              format source from file or stdin
    talk hover file --line N --column N | --byte-offset N | --node-id ID
    talk html / talk parse          development views
    talk lsp --stdio                language server
    talk setup nvim                 install Neovim runtime support files
    talk completions SHELL          shell completion script
    talk llm                        print this reference

## Lexical and module basics

Comments are `//` line comments. Identifiers are ordinary words; type names are conventionally upper camel case. Statements are separated by newlines; semicolons are accepted but conventionally omitted. Blocks are `{ ... }`. Top-level declarations may be prefixed with `pub` to export them. Imports are explicit: `use package::path::{ Foo, bar }`, `use package::path::{ Foo as LocalFoo }`, `use package::path`, or dependency imports such as `use dependency::{ Foo }` / `use dependency`.

## Declarations

    pub let name: Type = expr
    func f<T>(x: T, y: Int) -> Result { body }
    struct Point {
        let x: Int
        let y: Int
        init(x: Int, y: Int) { self.x = x; self.y = y; self }
    }
    enum Optional<T> { case some(T) case none }
    protocol P { associated Element func next() -> Element? }
    extend Type: P { typealias Element = Int func next() -> Int? { ... } }
    extend Type { func method() -> R { ... } static func make() -> Type { ... } }
    typealias Name = Type
    effect 'name(payload: Type) -> ReturnType

Function result annotations are optional when inferable, and so are effect payload type annotations (`effect 'oops(error) -> Never`). `init` bodies assign `self.field` and return `self`. Methods have implicit `self`; do not declare a self parameter. Receiver modes: plain `func` reads a shared value, `mut func` may update `self` and writes the receiver back at the call site, `consuming func` takes ownership. Parameters take ownership with the `consume` modifier: `func eat(consume xs: Array<Int>)`. `static func` is called on the type/protocol namespace.

## Expressions and control flow

Literals: integers, floats, strings, `true`, `false`, arrays `[a, b]`, records `{ field: expr, other: expr }`, closures `func(x: Int) -> Int { x + 1 }`. Call arguments are positional (`f(a, b)`) or labeled (`f(x: 1, y: 2)`). Constructors look like calls: `Point(x: 1, y: 2)`, enum cases may be qualified or inferred: `Optional<Int>.some(1)` or `.some(1)`. Field/member access is `value.field` and `value.method(args)`. Generic arguments may be explicit: `id<Int>(1)`. Arguments are always passed plainly — `&x` is not expression syntax; a parameter's `&T`/`&mut T` type alone makes the call site a borrow.

Bindings and mutation: `let x = expr`; assignment is `x = expr` or `self.field = expr`. `let` variables are mutable by assignment in current Talk. Type ascription is `let x: Type = expr`.

Blocks are expressions. `if cond { a } else { b }` is an expression; branches must agree. `if let .some(x) = expr { ... }` matches a pattern. Commas form left-to-right, short-circuiting condition lists and later clauses can use earlier pattern bindings: `if let .some(x) = expr, x.is_valid() { ... }`. `let .some(x) = expr else { ... }` binds `x` after the statement and evaluates the `else` block when the pattern misses. `loop { ... }` loops forever until `break`; `loop condition { ... }` is while-like. `break`, `continue`, and `return expr` are supported. `for x in iterable { ... }` uses the iterable/iterator protocols.

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

Builtin scalar/value types include `Int`, `Float`, `Bool`, `Byte`, `RawPtr`, `Void`/`()`, and `Never`. Core nominal types include `String`, `Substring`, `Array<T>`, `InlineArray<T, N>`, and `Optional<T>`; `[T]` spells a dynamic Array, `[T; N]` spells an exact-size InlineArray, and `T?` is syntax for optional. Structural record types are written `{ field: Type }` and match record literals and patterns. Function types are `(A, B) -> R`; effectful functions write effects before the arrow, e.g. `(A) 'io -> R` or `func read() 'io -> Int`. Borrow types use `&T` and exclusive borrows use `&mut T`. Protocol existential types use `any P`; associated type constraints use `any P<Element = Int>` (only protocols whose requirements keep `Self` in receiver position can form existentials — core `Iterator` cannot). Protocol composition uses `&` in where clauses: `where T: A & B`, with multiple predicates chained by `&&`; inline bounds take a single protocol.

Generics are written with angle brackets: `func id<T>(x: T) -> T`. Simple bounds use `T: Protocol`; associated types use `associated Name` in protocols and `typealias Name = Type` in conforming extensions. Protocol requirements can include funcs, mut/consuming funcs, static funcs, associated types, and defaults in extensions.

## Operators and builtins

Common operators are library-backed or builtin-resolved: arithmetic `+ - * /`, comparison `== != < <= > >=`, bitwise `& | ^ ~ << >>`, boolean values, string concatenation via `+`, member calls, and casts/ascriptions using `as` for protocol existentials where supported. Bitwise shifts mask the amount to the operand width. On a two-variant enum, postfix `?` extracts the first variant or returns the second from the enclosing function; postfix `!` extracts the first variant or evaluates `unreachable`, performing `'panic`. `print(x)` prints Showable-ish values; `sleep(ms)` and I/O live in core effects. The core library defines protocols such as `Showable`, `Add`, `Equatable`, `BitwiseAnd`, `ShiftLeft`, `Iterable`, `Iterator`, `From`, `Into`, `Borrowed`, and `Owner`.

Low-level trusted IR escapes use `@_ir(args...) { ... }` and appear mainly in core. Operations include integer/float math, bitwise operations, comparisons, `alloc`, `load`, `store`, `gep`, `copy`, and I/O shims. Outside core, `_ir` requires the intrinsic `'unsafe` effect; acknowledge and discharge it with a lexical `@unsafe { ... }` block.

## Effects

Effects are named with a leading tick: `effect 'throws(error: String) -> Never`. Calling an effect is expression syntax: `'throws("bad")`. Effect rows appear on functions before `->`: `func f() 'throws -> ()`. Handlers use `@handle 'effect { payload in body }` for abortive handling; when the effect return type is not `Never`, `'continue expr` inside the handler resumes at the perform site with that value (loop `continue` is separate and takes no value). The `unreachable` expression performs Core's public abortive `'panic` effect and has type `Never`. `@handle 'panic { message in ... }` may intercept it; otherwise Core reports the message and terminates the process.

## Memory and value model

Source-level structs, enums, arrays, strings, records, and function values have value semantics. `&T` and `&mut T` express borrow permissions, `consuming` expresses ownership transfer, and marker protocols like `Owner`/`Borrowed` describe library-level ownership roles. The backend enforces ownership with implicit sharing: a consume of a value with later uses retains automatically, snapshots preserve live views across owner mutation, and only exclusivity violations, linear-value misuse, borrow escapes (returning or globally storing a view of frame-owned data), and ungated `unsafe` constructs are static errors.

## Compiler model

Pipeline: parse -> name resolution/imports -> OutsideIn-style type checking with qualified predicates, protocols, associated types, existentials, and GADT refinements -> TypedProgram -> register MIR with ownership checking and drop elaboration -> register bytecode executed by the runtime VM (the static C runtime and the Wasm embedding host the same VM). Useful inspection commands are `talk check`, `talk hover`, and `talk mir`.
"#;

#[cfg(feature = "cli")]
const NVIM_RUNTIME_FILES: &[(&str, &[u8])] = &[
    (
        "ftdetect/talktalk.lua",
        include_bytes!("../../dev/editors/nvim/ftdetect/talktalk.lua"),
    ),
    (
        "ftplugin/talktalk.lua",
        include_bytes!("../../dev/editors/nvim/ftplugin/talktalk.lua"),
    ),
    (
        "indent/talktalk.vim",
        include_bytes!("../../dev/editors/nvim/indent/talktalk.vim"),
    ),
    (
        "lua/neotest-talk/init.lua",
        include_bytes!("../../dev/editors/nvim/lua/neotest-talk/init.lua"),
    ),
    (
        "syntax/talktalk.vim",
        include_bytes!("../../dev/editors/nvim/syntax/talktalk.vim"),
    ),
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

        println!("Installing TalkTalk Neovim runtime files bundled with talk");
        println!("Target runtime root: {}", self.target_root.display());

        for &(relative_path, contents) in NVIM_RUNTIME_FILES {
            let target = self.target_root.join(relative_path);
            if target.exists() && !self.force {
                let existing = std::fs::read(&target)
                    .with_context(|| format!("failed to read {}", target.display()))?;
                if existing.as_slice() != contents {
                    anyhow::bail!(
                        "{} already exists and differs; rerun with --force to overwrite",
                        target.display()
                    );
                }
            }
        }

        for &(relative_path, contents) in NVIM_RUNTIME_FILES {
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
}

#[cfg(feature = "cli")]
fn install_current_package(
    offline: bool,
    update: bool,
) -> Result<talk::compiling::package::PackageProject, talk::compiling::package::PackageError> {
    let root =
        std::env::current_dir().map_err(|source| talk::compiling::package::PackageError::Io {
            context: "failed to determine the current directory".into(),
            source,
        })?;
    talk::compiling::package::PackageProject::install_at(root, offline, update)
}

#[cfg(feature = "cli")]
fn update_current_package(
    offline: bool,
    packages: &[String],
) -> Result<talk::compiling::package::PackageProject, talk::compiling::package::PackageError> {
    let root =
        std::env::current_dir().map_err(|source| talk::compiling::package::PackageError::Io {
            context: "failed to determine the current directory".into(),
            source,
        })?;
    talk::compiling::package::PackageProject::update_at(root, offline, packages)
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
fn check_or_exit(
    filenames: &[String],
) -> talk::compiling::driver::Driver<talk::compiling::driver::Typed> {
    use talk::compiling::driver::{Driver, DriverConfig};
    let sources = sources_for_filenames(filenames);
    let driver = Driver::new(sources, DriverConfig::new("Main"));
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
            eprintln!("{diagnostic}");
        }
        std::process::exit(1);
    }
    typed
}

/// Create the scratch translation unit, refusing to write through an
/// existing file. `create_new` makes the create-and-open one step, so a
/// name that lost a race -- or was pre-created as a symlink pointing
/// somewhere else -- is an error rather than a file this process
/// truncates. On unix it is created readable only by its owner.
#[cfg(feature = "cli")]
fn scratch_source(source: &str) -> std::io::Result<std::path::PathBuf> {
    use std::io::Write as _;

    let directory = std::env::temp_dir();
    let mut last = None;
    for attempt in 0..32u32 {
        let unique = format!(
            "talk-{}-{}-{attempt}.c",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|elapsed| elapsed.as_nanos())
                .unwrap_or_default()
        );
        let path = directory.join(unique);
        let mut options = std::fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt as _;
            options.mode(0o600);
        }
        match options.open(&path) {
            Ok(mut file) => {
                file.write_all(source.as_bytes())?;
                return Ok(path);
            }
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => last = Some(err),
            Err(err) => return Err(err),
        }
    }
    Err(last.unwrap_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "could not find an unused scratch name",
        )
    }))
}

/// Which C compiler to drive.
///
/// The default is the host's, because the generated translation unit is
/// ordinary self-contained C and whatever the machine already has will
/// build it. Cross-compiling is the case that needs more than a compiler
/// -- headers and a libc for the target too -- so it goes through `zig
/// cc`, which carries its own.
#[cfg(feature = "cli")]
enum Toolchain {
    Host(String),
    Zig(String),
}

#[cfg(feature = "cli")]
impl Toolchain {
    fn command(&self) -> (&str, Vec<String>) {
        match self {
            Toolchain::Host(program) => (program, vec![]),
            Toolchain::Zig(triple) => ("zig", vec!["cc".into(), "-target".into(), triple.clone()]),
        }
    }
}

#[cfg(feature = "cli")]
fn toolchain(compiler: Option<&str>, target: Option<&str>) -> Result<Toolchain, String> {
    let Some(triple) = target else {
        return Ok(Toolchain::Host(
            compiler
                .map(str::to_string)
                .or_else(|| std::env::var("CC").ok())
                .unwrap_or_else(|| "cc".to_string()),
        ));
    };
    // An explicit --cc wins: someone who has a cross toolchain of their
    // own should not be made to install another one.
    if let Some(compiler) = compiler {
        return Ok(Toolchain::Host(compiler.to_string()));
    }
    let available = std::process::Command::new("zig")
        .arg("version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|status| status.success());
    if !available {
        return Err(format!(
            "error: cross-compiling to `{triple}` needs `zig` on PATH\n\
             note: zig cc carries headers and a libc for every target, which a\n\
             \x20     bare cross compiler does not\n\
             note: install it from https://ziglang.org/download/ (or your package\n\
             \x20     manager), or pass --cc with a cross compiler you already have"
        ));
    }
    Ok(Toolchain::Zig(triple.to_string()))
}

/// Compile ahead of time to a native executable: emit C, then drive a C
/// compiler over it. The generated translation unit is self-contained, so
/// there is nothing to link against and no build system involved.
#[cfg(feature = "cli")]
fn build_native(
    filenames: &[String],
    output: &str,
    entry: Option<&str>,
    compiler: Option<&str>,
    target: Option<&str>,
    extra_flags: &[String],
    keep_c: bool,
) {
    let toolchain = match toolchain(compiler, target) {
        Ok(toolchain) => toolchain,
        Err(message) => {
            eprintln!("{message}");
            std::process::exit(1);
        }
    };
    let source = match check_or_exit(filenames).render_c(entry) {
        Ok(source) => source,
        Err(message) => {
            eprintln!("error: {message}");
            std::process::exit(1);
        }
    };

    // A uniquely named scratch file, never `<output>.c`: building `foo`
    // must not truncate a `foo.c` that the user owns. `--keep-c` is the
    // one case that writes beside the output, because it was asked for.
    let c_path = if keep_c {
        std::path::Path::new(output).with_extension("c")
    } else {
        match scratch_source(&source) {
            Ok(path) => path,
            Err(err) => {
                eprintln!("error: failed to write the generated C: {err}");
                std::process::exit(1);
            }
        }
    };
    if keep_c && let Err(err) = std::fs::write(&c_path, &source) {
        eprintln!("error: failed to write {}: {err}", c_path.display());
        std::process::exit(1);
    }

    let (program, leading) = toolchain.command();
    let mut command = std::process::Command::new(program);
    command
        .args(leading)
        .args(["-O2", "-std=c11"])
        .arg(&c_path)
        .arg("-o")
        .arg(output)
        .args(extra_flags);
    let status = match command.status() {
        Ok(status) => status,
        Err(err) => {
            eprintln!("error: failed to run `{program}`: {err}");
            eprintln!("note: the generated C is at {}", c_path.display());
            std::process::exit(1);
        }
    };
    if !status.success() {
        eprintln!("error: `{program}` failed to compile the generated C");
        eprintln!("note: the generated C is at {}", c_path.display());
        std::process::exit(1);
    }
    if !keep_c {
        let _ = std::fs::remove_file(&c_path);
    }
}

#[cfg(feature = "cli")]
fn compile_or_exit(
    filenames: &[String],
    entry: Option<&str>,
) -> talk::compiling::driver::Executable {
    match check_or_exit(filenames).compile_executable(entry) {
        Ok(executable) => executable,
        Err(message) => {
            eprintln!("error: {message}");
            std::process::exit(1);
        }
    }
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
