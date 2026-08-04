use std::ffi::OsString;
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use talk::compiling::driver::{Driver, DriverConfig, MirEntry, Source, Typed};

struct Options {
    build: bool,
    entry: Option<String>,
    binary: Option<String>,
    offline: bool,
    output: Option<PathBuf>,
    compiler: Option<OsString>,
    compiler_flags: Vec<OsString>,
    keep: bool,
    exports: Vec<String>,
    allow_effects: Vec<String>,
    prefix: Option<String>,
    header: Option<PathBuf>,
    manifest: Option<PathBuf>,
    files: Vec<OsString>,
}

/// What one invocation emits: a process or a library (ADR 0048).
enum Emitted {
    Executable(talk_llvm::Artifact),
    Library(talk_llvm::LibraryArtifact),
}

fn main() {
    let options = match Options::parse(std::env::args_os().skip(1)) {
        Ok(Some(options)) => options,
        Ok(None) => return,
        Err(message) => fail(&message),
    };
    let emitted = match compile(&options) {
        Ok(emitted) => emitted,
        Err(message) => fail(&message),
    };
    let (ir, runtime_c, shared) = match &emitted {
        Emitted::Executable(artifact) => (&artifact.ir, &artifact.runtime_c, false),
        Emitted::Library(artifact) => {
            for (path, text) in [
                (&options.header, &artifact.header),
                (&options.manifest, &artifact.manifest),
            ] {
                if let Some(path) = path
                    && let Err(error) = std::fs::write(path, text)
                {
                    fail(&format!("failed to write {}: {error}", path.display()));
                }
            }
            (&artifact.ir, &artifact.runtime_c, true)
        }
    };
    if options.build {
        let Some(output) = options.output.as_deref() else {
            fail("build requires -o or --output");
        };
        build(
            ir,
            runtime_c,
            shared,
            output,
            options.compiler.as_deref(),
            &options.compiler_flags,
            options.keep,
        );
    } else {
        print!("{ir}");
    }
}

impl Options {
    fn parse(arguments: impl Iterator<Item = OsString>) -> Result<Option<Self>, String> {
        let mut arguments = arguments.peekable();
        let build = arguments.next_if(|argument| argument == "build").is_some();
        let mut options = Self {
            build,
            entry: None,
            binary: None,
            offline: false,
            output: None,
            compiler: None,
            compiler_flags: Vec::new(),
            keep: false,
            exports: Vec::new(),
            allow_effects: Vec::new(),
            prefix: None,
            header: None,
            manifest: None,
            files: Vec::new(),
        };
        let mut positional = false;
        while let Some(argument) = arguments.next() {
            if positional {
                options.files.push(argument);
                continue;
            }
            match argument.to_str() {
                Some("--") => positional = true,
                Some("-h" | "--help") => {
                    print_help();
                    return Ok(None);
                }
                Some("--version") => {
                    println!("talk-llvm {}", env!("CARGO_PKG_VERSION"));
                    return Ok(None);
                }
                Some("--entry") => {
                    options.entry = Some(string_value("--entry", arguments.next())?);
                }
                Some("--bin") => {
                    options.binary = Some(string_value("--bin", arguments.next())?);
                }
                Some("--offline") => options.offline = true,
                Some("-o" | "--output") => {
                    options.output = Some(PathBuf::from(value("--output", arguments.next())?));
                }
                Some("--cc") => {
                    options.compiler = Some(value("--cc", arguments.next())?);
                }
                Some("--cflag") => {
                    options
                        .compiler_flags
                        .push(value("--cflag", arguments.next())?);
                }
                Some("--keep") => options.keep = true,
                Some("--export") => {
                    options.exports.push(string_value("--export", arguments.next())?);
                }
                Some("--allow-effect") => {
                    options
                        .allow_effects
                        .push(string_value("--allow-effect", arguments.next())?);
                }
                Some("--prefix") => {
                    options.prefix = Some(string_value("--prefix", arguments.next())?);
                }
                Some("--header") => {
                    options.header = Some(PathBuf::from(value("--header", arguments.next())?));
                }
                Some("--manifest") => {
                    options.manifest = Some(PathBuf::from(value("--manifest", arguments.next())?));
                }
                Some(value) if value.starts_with('-') && value != "-" => {
                    return Err(format!("unknown option `{value}`"));
                }
                _ => options.files.push(argument),
            }
        }
        if !options.build {
            if options.output.is_some() {
                return Err("--output only applies to `talk llvm build`".into());
            }
            if options.compiler.is_some() || !options.compiler_flags.is_empty() || options.keep {
                return Err("--cc, --cflag, and --keep only apply to `talk llvm build`".into());
            }
        }
        if options.exports.is_empty() {
            if !options.allow_effects.is_empty()
                || options.prefix.is_some()
                || options.header.is_some()
                || options.manifest.is_some()
            {
                return Err(
                    "--allow-effect, --prefix, --header, and --manifest require --export".into(),
                );
            }
        } else if options.entry.is_some() {
            return Err("--entry does not apply to --export".into());
        }
        Ok(Some(options))
    }
}

fn value(flag: &str, value: Option<OsString>) -> Result<OsString, String> {
    value.ok_or_else(|| format!("{flag} requires a value"))
}

fn string_value(flag: &str, argument: Option<OsString>) -> Result<String, String> {
    value(flag, argument)?
        .into_string()
        .map_err(|_| format!("{flag} requires UTF-8 text"))
}

fn compile(options: &Options) -> Result<Emitted, String> {
    if !options.exports.is_empty() {
        if options.binary.is_some() || options.offline {
            return Err("--export requires source files, not a package".into());
        }
        let module = typecheck(&options.files)?
            .compile_mir(MirEntry::Exports {
                names: &options.exports,
                allowed_effects: &options.allow_effects,
            })
            .map(|output| output.module)?;
        return talk_llvm::emit_library(&module, options.prefix.as_deref().unwrap_or("talk"))
            .map(Emitted::Library)
            .map_err(|error| error.to_string());
    }
    let package_root = if options.files.is_empty() {
        talk::compiling::package::PackageProject::enclosing_root(".")
    } else {
        None
    };
    let module = if let Some(root) = package_root {
        let project = talk::compiling::package::PackageProject::open_at(root, options.offline)
            .map_err(|error| error.to_string())?;
        project
            .mir_binary(options.binary.as_deref(), options.entry.as_deref())
            .map_err(|error| error.to_string())?
            .module
    } else {
        if options.binary.is_some() {
            return Err("--bin requires package compilation without source files".into());
        }
        if options.offline {
            return Err("--offline requires package compilation without source files".into());
        }
        let entry = match options.entry.as_deref() {
            Some(name) => MirEntry::Named(name),
            None => MirEntry::Script,
        };
        typecheck(&options.files)?
            .compile_mir(entry)
            .map(|output| output.module)?
    };
    talk_llvm::emit(&module)
        .map(Emitted::Executable)
        .map_err(|error| error.to_string())
}

fn typecheck(files: &[OsString]) -> Result<Driver<Typed>, String> {
    let sources = if files.is_empty() {
        let mut text = String::new();
        std::io::stdin()
            .read_to_string(&mut text)
            .map_err(|error| format!("failed to read stdin: {error}"))?;
        vec![Source::in_memory(PathBuf::from("<stdin>"), text)]
    } else {
        let mut sources = Vec::with_capacity(files.len());
        let mut stdin = None;
        for file in files {
            if file == "-" {
                if stdin.is_none() {
                    let mut text = String::new();
                    std::io::stdin()
                        .read_to_string(&mut text)
                        .map_err(|error| format!("failed to read stdin: {error}"))?;
                    stdin = Some(text);
                }
                sources.push(Source::in_memory(
                    PathBuf::from("<stdin>"),
                    stdin.as_ref().cloned().unwrap_or_default(),
                ));
            } else {
                sources.push(Source::from(PathBuf::from(file)));
            }
        }
        sources
    };
    let parsed = Driver::new(sources, DriverConfig::new("Main"))
        .parse()
        .map_err(|error| format!("{error:?}"))?;
    let resolved = parsed
        .resolve_names()
        .map_err(|error| format!("{error:?}"))?;
    let typed = resolved.type_check();
    if typed.has_errors() {
        let diagnostics = typed
            .diagnostics()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        return Err(diagnostics);
    }
    Ok(typed)
}

fn build(
    ir: &str,
    runtime_c: &str,
    shared: bool,
    output: &Path,
    compiler: Option<&std::ffi::OsStr>,
    compiler_flags: &[OsString],
    keep: bool,
) {
    let (ir_path, runtime_path) = if keep {
        (
            output.with_extension("ll"),
            output.with_extension("runtime.c"),
        )
    } else {
        let ir_path = scratch_file(ir, "ll").unwrap_or_else(|error| {
            fail(&format!("failed to write generated IR: {error}"));
        });
        let runtime_path = scratch_file(runtime_c, "c").unwrap_or_else(|error| {
            let _ = std::fs::remove_file(&ir_path);
            fail(&format!("failed to write generated runtime: {error}"));
        });
        (ir_path, runtime_path)
    };
    if keep {
        std::fs::write(&ir_path, ir).unwrap_or_else(|error| {
            fail(&format!("failed to write {}: {error}", ir_path.display()));
        });
        std::fs::write(&runtime_path, runtime_c).unwrap_or_else(|error| {
            fail(&format!(
                "failed to write {}: {error}",
                runtime_path.display()
            ));
        });
    }

    let compiler = compiler
        .map(OsString::from)
        .or_else(|| std::env::var_os("CLANG"))
        .unwrap_or_else(|| "clang".into());
    let mut command = Command::new(&compiler);
    command.args(["-O2", "-std=c11"]);
    if shared {
        // A library artifact renders as a shared object the host links
        // or loads (ADR 0048).
        command.args(["-shared", "-fPIC"]);
    }
    let status = command
        .arg(&ir_path)
        .arg(&runtime_path)
        .arg("-o")
        .arg(output)
        .args(compiler_flags)
        .status();
    match status {
        Ok(status) if status.success() => {}
        Ok(_) => {
            eprintln!(
                "error: `{}` failed to compile the generated module",
                compiler.to_string_lossy()
            );
            eprintln!("note: IR is at {}", ir_path.display());
            eprintln!("note: runtime source is at {}", runtime_path.display());
            std::process::exit(1);
        }
        Err(error) => {
            eprintln!(
                "error: failed to run `{}`: {error}",
                compiler.to_string_lossy()
            );
            eprintln!("note: IR is at {}", ir_path.display());
            eprintln!("note: runtime source is at {}", runtime_path.display());
            std::process::exit(1);
        }
    }
    if !keep {
        let _ = std::fs::remove_file(ir_path);
        let _ = std::fs::remove_file(runtime_path);
    }
}

fn scratch_file(source: &str, extension: &str) -> std::io::Result<PathBuf> {
    use std::io::Write as _;

    let directory = std::env::temp_dir();
    let mut last = None;
    for attempt in 0..32u32 {
        let unique = format!(
            "talk-llvm-{}-{}-{attempt}.{extension}",
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
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => last = Some(error),
            Err(error) => return Err(error),
        }
    }
    Err(last.unwrap_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "could not find an unused scratch name",
        )
    }))
}

fn print_help() {
    println!(
        r#"LLVM code generation for Talk

Usage:
  talk llvm [OPTIONS] [FILES]...
  talk llvm build [OPTIONS] -o FILE [FILES]...

With no files inside a package, compile its selected binary.
Pass - explicitly to compile standard input instead.

Options:
      --entry NAME       Compile a named zero-parameter entry
      --bin NAME         Select a package binary
      --offline          Use only locally installed package sources
      --export NAME      Emit a library instead of a program: one
                         host-callable wrapper per export; repeatable
      --allow-effect E   Effects the exports may perform; repeatable
      --prefix PREFIX    External symbol prefix for the library
      --header PATH      Write the library's generated C header
      --manifest PATH    Write the export-name-to-symbol manifest
  -o, --output FILE      Output executable for build; a shared library
                         with --export
      --cc PROGRAM       Clang-compatible compiler driver
      --cflag FLAG       Extra compiler argument; repeatable
      --keep             Keep .ll and .runtime.c files
  -h, --help             Print help"#
    );
}

fn fail(message: &str) -> ! {
    eprintln!("error: {message}");
    std::process::exit(1);
}
