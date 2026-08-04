fn main() {
    println!("cargo:rerun-if-env-changed=TALK_BUILD_SHA");
    println!("cargo:rerun-if-env-changed=GITHUB_SHA");
    emit_git_head_watches();

    let sha = std::env::var("TALK_BUILD_SHA")
        .ok()
        .or_else(|| std::env::var("GITHUB_SHA").ok())
        .or_else(|| {
            let output = std::process::Command::new("git")
                .args(["rev-parse", "HEAD"])
                .output()
                .ok()?;
            if output.status.success() {
                String::from_utf8(output.stdout).ok()
            } else {
                None
            }
        })
        .map(|value| value.trim().to_string())
        .filter(|value| value.len() >= 7 && value.bytes().all(|byte| byte.is_ascii_hexdigit()));

    if let Some(sha) = sha {
        println!("cargo:rustc-env=TALK_BUILD_SHA={sha}");
    }

    compile_native_frontend();
}

/// Compile the checked-in native frontend translation unit for the
/// Cargo target and link the resulting object (ADR 0048). The manifest
/// binds the C to the bootstrap fixed point, so a hand-edited or stale
/// `frontend.c` fails the build here rather than misparsing later. A
/// target without a working C toolchain fails explicitly; there is no
/// bytecode fallback for production parsing.
fn compile_native_frontend() {
    use sha2::Digest as _;

    // wasm32 has no C toolchain story under wasm-pack; it executes the
    // verified bootstrap bytecode in the VM instead (ADR 0048 wasm
    // carve-out) and skips the native artifact entirely.
    if std::env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("wasm32") {
        return;
    }

    println!("cargo:rerun-if-changed=bootstrap/frontend.c");
    println!("cargo:rerun-if-changed=bootstrap/frontend.manifest");
    let manifest = std::fs::read_to_string("bootstrap/frontend.manifest")
        .expect("bootstrap/frontend.manifest is missing; regenerate with `talk bootstrap`");
    let recorded = manifest
        .lines()
        .find_map(|line| line.trim().strip_prefix("c_digest:"))
        .map(str::trim)
        .expect(
            "bootstrap/frontend.manifest records no c_digest; regenerate with `talk bootstrap`",
        );
    let source = std::fs::read("bootstrap/frontend.c")
        .expect("bootstrap/frontend.c is missing; regenerate with `talk bootstrap`");
    let actual = format!("{:x}", sha2::Sha256::digest(&source));
    assert_eq!(
        recorded, actual,
        "bootstrap/frontend.c does not match its manifest; regenerate with `talk bootstrap`"
    );

    // Full optimization regardless of the Cargo profile: parsing speed
    // is the point of the native frontend, dev builds included, and the
    // object is cached until the checked-in C changes.
    cc::Build::new()
        .file("bootstrap/frontend.c")
        .opt_level(2)
        .flag_if_supported("-std=c11")
        .try_compile("talk_frontend_native")
        .unwrap_or_else(|error| {
            panic!(
                "failed to compile the native frontend for this target: {error}\n\
                 building Talk requires a target C compiler (ADR 0048); \
                 a target that cannot build the native frontend is unsupported"
            )
        });
}

/// Watch the checked-out commit for changes. In a plain checkout
/// `.git/HEAD` (and the ref it names) are files under `.git`; in a
/// linked worktree `.git` is a pointer file and both live in the real
/// gitdir. Watching a path that does not exist would rerun this
/// script — and relink every binary — on every build, which also
/// invalidates the compiled-stdlib cache keyed on binary identity.
fn emit_git_head_watches() {
    let dotgit = std::path::PathBuf::from(".git");
    let gitdir = if dotgit.is_file() {
        std::fs::read_to_string(&dotgit).ok().and_then(|content| {
            content
                .trim()
                .strip_prefix("gitdir: ")
                .map(std::path::PathBuf::from)
        })
    } else {
        Some(dotgit)
    };
    let Some(gitdir) = gitdir else { return };
    let head_path = gitdir.join("HEAD");
    println!("cargo:rerun-if-changed={}", head_path.display());
    let Ok(head) = std::fs::read_to_string(&head_path) else {
        return;
    };
    let Some(ref_name) = head.trim().strip_prefix("ref: ") else {
        return;
    };
    // A linked worktree's shared refs live in the common gitdir.
    let commondir = std::fs::read_to_string(gitdir.join("commondir"))
        .ok()
        .map(|path| gitdir.join(path.trim()))
        .unwrap_or_else(|| gitdir.clone());
    let ref_path = commondir.join(ref_name);
    if ref_path.exists() {
        println!("cargo:rerun-if-changed={}", ref_path.display());
    } else if commondir.join("packed-refs").exists() {
        println!(
            "cargo:rerun-if-changed={}",
            commondir.join("packed-refs").display()
        );
    }
}
