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
        std::fs::read_to_string(&dotgit)
            .ok()
            .and_then(|content| {
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
