fn main() {
    println!("cargo:rerun-if-env-changed=TALK_BUILD_SHA");
    println!("cargo:rerun-if-env-changed=GITHUB_SHA");
    println!("cargo:rerun-if-changed=.git/HEAD");
    if let Ok(head) = std::fs::read_to_string(".git/HEAD")
        && let Some(ref_name) = head.trim().strip_prefix("ref: ")
    {
        println!("cargo:rerun-if-changed=.git/{ref_name}");
    }

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
