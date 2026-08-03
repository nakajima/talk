//! The frozen parse-dump golden corpus (ADR 0043). The dump format is
//! owned by the self-hosted frontend (stdlib/syntax/Dump.tlk); the goldens
//! under `tests/parser/**/expected/` pin it byte-for-byte. The Rust
//! renderer that originally defined the format is deleted (Stage 5) —
//! the migration harness proved the frontend reproduces it exactly.

#[cfg(test)]
mod tests {
    use std::path::Path;

    fn check_corpus_dir(dir: &Path, dumper: &dyn Fn(&str) -> String) {
        let expected_dir = dir.join("expected");
        let update = std::env::var_os("TALK_UPDATE_PARSER_DUMPS").is_some();
        let mut entries: Vec<_> = std::fs::read_dir(dir)
            .unwrap_or_else(|_| panic!("{} exists", dir.display()))
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "tlk"))
            .collect();
        entries.sort();
        assert!(!entries.is_empty(), "{} must not be empty", dir.display());

        for path in entries {
            let source = std::fs::read_to_string(&path).expect("read corpus source");
            let actual = dumper(&source);
            let name = path.file_stem().expect("file stem").to_string_lossy();
            let expected_path = expected_dir.join(format!("{name}.dump"));
            if update {
                std::fs::create_dir_all(&expected_dir).expect("expected dir");
                std::fs::write(&expected_path, &actual).expect("write dump");
                continue;
            }
            let expected = std::fs::read_to_string(&expected_path).unwrap_or_else(|_| {
                panic!(
                    "missing {}; regenerate with TALK_UPDATE_PARSER_DUMPS=1",
                    expected_path.display()
                )
            });
            assert_eq!(
                actual,
                expected,
                "{} dumped differently; regenerate with TALK_UPDATE_PARSER_DUMPS=1 if intended",
                path.display()
            );
        }
    }

    /// Golden corpus: every `tests/parser/**/*.tlk` must dump exactly
    /// as its `expected/*.dump` sibling — whole files at the root, one
    /// subdirectory per category entry point. Regenerate with
    /// `TALK_UPDATE_PARSER_DUMPS=1 cargo test -p talk parser_dump`.
    fn frontend_dump(export: &'static str) -> impl Fn(&str) -> String {
        move |source| {
            crate::compiling::frontend::dump_export(export, source)
                .unwrap_or_else(|error| panic!("{export} failed: {error}"))
        }
    }

    /// The dumps come from the self-hosted frontend (ADR 0043 Stage
    /// 5): the goldens pin the frozen dump format the migration
    /// validated byte-for-byte against the retired Rust parser.
    #[test]
    fn parser_dump_corpus_matches_expected() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/parser");
        check_corpus_dir(&root, &frontend_dump("parse"));
        check_corpus_dir(&root.join("expr"), &frontend_dump("parse_expr"));
        check_corpus_dir(&root.join("pattern"), &frontend_dump("parse_pattern"));
        check_corpus_dir(&root.join("type"), &frontend_dump("parse_type"));
        check_corpus_dir(&root.join("block"), &frontend_dump("parse_block_items"));
        check_corpus_dir(&root.join("tokentree"), &frontend_dump("trees"));
        check_corpus_dir(&root.join("lenient"), &frontend_dump("parse_lenient"));
        check_corpus_dir(&root.join("unicode"), &frontend_dump("parse"));
    }
}
