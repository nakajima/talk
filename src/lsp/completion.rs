#[cfg(test)]
mod tests {
    use async_lsp::lsp_types::{CompletionItem, Position};
    use indoc::formatdoc;

    use crate::compiling::driver::{Driver, DriverConfig, Source};

    fn complete(
        files: Vec<&str>,
        _position: Position,
        _is_member_lookup: bool,
    ) -> Vec<CompletionItem> {
        let mut _driver = Driver::new(
            files.into_iter().map(Source::from).collect(),
            DriverConfig::new("TestDriver"),
        );
        vec![]

        // let checked = driver.check();
        // let checked_unit = checked.first().unwrap();
        // let source_file = checked_unit.source_file(Path::new("./file-0.tlk")).unwrap();
        // let env = &checked_unit.env.clone();
    }

    #[test]
    #[ignore = "wip"]
    fn test_variable_completion() {
        let completions = complete(
            vec![
                "
            let foo = 1
            f
            ",
            ],
            Position::new(2, 1),
            false,
        );

        assert_eq!(
            completions.len(),
            7,
            "{:?}",
            completions
                .iter()
                .map(|c| c.label.clone())
                .collect::<Vec<String>>()
        );
        assert_eq!(completions[0].label, "foo");
    }

    #[test]
    #[ignore = "wip"]
    fn test_member_completion() {
        let completions = complete(
            vec![&formatdoc!(
                r#"
            struct Foo {{
                let bar: Int
            }}
            let foo = Foo(bar: 1)
            foo.
            "#
            )],
            Position::new(4, 4),
            true,
        );

        assert_eq!(completions.len(), 1, "{completions:?}");
        assert_eq!(completions[0].label, "bar");
    }

    #[test]
    #[ignore = "wip"]
    fn test_self_member_completion() {
        let completions = complete(
            vec![&formatdoc!(
                r#"
            struct Foo {{
                let bar: Int

                func fizz() {{
                    self.
                }}
            }}
            "#
            )],
            Position::new(4, 9),
            true,
        );

        assert_eq!(completions.len(), 1);
        assert_eq!(completions[0].label, "bar");
    }

    #[test]
    #[ignore = "wip"]
    fn test_record_member_completion() {
        let completions = complete(
            vec![&formatdoc!(
                r#"
            let point = {{x: 10, y: 20}}
            point.
            "#
            )],
            Position::new(1, 6),
            true,
        );

        assert_eq!(completions.len(), 2, "{completions:?}");
        let labels: Vec<&str> = completions.iter().map(|c| c.label.as_str()).collect();
        assert!(labels.contains(&"x"));
        assert!(labels.contains(&"y"));
    }
}
