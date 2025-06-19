use crate::SourceFile;
use crate::Typed;
use crate::compiling::driver::Driver;
use crate::environment::TypeDef;
use crate::symbol_table::SymbolKind;
use crate::type_checker::Ty;
use async_lsp::lsp_types::CompletionItem;
use async_lsp::lsp_types::CompletionItemKind;
use async_lsp::lsp_types::Position;

pub struct CompletionContext<'a> {
    pub driver: &'a Driver,
    pub source_file: &'a SourceFile<Typed>,
    pub position: Position,
    pub is_member_lookup: bool,
}

impl From<Position> for crate::diagnostic::Position {
    fn from(value: Position) -> Self {
        Self {
            line: value.line,
            col: value.character,
        }
    }
}

impl<'a> CompletionContext<'a> {
    pub fn get_completions(&self) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        if self.is_member_lookup {
            completions.extend(self.get_member_completions());
        } else {
            completions.extend(self.get_scope_completions());
            completions.extend(self.get_keyword_completions());
        }

        completions
    }

    fn get_member_completions(&self) -> Vec<CompletionItem> {
        let position_before_dot = Position::new(
            self.position.line,
            self.position.character.saturating_sub(1),
        );

        if let Some(ty) = self
            .driver
            .symbol_from_position(position_before_dot, &self.source_file.path)
            .map(|sym| {
                self.source_file
                    .type_from_symbol(sym, &self.driver.symbol_table)
            })
            .unwrap_or(None)
        {
            let type_def = match ty {
                Ty::Enum(symbol_id, _) => self.source_file.type_def(&symbol_id),
                Ty::Struct(symbol_id, _) => self.source_file.type_def(&symbol_id),
                _ => return vec![],
            };

            match type_def {
                Some(TypeDef::Enum(enum_def)) => {
                    let mut completions = vec![];
                    completions.extend(enum_def.methods.keys().map(|label| CompletionItem {
                        label: label.clone(),
                        kind: Some(CompletionItemKind::METHOD),
                        ..Default::default()
                    }));

                    completions.extend(enum_def.variants.iter().map(|variant| CompletionItem {
                        label: variant.name.clone(),
                        kind: Some(CompletionItemKind::METHOD),
                        ..Default::default()
                    }));

                    completions
                }
                Some(TypeDef::Struct(struct_def)) => {
                    let mut completions = vec![];
                    completions.extend(struct_def.methods.keys().map(|label| CompletionItem {
                        label: label.clone(),
                        kind: Some(CompletionItemKind::METHOD),
                        ..Default::default()
                    }));
                    completions.extend(struct_def.properties.iter().map(|prop| CompletionItem {
                        label: prop.name.clone(),
                        kind: Some(CompletionItemKind::PROPERTY),
                        ..Default::default()
                    }));
                    completions
                }
                _ => vec![],
            }
        } else {
            vec![]
        }
    }

    fn get_keyword_completions(&self) -> Vec<CompletionItem> {
        // This can be made more context-aware
        vec!["let", "if", "else", "func", "struct", "loop"]
            .into_iter()
            .map(|kw| CompletionItem {
                label: kw.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                ..Default::default()
            })
            .collect()
    }

    fn get_scope_completions(&self) -> Vec<CompletionItem> {
        let mut scope_completions = Vec::new();
        // This method needs to be implemented in your SymbolTable

        if let Some(scope) = self
            .source_file
            .scope_tree
            .find_scope_at(self.position.into())
        {
            for symbol_id in self.source_file.scope_tree.get_symbols_in_scope(scope) {
                if let Some(symbol_info) = self.driver.symbol_table.get(&symbol_id) {
                    let kind = match symbol_info.kind {
                        SymbolKind::Func => CompletionItemKind::FUNCTION,
                        SymbolKind::Param => CompletionItemKind::VARIABLE,
                        SymbolKind::Local => CompletionItemKind::VARIABLE,
                        SymbolKind::Enum => CompletionItemKind::ENUM,
                        SymbolKind::Struct => CompletionItemKind::STRUCT,
                        SymbolKind::TypeParameter => CompletionItemKind::TYPE_PARAMETER,
                        SymbolKind::BuiltinType => CompletionItemKind::CLASS,
                        SymbolKind::BuiltinFunc => CompletionItemKind::FUNCTION,
                        _ => CompletionItemKind::TEXT,
                    };

                    scope_completions.push(CompletionItem {
                        label: symbol_info.name.clone(),
                        kind: Some(kind),
                        ..Default::default()
                    });
                }
            }
        }

        scope_completions
    }
}

#[cfg(test)]
mod tests {
    use async_lsp::lsp_types::{CompletionItem, Position};
    use indoc::formatdoc;

    use crate::{compiling::driver::Driver, lsp::completion::CompletionContext};

    fn complete(
        files: Vec<&str>,
        position: Position,
        is_member_lookup: bool,
    ) -> Vec<CompletionItem> {
        let mut driver = Driver::new(Default::default());
        for (i, file) in files.iter().enumerate() {
            driver.update_file(&(&format!("./file-{}.tlk", i)).into(), file.to_string());
        }

        let source_file = &driver.typed_source_file(&"./file-0.tlk".into()).unwrap();

        CompletionContext {
            driver: &driver,
            source_file,
            position,
            is_member_lookup,
        }
        .get_completions()
    }

    #[test]
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

        assert_eq!(completions.len(), 1);
        assert_eq!(completions[0].label, "bar");
    }
}
