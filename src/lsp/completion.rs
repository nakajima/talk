use crate::SourceFile;
use crate::Typed;
use crate::compiling::driver::Driver;
use crate::environment::Environment;
use crate::symbol_table::SymbolKind;
use crate::ty::RowKind;
use crate::type_checking::ty::Ty;
use crate::type_checking::type_def::TypeMember;
use async_lsp::lsp_types::CompletionItem;
use async_lsp::lsp_types::CompletionItemKind;
use async_lsp::lsp_types::Position;

pub struct CompletionContext<'a> {
    pub driver: &'a Driver,
    pub env: &'a Environment,
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
        // Move the lookup position two characters back from the current
        // cursor location. The completion request position is typically
        // placed *after* the dot triggering the member lookup. Moving two
        // characters ensures that the position we query for a symbol lies
        // within the preceding identifier rather than on the dot itself,
        // which would not be associated with any symbol span.
        let position_before_dot = Position::new(
            self.position.line,
            self.position.character.saturating_sub(2),
        );

        // First, try to get the type of the expression before the dot
        let expr_type = self
            .driver
            .symbol_at_position(position_before_dot.into(), &self.source_file.path)
            .and_then(|sym| {
                let info = self.driver.symbol_table.get(&sym)?;
                self.source_file
                    .typed_expr(info.expr_id)
                    .map(|typed| typed.ty.clone())
            })
            // Fallback for `self` keyword completion
            .or_else(|| self.env.selfs.last().cloned());

        if let Some(ty) = expr_type {
            self.get_completions_for_type(&ty)
        } else {
            // If we couldn't find the type directly, try the old approach
            let type_sym = self
                .driver
                .symbol_at_position(position_before_dot.into(), &self.source_file.path)
                .and_then(|sym| {
                    let info = self.driver.symbol_table.get(&sym)?;
                    info.definition
                        .as_ref()
                        .and_then(|def| def.sym)
                        .or_else(|| self.env.lookup_type(&sym).map(|_| sym))
                });

            if let Some(type_def) = type_sym.and_then(|sym| self.env.lookup_type(&sym)) {
                self.get_completions_for_typedef(type_def)
            } else {
                tracing::error!("did not get type: {:?}", self.env.types);
                vec![]
            }
        }
    }

    /// Get completions for a specific type (handles both records and typedefs)
    fn get_completions_for_type(&self, ty: &Ty) -> Vec<CompletionItem> {
        match ty {
            // Enums are now represented as Row types
            // Handle unified row types
            Ty::Row { kind, .. } => {
                if let RowKind::Struct(symbol_id, _)
                | RowKind::Protocol(symbol_id, _)
                | RowKind::Enum(symbol_id, _) = kind
                {
                    // Nominal row - use typedef
                    if let Some(type_def) = self.env.lookup_type(symbol_id) {
                        self.get_completions_for_typedef(type_def)
                    } else {
                        vec![]
                    }
                } else {
                    // Structural row - TODO: look up fields from constraints
                    vec![]
                }
            }
            _ => vec![],
        }
    }

    /// Get completions from a typedef's members
    fn get_completions_for_typedef(
        &self,
        type_def: &crate::type_checking::type_def::TypeDef,
    ) -> Vec<CompletionItem> {
        type_def
            .members
            .iter()
            .filter_map(|(name, member)| {
                let (kind, detail) = match member {
                    TypeMember::Method(_) | TypeMember::MethodRequirement(_) => {
                        (CompletionItemKind::METHOD, format!("{:?}", member.ty()))
                    }
                    TypeMember::Property(_) => {
                        (CompletionItemKind::PROPERTY, format!("{:?}", member.ty()))
                    }
                    TypeMember::Variant(_) => (
                        CompletionItemKind::ENUM_MEMBER,
                        format!("{:?}", member.ty()),
                    ),
                    _ => return None,
                };

                Some(CompletionItem {
                    label: name.clone(),
                    kind: Some(kind),
                    detail: Some(detail),
                    ..Default::default()
                })
            })
            .collect()
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
            .phase_data
            .scope_tree
            .find_scope_at(self.position.into())
        {
            for symbol_id in self
                .source_file
                .phase_data
                .scope_tree
                .get_symbols_in_scope(scope)
            {
                if let Some(symbol_info) = self.driver.symbol_table.get(&symbol_id) {
                    let kind = match symbol_info.kind {
                        SymbolKind::FuncDef => CompletionItemKind::FUNCTION,
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
    use std::path::Path;

    use async_lsp::lsp_types::{CompletionItem, Position};
    use indoc::formatdoc;

    use crate::{compiling::driver::Driver, lsp::completion::CompletionContext};

    fn complete(
        files: Vec<&str>,
        position: Position,
        is_member_lookup: bool,
    ) -> Vec<CompletionItem> {
        let mut driver = Driver::new("CompletionTests", Default::default());
        for (i, file) in files.iter().enumerate() {
            driver.update_file(&(&format!("./file-{i}.tlk")).into(), file.to_string());
        }

        let checked = driver.check();
        let checked_unit = checked.first().unwrap();
        let source_file = checked_unit.source_file(Path::new("./file-0.tlk")).unwrap();
        let env = &checked_unit.env.clone();

        CompletionContext {
            driver: &driver,
            source_file,
            position,
            is_member_lookup,
            env,
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

        assert_eq!(completions.len(), 1, "{completions:?}");
        assert_eq!(completions[0].label, "bar");
    }

    #[test]
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
