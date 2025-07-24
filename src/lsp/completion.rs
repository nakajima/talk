use crate::SourceFile;
use crate::Typed;
use crate::compiling::driver::Driver;
use crate::environment::Environment;
use crate::symbol_table::SymbolKind;
use crate::type_checking::ty::Ty;
use crate::type_def::TypeMember;
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

        let type_sym = self
            .driver
            .symbol_from_position(position_before_dot.into(), &self.source_file.path)
            .and_then(|sym| {
                let info = self.driver.symbol_table.get(sym)?;

                // Attempt to find type symbol in order of precedence:
                // 1. From the symbol's definition (e.g., a variable's type).
                info.definition
                    .as_ref()
                    .and_then(|def| def.sym)
                    // 2. If the symbol itself is a type.
                    .or_else(|| self.env.lookup_type(sym).map(|_| *sym))
                    // 3. From the type of the expression the symbol is part of.
                    .or_else(|| {
                        self.source_file.typed_expr(info.expr_id).and_then(|typed| {
                            match &typed.ty {
                                Ty::Struct(id, _) | Ty::Enum(id, _) | Ty::Protocol(id, _) => {
                                    Some(*id)
                                }
                                _ => None,
                            }
                        })
                    })
            })
            // 4. Fallback for `self` keyword completion.
            .or_else(|| {
                self.env.selfs.last().and_then(|ty| match ty {
                    Ty::Struct(id, _) | Ty::Enum(id, _) | Ty::Protocol(id, _) => Some(*id),
                    _ => None,
                })
            });
        let type_sym = type_sym.or_else(|| {
            self.env.selfs.last().and_then(|ty| match ty {
                Ty::Struct(id, _) | Ty::Enum(id, _) | Ty::Protocol(id, _) => Some(*id),
                _ => None,
            })
        });

        if let Some(type_def) = type_sym.and_then(|sym| self.env.lookup_type(&sym)) {
            let mut completions = vec![];
            for (name, member) in type_def.members.iter() {
                let item = match member {
                    TypeMember::Method(_) | TypeMember::MethodRequirement(_) => CompletionItem {
                        label: name.clone(),
                        kind: Some(CompletionItemKind::METHOD),
                        detail: Some(format!("{:?}", member.ty())),
                        ..Default::default()
                    },
                    TypeMember::Property(_) => CompletionItem {
                        label: name.clone(),
                        kind: Some(CompletionItemKind::PROPERTY),
                        detail: Some(format!("{:?}", member.ty())),
                        ..Default::default()
                    },
                    TypeMember::Variant(_) => CompletionItem {
                        label: name.clone(),
                        kind: Some(CompletionItemKind::ENUM_MEMBER),
                        detail: Some(format!("{:?}", member.ty())),
                        ..Default::default()
                    },
                    _ => continue,
                };

                completions.push(item)
            }

            completions
        } else {
            tracing::error!("did not get type: {:?}", self.env.types);
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
}
