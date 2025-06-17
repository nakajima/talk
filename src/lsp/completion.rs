use crate::SourceFile;
use crate::Typed;
use crate::compiling::driver::Driver;
use crate::diagnostic::Position;
use crate::symbol_table::SymbolKind;
use async_lsp::lsp_types::CompletionItem;
use async_lsp::lsp_types::CompletionItemKind;

pub struct CompletionContext<'a> {
    pub driver: &'a Driver,
    pub source_file: &'a SourceFile<Typed>,
    pub position: Position,
}

impl<'a> CompletionContext<'a> {
    pub fn get_completions(&self) -> Vec<CompletionItem> {
        let mut completions = Vec::new();

        // 1. Add keywords
        completions.extend(self.get_keyword_completions());

        // 2. Add symbols from the current scope
        completions.extend(self.get_scope_completions());

        completions
    }

    fn get_keyword_completions(&self) -> Vec<CompletionItem> {
        // This can be made more context-aware
        vec!["let", "if", "else", "fn", "struct", "while", "for"]
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

        if let Some(scope) = self.source_file.scope_tree.find_scope_at(Position {
            line: self.position.line,
            col: self.position.col,
        }) {
            for symbol_id in self.source_file.scope_tree.get_symbols_in_scope(scope) {
                if let Some(symbol_info) = self.driver.symbol_table.get(&symbol_id) {
                    let kind = match symbol_info.kind {
                        SymbolKind::Func => CompletionItemKind::FUNCTION,
                        SymbolKind::Struct => CompletionItemKind::STRUCT,
                        SymbolKind::Local => CompletionItemKind::VARIABLE,
                        SymbolKind::Param => CompletionItemKind::VARIABLE,
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
