use crate::{SymbolID, diagnostic::Position, span::Span};

// A unique identifier for a scope
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ScopeId(pub usize);

// Represents a single lexical scope in the source code (e.g., a block, a function body)
#[derive(Debug, Default, Eq, PartialEq, Hash, Clone)]
pub struct Scope {
    pub id: ScopeId,
    pub parent: Option<ScopeId>, // The scope that contains this one
    pub span: Span,              // The region of code this scope covers

    // Symbols defined directly in this scope
    symbols: Vec<SymbolID>,
}

// The data structure that holds all scopes for a file
#[derive(Debug, Default, Eq, PartialEq, Hash, Clone)]
pub struct ScopeTree {
    scopes: Vec<Scope>,
}

impl ScopeTree {
    /// Creates a new scope, setting its parent to the provided `parent_id`.
    /// Returns the ID of the newly created scope.
    pub fn new_scope(&mut self, parent_id: Option<ScopeId>, span: Span) -> ScopeId {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope {
            id,
            parent: parent_id,
            span,
            symbols: Vec::new(),
        });
        id
    }

    /// Adds a symbol definition to a specific scope.
    pub fn add_symbol_to_scope(&mut self, scope_id: ScopeId, symbol_id: SymbolID) {
        if let Some(scope) = self.scopes.get_mut(scope_id.0) {
            scope.symbols.push(symbol_id);
        }
    }

    /// Finds the most specific (inner-most) scope that contains the given position.
    pub fn find_scope_at(&self, position: Position) -> Option<ScopeId> {
        let mut most_specific_scope: Option<ScopeId> = None;

        for (i, scope) in self.scopes.iter().enumerate() {
            if scope.span.contains(&position) {
                // This scope contains the position. Is it more specific than the last one we found?
                if let Some(current_best_id) = most_specific_scope {
                    let current_best_scope = &self.scopes[current_best_id.0];
                    // If the current scope is contained within the previous best, it's more specific.
                    if current_best_scope.span.contains_span(&scope.span) {
                        most_specific_scope = Some(ScopeId(i));
                    }
                } else {
                    // This is the first scope we've found that contains the position.
                    most_specific_scope = Some(ScopeId(i));
                }
            }
        }
        most_specific_scope
    }

    /// Collects all symbols that are visible from a given scope, walking
    /// up the tree to include symbols from all parent scopes.
    pub fn get_symbols_in_scope(&self, scope_id: ScopeId) -> Vec<SymbolID> {
        let mut visible_symbols = Vec::new();
        let mut current_scope_id = Some(scope_id);

        while let Some(id) = current_scope_id {
            if let Some(scope) = self.scopes.get(id.0) {
                visible_symbols.extend(&scope.symbols);
                current_scope_id = scope.parent;
            } else {
                break;
            }
        }
        visible_symbols
    }
}
