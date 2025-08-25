use crate::{
    node_id::NodeID, lexing::span::Span, span_index::SpanIndex, symbol_table::SymbolID, ty::Ty2,
};
use std::collections::HashMap;

/// Semantic information about an expression
#[derive(Debug, Clone)]
pub enum ResolvedExpr {
    Variable {
        symbol: SymbolID,
        ty: Ty2,
    },
    MemberAccess {
        receiver: NodeID,
        member_name: String,
        resolved_symbol: Option<SymbolID>,
        ty: Ty2,
    },
    FunctionCall {
        func: NodeID,
        args: Vec<NodeID>,
        ty: Ty2,
    },
    Literal {
        ty: Ty2,
    },
    TypeExpression {
        ty: Ty2,
    },
}

/// Location of a definition
#[derive(Debug, Clone)]
pub struct Location {
    pub file: std::path::PathBuf,
    pub span: Span,
}

/// Information about a type's members
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub symbol: SymbolID,
    pub members: Vec<MemberInfo>,
}

#[derive(Debug, Clone)]
pub struct MemberInfo {
    pub name: String,
    pub symbol: SymbolID,
    pub ty: Ty2,
    pub kind: MemberKind,
}

#[derive(Debug, Clone)]
pub enum MemberKind {
    Property,
    Method,
    Variant,
}

/// The semantic index stores resolved information about the program
#[derive(Debug, Default, Clone)]
pub struct SemanticIndex {
    /// Maps expression IDs to their resolved semantic information
    expressions: HashMap<NodeID, ResolvedExpr>,

    /// Maps symbols to their definition locations
    definitions: HashMap<SymbolID, Location>,

    /// Maps types to their member information
    type_info: HashMap<SymbolID, TypeInfo>,

    /// Maps expression IDs to their spans (for reverse lookup)
    expr_spans: HashMap<NodeID, Span>,

    /// Spatial index for efficient span lookups
    span_index: SpanIndex,
}

impl SemanticIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Debug method to get expression count
    pub fn expression_count(&self) -> usize {
        self.expressions.len()
    }

    /// Debug method to list member accesses
    pub fn debug_member_accesses(&self) -> Vec<(&NodeID, &str, Option<SymbolID>)> {
        let mut result = Vec::new();
        for (expr_id, expr) in &self.expressions {
            if let ResolvedExpr::MemberAccess {
                member_name,
                resolved_symbol,
                ..
            } = expr
            {
                result.push((expr_id, member_name.as_str(), *resolved_symbol));
            }
        }
        result
    }

    /// Debug method to get span count
    pub fn span_count(&self) -> usize {
        self.expr_spans.len()
    }

    /// Record semantic information about an expression
    pub fn record_expression(&mut self, expr_id: NodeID, resolved: ResolvedExpr) {
        self.expressions.insert(expr_id, resolved);
    }

    /// Record the definition location of a symbol
    pub fn record_definition(&mut self, symbol: SymbolID, location: Location) {
        self.definitions.insert(symbol, location);
    }

    /// Record type information
    pub fn record_type_info(&mut self, type_symbol: SymbolID, info: TypeInfo) {
        self.type_info.insert(type_symbol, info);
    }

    /// Record the span of an expression
    pub fn record_expr_span(&mut self, expr_id: NodeID, span: Span) {
        self.expr_spans.insert(expr_id, span.clone());
        self.span_index.insert(expr_id, span);
    }

    /// Get semantic information about an expression
    pub fn get_expression(&self, expr_id: &NodeID) -> Option<&ResolvedExpr> {
        self.expressions.get(expr_id)
    }

    /// Get the definition location of a symbol
    pub fn get_definition(&self, symbol: &SymbolID) -> Option<&Location> {
        self.definitions.get(symbol)
    }

    /// Get type information
    pub fn get_type_info(&self, type_symbol: &SymbolID) -> Option<&TypeInfo> {
        self.type_info.get(type_symbol)
    }

    /// Find expression by span (for LSP queries)
    pub fn find_expr_by_span(&self, span: Span) -> Option<NodeID> {
        // This is inefficient but works for now
        // In production, we'd want a more efficient spatial index
        self.expr_spans
            .iter()
            .find(|(_, s)| **s == span)
            .map(|(id, _)| *id)
    }

    /// Find expression containing a position
    pub fn find_expr_at_position(
        &self,
        position: &crate::diagnostic::Position,
        path: &std::path::PathBuf,
    ) -> Option<NodeID> {
        self.span_index.find_at_position(position, path)
    }

    /// Rebuild the spatial index from current spans
    /// Useful after bulk operations or when loading from cache
    pub fn rebuild_span_index(&mut self) {
        self.span_index = SpanIndex::build_from(&self.expr_spans);
    }
}

/// Query interface for the semantic index
pub trait QueryDatabase {
    /// What type does this expression have?
    fn expr_type(&self, expr: NodeID) -> Option<Ty2>;

    /// What symbol does this expression resolve to?
    fn expr_symbol(&self, expr: NodeID) -> Option<SymbolID>;

    /// Where is this symbol defined?
    fn symbol_definition(&self, symbol: SymbolID) -> Option<&Location>;

    /// What members does this type have?
    fn type_members(&self, type_symbol: SymbolID) -> Option<&[MemberInfo]>;

    /// Find the expression at a given span
    fn expr_at_span(&self, span: Span) -> Option<NodeID>;
}

impl QueryDatabase for SemanticIndex {
    fn expr_type(&self, expr: NodeID) -> Option<Ty2> {
        self.expressions.get(&expr).map(|resolved| match resolved {
            ResolvedExpr::Variable { ty, .. } => ty.clone(),
            ResolvedExpr::MemberAccess { ty, .. } => ty.clone(),
            ResolvedExpr::FunctionCall { ty, .. } => ty.clone(),
            ResolvedExpr::Literal { ty } => ty.clone(),
            ResolvedExpr::TypeExpression { ty } => ty.clone(),
        })
    }

    fn expr_symbol(&self, expr: NodeID) -> Option<SymbolID> {
        self.expressions
            .get(&expr)
            .and_then(|resolved| match resolved {
                ResolvedExpr::Variable { symbol, .. } => Some(*symbol),
                ResolvedExpr::MemberAccess {
                    resolved_symbol, ..
                } => *resolved_symbol,
                _ => None,
            })
    }

    fn symbol_definition(&self, symbol: SymbolID) -> Option<&Location> {
        self.definitions.get(&symbol)
    }

    fn type_members(&self, type_symbol: SymbolID) -> Option<&[MemberInfo]> {
        self.type_info
            .get(&type_symbol)
            .map(|info| &info.members[..])
    }

    fn expr_at_span(&self, span: Span) -> Option<NodeID> {
        self.find_expr_by_span(span)
    }
}
