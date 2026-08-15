use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    ast::{AST, Parsed},
    id_generator::IDGenerator,
    label::Label,
    name::Name,
    node_id::{FileID, NodeID},
    node_kinds::{
        call_arg::{ArgMode, CallArg, CallArgOrigin},
        expr::{Expr, ExprKind, MacroToken, QuoteCategory},
    },
    span::Span,
};

/// Lower opaque `quote { ... }` nodes to calls into the Talk syntax runtime.
/// Canonical token records were captured by the parser and become constants;
/// lowering never scans the quotation text.
#[derive(Debug, VisitorMut)]
#[visitor(Expr(enter))]
pub struct LowerSyntaxQuotes {
    file_id: FileID,
    node_ids: IDGenerator,
}

impl LowerSyntaxQuotes {
    pub fn run(ast: &mut AST<Parsed>) {
        let node_ids = std::mem::take(&mut ast.node_ids);
        let mut lowerer = Self {
            file_id: ast.file_id,
            node_ids,
        };
        for root in &mut ast.roots {
            root.drive_mut(&mut lowerer);
        }
        ast.node_ids = lowerer.node_ids;
    }

    fn next_id(&mut self) -> NodeID {
        NodeID(self.file_id, self.node_ids.next_id())
    }

    fn string_contents(value: &str) -> String {
        let mut escaped = String::new();
        for ch in value.chars() {
            match ch {
                '"' => escaped.push_str("\\\""),
                '\\' => escaped.push_str("\\\\"),
                '\n' => escaped.push_str("\\n"),
                '\r' => escaped.push_str("\\r"),
                '\t' => escaped.push_str("\\t"),
                ch if ch <= '\u{1f}' => escaped.push_str(&format!("\\u{{{:x}}}", ch as u32)),
                ch => escaped.push(ch),
            }
        }
        escaped
    }

    fn variable(&mut self, name: impl Into<String>, span: Span) -> Expr {
        Expr {
            id: self.next_id(),
            kind: ExprKind::Variable(Name::Raw(name.into())),
            span,
        }
    }

    fn string(&mut self, value: &str, span: Span) -> Expr {
        Expr {
            id: self.next_id(),
            kind: ExprKind::LiteralString(Self::string_contents(value)),
            span,
        }
    }

    fn argument(&mut self, label: &str, value: Expr, mode: Option<ArgMode>, span: Span) -> CallArg {
        CallArg {
            origin: CallArgOrigin::Synthesized,
            id: self.next_id(),
            label: Label::Named(label.into()),
            label_span: Span::SYNTHESIZED,
            value,
            span,
            mode,
            mode_span: mode.map(|_| Span::SYNTHESIZED),
        }
    }

    fn call(&mut self, name: &str, args: Vec<CallArg>, span: Span) -> Expr {
        let callee = self.variable(name, span);
        Expr {
            id: self.next_id(),
            kind: ExprKind::Call {
                callee: Box::new(callee),
                type_args: Vec::new(),
                args,
                trailing_block: None,
                desugared_operator: None,
            },
            span,
        }
    }

    fn splice(&mut self, name: &str, span: Span) -> Expr {
        let name_value = self.string(name, span);
        let syntax = self.variable(name, span);
        let name_arg = self.argument("name", name_value, None, span);
        let syntax_arg = self.argument("syntax", syntax, Some(ArgMode::Consume), span);
        self.call("splice", vec![name_arg, syntax_arg], span)
    }

    fn enter_expr(&mut self, expr: &mut Expr) {
        let ExprKind::SyntaxQuote {
            source,
            tokens,
            splices,
            category,
        } = expr.kind.clone()
        else {
            return;
        };
        let span = expr.span;
        let source_id = self.variable("__talk_macro_definition_source_id", span);
        let source = self.string(&source, span);
        let encoded = self.string(&MacroToken::encode_all(&tokens), span);
        let splice_values = splices.iter().map(|name| self.splice(name, span)).collect();
        let splice_array = Expr {
            id: self.next_id(),
            kind: ExprKind::LiteralArray(splice_values),
            span,
        };
        let context = self.variable("context", span);
        let args = vec![
            self.argument("source_id", source_id, None, span),
            self.argument("source", source, None, span),
            self.argument("encoded", encoded, None, span),
            self.argument("splices", splice_array, None, span),
            self.argument("context", context, None, span),
        ];
        let entry = match category {
            QuoteCategory::Expr => "quote_expr_encoded",
            QuoteCategory::Decl => "quote_decl_encoded",
        };
        let lowered = self.call(entry, args, span);
        expr.kind = lowered.kind;
    }
}
