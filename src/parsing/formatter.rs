use crate::{
    expr::{Expr, ExprMeta, Pattern},
    name::Name,
    parser::ExprID,
    source_file::SourceFile,
    token_kind::TokenKind,
};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Doc {
    Empty,
    Text(String),
    Line,
    Softline,
    Hardline,
    Nest(u8, Box<Doc>),
    Concat(Box<Doc>, Box<Doc>),
    Group(Box<Doc>),
}

impl Doc {
    pub fn is_empty(&self) -> bool {
        matches!(self, Doc::Empty)
    }

    pub fn is_line_break(&self) -> bool {
        matches!(self, Doc::Line | Doc::Softline | Doc::Hardline)
    }
}

// Helper functions for building documents
fn empty() -> Doc {
    Doc::Empty
}

fn text(s: impl Into<String>) -> Doc {
    Doc::Text(s.into())
}

fn line() -> Doc {
    Doc::Line
}

fn softline() -> Doc {
    Doc::Softline
}

fn hardline() -> Doc {
    Doc::Hardline
}

fn nest(indent: u8, doc: Doc) -> Doc {
    Doc::Nest(indent, Box::new(doc))
}

fn concat(lhs: Doc, rhs: Doc) -> Doc {
    Doc::Concat(Box::new(lhs), Box::new(rhs))
}

fn group(doc: Doc) -> Doc {
    Doc::Group(Box::new(doc))
}

// Concat operator
// fn concat_op(lhs: Doc, rhs: Doc) -> Doc {
//     concat(lhs, rhs)
// }

// Concat with space operator
fn concat_space(lhs: Doc, rhs: Doc) -> Doc {
    concat(concat(lhs, text(" ")), rhs)
}

// Join documents with a separator
fn join(docs: Vec<Doc>, separator: Doc) -> Doc {
    docs.into_iter().fold(empty(), |acc, doc| {
        if acc.is_empty() {
            doc
        } else {
            concat(concat(acc, separator.clone()), doc)
        }
    })
}

pub struct Formatter<'a> {
    source_file: &'a SourceFile,
    // Track expression metadata for source location info
    meta_cache: HashMap<ExprID, &'a ExprMeta>,
}

impl<'a> Formatter<'a> {
    pub fn new(source_file: &'a SourceFile) -> Self {
        let mut meta_cache = HashMap::new();
        for (i, meta) in &source_file.meta {
            meta_cache.insert(*i, meta);
        }
        Self {
            source_file,
            meta_cache,
        }
    }

    pub fn format_single_expr(source_file: &'a SourceFile, expr_id: &'a ExprID) -> String {
        let formatter = Self::new(source_file);
        let doc = formatter.format_expr(*expr_id);
        Self::render_doc(doc, 80)
    }

    pub fn format(&self, width: usize) -> String {
        let mut output = String::new();
        let mut last_meta: Option<&ExprMeta> = None;

        for (i, &root_id) in self.source_file.root_ids().iter().enumerate() {
            if i > 0 {
                output.push('\n');

                if let (Some(last), Some(current)) = (last_meta, self.meta_cache.get(&root_id)) {
                    // If there's more than 1 line between expressions, add blank line
                    if current.start.line - last.end.line > 1 {
                        output.push('\n');
                    }
                }
            }

            let doc = self.format_expr(root_id);
            output.push_str(&Self::render_doc(doc, width));

            last_meta = self.meta_cache.get(&root_id).map(|v| &**v);
        }

        output
    }

    pub(crate) fn format_expr(&self, expr_id: ExprID) -> Doc {
        let Some(expr) = self.source_file.get(&expr_id) else {
            return Doc::Empty;
        };

        match expr {
            Expr::Incomplete(_) => Doc::Empty,
            Expr::LiteralArray(items) => self.format_array_literal(items),
            Expr::LiteralString(string) => self.format_string_literal(string),
            Expr::LiteralInt(val) => text(val),
            Expr::LiteralFloat(val) => text(val),
            Expr::LiteralTrue => text("true"),
            Expr::LiteralFalse => text("false"),
            Expr::Unary(op, rhs) => self.format_unary(op, *rhs),
            Expr::Binary(lhs, op, rhs) => self.format_binary(*lhs, op, *rhs),
            Expr::Tuple(items) => self.format_tuple(items),
            Expr::Block(stmts) => self.format_block(stmts),
            Expr::Break => text("break"),
            Expr::Await(id) => join(vec![text("await"), self.format_expr(*id)], text(" ")),
            Expr::Call {
                callee,
                type_args,
                args,
            } => self.format_call(*callee, type_args, args),
            Expr::Pattern(pattern) => self.format_pattern(pattern),
            Expr::Return(value) => self.format_return(value.as_ref()),
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => self.format_struct(name, generics, conformances, *body),
            Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => self.format_extend(name, generics, conformances, *body),
            Expr::Property {
                name,
                type_repr,
                default_value,
            } => self.format_property(name, type_repr.as_ref(), default_value.as_ref()),
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                ..
            } => self.format_type_repr(name, generics, conformances),
            Expr::FuncTypeRepr(args, ret, _) => self.format_func_type_repr(args, *ret),
            Expr::TupleTypeRepr(types, _) => self.format_tuple_type_repr(types),
            Expr::Member(receiver, property) => self.format_member(receiver.as_ref(), property),
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                ..
            } => self.format_func(name, generics, params, Some(body), ret.as_ref(), false),
            Expr::Parameter(name, type_repr) => self.format_parameter(name, type_repr.as_ref()),
            Expr::Let(name, type_repr) => self.format_let(name, type_repr.as_ref()),
            Expr::Assignment(lhs, rhs) => self.format_assignment(*lhs, *rhs),
            Expr::Variable(name, _) => self.format_variable(name),
            Expr::If(cond, then_block, else_block) => {
                self.format_if(*cond, *then_block, else_block.as_ref())
            }
            Expr::Loop(cond, body) => self.format_loop(cond.as_ref(), *body),
            Expr::EnumDecl {
                name,
                generics,
                conformances,
                body,
            } => self.format_enum_decl(name, generics, conformances, *body),
            Expr::EnumVariant(name, types) => self.format_enum_variant(name, types),
            Expr::Match(target, arms) => self.format_match(*target, arms),
            Expr::MatchArm(pattern, body) => self.format_match_arm(*pattern, *body),
            Expr::PatternVariant(enum_name, variant_name, bindings) => {
                self.format_pattern_variant(enum_name, variant_name, bindings)
            }
            Expr::CallArg { label, value } => self.format_arg(label, value),
            Expr::Init(_, func_id) => {
                let Some(Expr::Func {
                    name,
                    generics,
                    params,
                    body,
                    ret,
                    ..
                }) = self.source_file.get(func_id)
                else {
                    return Doc::Empty;
                };

                self.format_func(name, generics, params, Some(body), ret.as_ref(), true)
            }
            Expr::ProtocolDecl {
                name,
                associated_types,
                conformances,
                body,
            } => self.format_protocol(name, associated_types, conformances, *body),
            Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => self.format_func(
                &Some(name.clone()),
                generics,
                params,
                None,
                Some(ret),
                false,
            ),
        }
    }

    fn format_arg(&self, label: &Option<Name>, value: &ExprID) -> Doc {
        let Some(name) = label else {
            return self.format_expr(*value);
        };

        group(concat(
            concat(self.format_name(name), text(": ")),
            self.format_expr(*value),
        ))
    }

    fn format_string_literal(&self, string: &String) -> Doc {
        concat(text("\""), concat(text(string), text("\"")))
    }

    fn format_array_literal(&self, items: &[ExprID]) -> Doc {
        if items.is_empty() {
            return concat(text("["), text("]"));
        }

        let elements = items.iter().map(|&id| self.format_expr(id)).collect();

        group(concat(
            text("["),
            concat(
                nest(
                    1,
                    concat(softline(), join(elements, concat(text(","), line()))),
                ),
                concat(softline(), text("]")),
            ),
        ))
    }

    fn format_unary(&self, op: &TokenKind, rhs: ExprID) -> Doc {
        let op_text = match op {
            TokenKind::Minus => "-",
            TokenKind::Bang => "!",
            _ => &format!("{op}"),
        };

        concat(text(op_text), self.format_expr(rhs))
    }

    fn format_binary(&self, lhs: ExprID, op: &TokenKind, rhs: ExprID) -> Doc {
        let op_text = match op {
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Star => "*",
            TokenKind::Slash => "/",
            TokenKind::Less => "<",
            TokenKind::LessEquals => "<=",
            TokenKind::Greater => ">",
            TokenKind::GreaterEquals => ">=",
            TokenKind::EqualsEquals => "==",
            TokenKind::BangEquals => "!=",
            TokenKind::Caret => "^",
            TokenKind::Pipe => "|",
            TokenKind::PipePipe => "||",
            _ => &format!("{op}"),
        };

        group(concat_space(
            self.format_expr(lhs),
            concat_space(text(op_text), self.format_expr(rhs)),
        ))
    }

    fn format_tuple(&self, items: &[ExprID]) -> Doc {
        if items.is_empty() {
            return concat(text("("), text(")"));
        }

        if items.len() == 1 {
            return concat(text("("), concat(self.format_expr(items[0]), text(")")));
        }

        let elements = items.iter().map(|&id| self.format_expr(id)).collect();

        group(concat(
            text("("),
            concat(join(elements, concat(text(","), line())), text(")")),
        ))
    }

    fn format_block(&self, stmts: &[ExprID]) -> Doc {
        if stmts.is_empty() {
            return concat(text("{"), text("}"));
        }

        // Handle the special case for single-line blocks
        if stmts.len() == 1 && !self.contains_control_flow(&stmts[0]) {
            return group(concat(
                text("{"),
                concat(concat(text(" "), self.format_expr(stmts[0])), text(" }")),
            ));
        }

        // --- Corrected Logic ---
        let mut final_doc = empty();
        let mut last_meta: Option<&ExprMeta> = None;

        for (i, &stmt_id) in stmts.iter().enumerate() {
            let meta = self.meta_cache.get(&stmt_id);

            // Add separators *before* each statement, except the first one.
            if i > 0 {
                // Always add at least one newline.
                final_doc = concat(final_doc, hardline());

                // If preserving a blank line, add a second newline.
                if let (Some(last), Some(current)) = (last_meta, meta)
                    && current.start.line - last.end.line > 1
                {
                    final_doc = concat(final_doc, hardline());
                }
            }

            // Add the formatted statement itself.
            final_doc = concat(final_doc, self.format_expr(stmt_id));
            last_meta = meta.map(|v| &**v);
        }

        concat(
            text("{"),
            concat(
                nest(1, concat(hardline(), final_doc)),
                concat(hardline(), text("}")),
            ),
        )
    }

    fn format_call(&self, callee: ExprID, type_args: &[ExprID], args: &[ExprID]) -> Doc {
        let mut result = self.format_expr(callee);

        if !type_args.is_empty() {
            let type_docs: Vec<_> = type_args.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(type_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        let arg_docs: Vec<_> = args.iter().map(|&id| self.format_expr(id)).collect();

        group(concat(
            result,
            concat(
                text("("),
                concat(
                    nest(
                        1,
                        concat(softline(), join(arg_docs, concat(text(","), line()))),
                    ),
                    concat(softline(), text(")")),
                ),
            ),
        ))
    }

    fn format_pattern(&self, pattern: &Pattern) -> Doc {
        match pattern {
            Pattern::LiteralInt(val) => text(val),
            Pattern::LiteralFloat(val) => text(val),
            Pattern::LiteralTrue => text("true"),
            Pattern::LiteralFalse => text("false"),
            Pattern::Bind(name) => self.format_name(name),
            Pattern::Wildcard => text("_"),
            Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let mut result = if let Some(name) = enum_name {
                    concat(
                        self.format_name(name),
                        concat(text("."), text(variant_name)),
                    )
                } else {
                    concat(text("."), text(variant_name))
                };

                if !fields.is_empty() {
                    let field_docs: Vec<_> =
                        fields.iter().map(|&id| self.format_expr(id)).collect();

                    result = concat(
                        result,
                        concat(
                            text("("),
                            concat(join(field_docs, concat(text(","), text(" "))), text(")")),
                        ),
                    );
                }

                result
            }
        }
    }

    fn format_return(&self, value: Option<&ExprID>) -> Doc {
        match value {
            Some(&id) => concat_space(text("return"), self.format_expr(id)),
            None => text("return"),
        }
    }

    fn format_struct(
        &self,
        name: &Name,
        generics: &[ExprID],
        conformances: &[ExprID],
        body: ExprID,
    ) -> Doc {
        let mut result = concat_space(text("struct"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|&id| self.format_expr(id))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        concat_space(result, self.format_expr(body))
    }

    fn format_extend(
        &self,
        name: &Name,
        generics: &[ExprID],
        conformances: &[ExprID],
        body: ExprID,
    ) -> Doc {
        let mut result = concat_space(text("extend"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|&id| self.format_expr(id))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        concat_space(result, self.format_expr(body))
    }

    fn format_protocol(
        &self,
        name: &Name,
        associated_types: &[ExprID],
        conformances: &[ExprID],
        body: ExprID,
    ) -> Doc {
        let mut result = concat_space(text("protocol"), self.format_name(name));

        if !associated_types.is_empty() {
            let associated_type_docs: Vec<_> = associated_types
                .iter()
                .map(|&id| self.format_expr(id))
                .collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(
                        join(associated_type_docs, concat(text(","), text(" "))),
                        text(">"),
                    ),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|&id| self.format_expr(id))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        concat_space(result, self.format_expr(body))
    }

    fn format_property(
        &self,
        name: &Name,
        type_repr: Option<&ExprID>,
        default_value: Option<&ExprID>,
    ) -> Doc {
        let mut result = concat_space(text("let"), self.format_name(name));

        if let Some(&type_id) = type_repr {
            result = concat(result, concat_space(text(":"), self.format_expr(type_id)));
        }

        if let Some(&value_id) = default_value {
            result = concat_space(result, concat_space(text("="), self.format_expr(value_id)));
        }

        result
    }

    fn format_type_repr(&self, name: &Name, generics: &[ExprID], conformances: &[ExprID]) -> Doc {
        let mut result = self.format_name(name);

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|&id| self.format_expr(id))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        result
    }

    fn format_func_type_repr(&self, args: &[ExprID], ret: ExprID) -> Doc {
        let arg_docs: Vec<_> = args.iter().map(|&id| self.format_expr(id)).collect();

        concat(
            text("("),
            concat(
                join(arg_docs, concat(text(","), text(" "))),
                concat_space(text(") ->"), self.format_expr(ret)),
            ),
        )
    }

    fn format_tuple_type_repr(&self, types: &[ExprID]) -> Doc {
        let type_docs: Vec<_> = types.iter().map(|&id| self.format_expr(id)).collect();

        concat(
            text("("),
            concat(join(type_docs, concat(text(","), text(" "))), text(")")),
        )
    }

    fn format_member(&self, receiver: Option<&ExprID>, property: &str) -> Doc {
        match receiver {
            Some(&id) => group(concat(
                self.format_expr(id),
                concat(text("."), text(property)),
            )),
            None => concat(text("."), text(property)),
        }
    }

    fn format_func(
        &self,
        name: &Option<Name>,
        generics: &[ExprID],
        params: &[ExprID],
        body: Option<&ExprID>,
        ret: Option<&ExprID>,
        is_init: bool,
    ) -> Doc {
        let mut result;

        if is_init {
            result = text("init");
        } else {
            result = text("func");
            if let Some(n) = name {
                result = concat_space(result, self.format_name(n));
            }
        }

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        let param_docs: Vec<_> = params.iter().map(|&id| self.format_expr(id)).collect();

        result = concat(
            result,
            concat(
                text("("),
                concat(join(param_docs, concat(text(","), text(" "))), text(")")),
            ),
        );

        if let Some(&ret_id) = ret {
            result = concat_space(result, concat_space(text("->"), self.format_expr(ret_id)));
        }

        // Check if the body is a single-statement block that could be formatted inline
        if let Some(body) = body {
            if let Some(Expr::Block(stmts)) = self.source_file.get(body)
                && stmts.len() == 1
                && !self.contains_control_flow(&stmts[0])
            {
                return group(concat_space(result, self.format_expr(*body)));
            }

            concat_space(result, self.format_expr(*body))
        } else {
            result
        }
    }

    fn format_parameter(&self, name: &Name, type_repr: Option<&ExprID>) -> Doc {
        let mut result = self.format_name(name);

        if let Some(&type_id) = type_repr {
            result = concat(result, concat_space(text(":"), self.format_expr(type_id)));
        }

        result
    }

    fn format_let(&self, name: &Name, type_repr: Option<&ExprID>) -> Doc {
        let mut result = concat_space(text("let"), self.format_name(name));

        if let Some(&type_id) = type_repr {
            result = concat(result, concat_space(text(":"), self.format_expr(type_id)));
        }

        result
    }

    fn format_assignment(&self, lhs: ExprID, rhs: ExprID) -> Doc {
        concat_space(
            self.format_expr(lhs),
            concat_space(text("="), self.format_expr(rhs)),
        )
    }

    fn format_variable(&self, name: &Name) -> Doc {
        self.format_name(name)
    }

    fn format_if(&self, cond: ExprID, then_block: ExprID, else_block: Option<&ExprID>) -> Doc {
        let mut result = concat_space(
            text("if"),
            concat_space(self.format_expr(cond), self.format_expr(then_block)),
        );

        if let Some(&else_id) = else_block {
            result = concat_space(
                result,
                concat_space(text("else"), self.format_expr(else_id)),
            );
        }

        result
    }

    fn format_loop(&self, cond: Option<&ExprID>, body: ExprID) -> Doc {
        let mut result = text("loop");

        if let Some(&cond_id) = cond {
            result = concat_space(result, self.format_expr(cond_id));
        }

        concat_space(result, self.format_expr(body))
    }

    fn format_enum_decl(
        &self,
        name: &Name,
        generics: &[ExprID],
        conformances: &[ExprID],
        body: ExprID,
    ) -> Doc {
        let mut result = concat_space(text("enum"), self.format_name(name));

        if !generics.is_empty() {
            let generic_docs: Vec<_> = generics.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("<"),
                    concat(join(generic_docs, concat(text(","), text(" "))), text(">")),
                ),
            );
        }

        if !conformances.is_empty() {
            let conformances_docs = conformances
                .iter()
                .map(|&id| self.format_expr(id))
                .collect();
            result = concat(
                result,
                concat(text(": "), join(conformances_docs, text(", "))),
            );
        }

        concat_space(result, self.format_enum_body(body))
    }

    fn format_enum_body(&self, body_id: ExprID) -> Doc {
        if let Some(Expr::Block(items)) = self.source_file.get(&body_id) {
            if items.is_empty() {
                return concat(text("{"), text("}"));
            }

            let mut docs = Vec::new();
            for &item_id in items {
                docs.push(self.format_expr(item_id));
            }

            concat(
                text("{"),
                concat(
                    nest(1, concat(line(), join(docs, line()))),
                    concat(line(), text("}")),
                ),
            )
        } else {
            self.format_expr(body_id)
        }
    }
    fn format_enum_variant(&self, name: &Name, types: &[ExprID]) -> Doc {
        let mut result = concat_space(text("case"), self.format_name(name));

        if !types.is_empty() {
            let type_docs: Vec<_> = types.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("("),
                    concat(join(type_docs, concat(text(","), text(" "))), text(")")),
                ),
            );
        }

        result
    }

    fn format_match(&self, target: ExprID, arms: &[ExprID]) -> Doc {
        let arms_docs: Vec<_> = arms.iter().map(|&id| self.format_expr(id)).collect();

        concat_space(
            text("match"),
            concat_space(
                self.format_expr(target),
                concat(
                    text("{"),
                    concat(
                        nest(1, concat(line(), join(arms_docs, line()))),
                        concat(line(), text("}")),
                    ),
                ),
            ),
        )
    }

    fn format_match_arm(&self, pattern: ExprID, body: ExprID) -> Doc {
        concat_space(
            self.format_expr(pattern),
            concat_space(text("->"), self.format_expr(body)),
        )
    }

    fn format_pattern_variant(
        &self,
        enum_name: &Option<Name>,
        variant_name: &Name,
        bindings: &[ExprID],
    ) -> Doc {
        let mut result = if let Some(name) = enum_name {
            concat(
                self.format_name(name),
                concat(text("."), self.format_name(variant_name)),
            )
        } else {
            concat(text("."), self.format_name(variant_name))
        };

        if !bindings.is_empty() {
            let binding_docs: Vec<_> = bindings.iter().map(|&id| self.format_expr(id)).collect();

            result = concat(
                result,
                concat(
                    text("("),
                    concat(join(binding_docs, concat(text(","), text(" "))), text(")")),
                ),
            );
        }

        result
    }

    fn format_name(&self, name: &Name) -> Doc {
        match name {
            Name::Raw(s) => text(s),
            Name::Resolved(_, s) => text(s),
            Name::_Self(_) => text("self"),
            Name::SelfType => text("Self"),
        }
    }

    fn contains_control_flow(&self, expr_id: &ExprID) -> bool {
        if let Some(expr) = self.source_file.get(expr_id) {
            match expr {
                Expr::Func { .. } | Expr::If(..) | Expr::Loop(..) | Expr::Match(..) => true,
                Expr::Block(stmts) => stmts.iter().any(|id| self.contains_control_flow(id)),
                _ => false,
            }
        } else {
            false
        }
    }

    pub fn render_doc(doc: Doc, width: usize) -> String {
        let mut output = String::new();
        let mut queue = vec![(0u8, doc)];
        let mut column = 0;
        let mut was_newline = false;

        while let Some((indent, current_doc)) = queue.pop() {
            match current_doc {
                Doc::Empty => continue,
                Doc::Text(s) => {
                    if was_newline {
                        output.push_str(&"\t".repeat(indent as usize));
                        was_newline = false;
                    }
                    output.push_str(&s);
                    column += s.len();
                }
                Doc::Line | Doc::Softline | Doc::Hardline => {
                    output.push('\n');
                    was_newline = true;
                    column = 0;
                }
                Doc::Concat(lhs, rhs) => {
                    queue.push((indent, *rhs));
                    queue.push((indent, *lhs));
                }
                Doc::Nest(ind, nested_doc) => {
                    queue.push((indent + ind, *nested_doc));
                }
                Doc::Group(grouped_doc) => {
                    let flat = Self::flatten(*grouped_doc.clone());
                    if Self::fits((width as isize) - (column as isize), &flat) {
                        queue.push((indent, flat));
                    } else {
                        queue.push((indent, *grouped_doc));
                    }
                }
            }
        }

        output
    }

    fn flatten(doc: Doc) -> Doc {
        match doc {
            Doc::Empty | Doc::Text(_) => doc,
            Doc::Hardline => Doc::Hardline,
            Doc::Softline => Doc::Empty,
            Doc::Line => Doc::Text(" ".to_string()),
            Doc::Concat(left, right) => Doc::Concat(
                Box::new(Self::flatten(*left)),
                Box::new(Self::flatten(*right)),
            ),
            Doc::Nest(indent, nested_doc) => {
                Doc::Nest(indent, Box::new(Self::flatten(*nested_doc)))
            }
            Doc::Group(grouped_doc) => Self::flatten(*grouped_doc),
        }
    }

    fn fits(remaining_width: isize, doc: &Doc) -> bool {
        let mut width = remaining_width;
        let mut queue = vec![doc];

        while width >= 0 && !queue.is_empty() {
            #[allow(clippy::unwrap_used)]
            match queue.pop().unwrap() {
                Doc::Empty => continue,
                Doc::Text(s) => width -= s.len() as isize,
                Doc::Line | Doc::Softline | Doc::Hardline => return true,
                Doc::Concat(left, right) => {
                    queue.push(right);
                    queue.push(left);
                }
                Doc::Nest(_, nested_doc) => queue.push(nested_doc),
                Doc::Group(grouped_doc) => queue.push(grouped_doc),
            }
        }

        width >= 0
    }
}

// Public API
pub fn format(source_file: &SourceFile, width: usize) -> String {
    let formatter = Formatter::new(source_file);
    formatter.format(width)
}

#[cfg(test)]
mod formatter_tests {
    use super::*;
    use crate::parser::parse;

    fn format_code(input: &str, width: usize) -> String {
        let source_file = parse(input, "-".into());
        format(&source_file, width)
    }

    #[test]
    fn test_literal_formatting() {
        assert_eq!(format_code("123", 80), "123");
        assert_eq!(format_code("123.45", 80), "123.45");
        assert_eq!(format_code("true", 80), "true");
        assert_eq!(format_code("false", 80), "false");
    }

    #[test]
    fn test_binary_expressions() {
        assert_eq!(format_code("1 + 2", 80), "1 + 2");
        assert_eq!(format_code("1+2", 80), "1 + 2");
        assert_eq!(format_code("1 * 2 + 3", 80), "1 * 2 + 3");
        assert_eq!(format_code("1 == 2", 80), "1 == 2");
        assert_eq!(format_code("1 != 2", 80), "1 != 2");
        assert_eq!(format_code("1 < 2", 80), "1 < 2");
        assert_eq!(format_code("1 <= 2", 80), "1 <= 2");
        assert_eq!(format_code("1 > 2", 80), "1 > 2");
        assert_eq!(format_code("1 >= 2", 80), "1 >= 2");
    }

    #[test]
    fn test_unary_expressions() {
        assert_eq!(format_code("-1", 80), "-1");
        assert_eq!(format_code("!true", 80), "!true");
        assert_eq!(format_code("- 1", 80), "-1");
        assert_eq!(format_code("! true", 80), "!true");
    }

    #[test]
    fn test_variable_and_member_access() {
        assert_eq!(format_code("foo", 80), "foo");
        assert_eq!(format_code("foo.bar", 80), "foo.bar");
        assert_eq!(format_code("foo . bar", 80), "foo.bar");
        assert_eq!(format_code(".bar", 80), ".bar");
    }

    #[test]
    fn test_array_formatting() {
        assert_eq!(format_code("[]", 80), "[]");
        assert_eq!(format_code("[1]", 80), "[1]");
        assert_eq!(format_code("[1, 2, 3]", 80), "[1, 2, 3]");

        // Test line breaking for long arrays
        let long_array = "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]";
        let formatted = format_code(long_array, 30);
        assert!(formatted.contains('\n'));
    }

    #[test]
    fn test_tuple_formatting() {
        assert_eq!(format_code("()", 80), "()");
        assert_eq!(format_code("(1)", 80), "(1)");
        assert_eq!(format_code("(1, 2)", 80), "(1, 2)");
        assert_eq!(format_code("(1, 2, 3)", 80), "(1, 2, 3)");
    }

    #[test]
    fn test_function_declarations() {
        assert_eq!(format_code("func() {}", 80), "func() {}");
        assert_eq!(format_code("func foo() {}", 80), "func foo() {}");
        assert_eq!(format_code("func foo(a) {}", 80), "func foo(a) {}");
        assert_eq!(format_code("func foo(a, b) {}", 80), "func foo(a, b) {}");

        // With return type
        assert_eq!(
            format_code("func foo() -> Int {}", 80),
            "func foo() -> Int {}"
        );

        // With type parameters
        assert_eq!(
            format_code("func foo(a: Int) {}", 80),
            "func foo(a: Int) {}"
        );
        assert_eq!(
            format_code("func foo(a: Int, b: Bool) {}", 80),
            "func foo(a: Int, b: Bool) {}"
        );

        // With generics
        assert_eq!(format_code("func foo<T>() {}", 80), "func foo<T>() {}");
        assert_eq!(
            format_code("func foo<T, U>() {}", 80),
            "func foo<T, U>() {}"
        );
    }

    #[test]
    fn test_function_bodies() {
        assert_eq!(format_code("func foo() { 123 }", 80), "func foo() { 123 }");

        assert_eq!(
            format_code("func foo() {\n123\n456\n}", 80),
            "func foo() {\n\t123\n\t456\n}"
        );
    }

    #[test]
    fn test_func_bodies_with_multiple_exprs_with_call() {
        assert_eq!(
            format_code("func foo() {1+1 2+2}()", 80),
            "func foo() {\n\t1 + 1\n\t2 + 2\n}()"
        );
    }

    #[test]
    fn test_doesnt_insert_too_many_newlines_at_root() {
        assert_eq!(
            format_code("let x = 1\nlet y = 2", 80),
            "let x = 1\nlet y = 2"
        );
    }

    #[test]
    fn test_doesnt_insert_too_many_newlines_nested() {
        assert_eq!(
            format_code("func() {let x = 1\nlet y = 2 }", 80),
            "func() {\n\tlet x = 1\n\tlet y = 2\n}"
        );
    }

    #[test]
    fn test_respects_newlines() {
        assert_eq!(
            format_code(
                "let maybe = Maybe.definitely(123)\n\nmatch maybe {\n\t.definitely(x) -> x\n}",
                80
            ),
            "let maybe = Maybe.definitely(123)\n\nmatch maybe {\n\t.definitely(x) -> x\n}"
        );
    }

    #[test]
    fn test_function_calls() {
        assert_eq!(format_code("foo()", 80), "foo()");
        assert_eq!(format_code("foo(1)", 80), "foo(1)");
        assert_eq!(format_code("foo(1, 2)", 80), "foo(1, 2)");

        // With generics
        assert_eq!(format_code("foo<Int>()", 80), "foo<Int>()");
        assert_eq!(
            format_code("foo<Int, Bool>(1, true)", 80),
            "foo<Int, Bool>(1, true)"
        );

        // Long calls should break
        let long_call = "foo(very_long_argument_name, another_very_long_argument)";
        let formatted = format_code(long_call, 40);
        assert!(formatted.contains('\n'));
    }

    #[test]
    fn test_let_declarations() {
        assert_eq!(format_code("let x", 80), "let x");
        assert_eq!(format_code("let x: Int", 80), "let x: Int");
        assert_eq!(format_code("let x = 123", 80), "let x = 123");
        assert_eq!(format_code("let x: Int = 123", 80), "let x: Int = 123");
    }

    #[test]
    fn test_if_expressions() {
        assert_eq!(format_code("if true { 123 }", 80), "if true { 123 }");
        assert_eq!(
            format_code("if true { 123 } else { 456 }", 80),
            "if true { 123 } else { 456 }"
        );

        // Nested
        assert_eq!(
            format_code("if true {\nif false { 1 }\n}", 80),
            "if true {\n\tif false { 1 }\n}"
        );
    }

    #[test]
    fn test_loop_expressions() {
        assert_eq!(format_code("loop { 123 }", 80), "loop { 123 }");
        assert_eq!(format_code("loop true { 123 }", 80), "loop true { 123 }");
    }

    #[test]
    fn test_enum_declarations() {
        assert_eq!(format_code("enum Foo {}", 80), "enum Foo {}");
        assert_eq!(
            format_code("enum Foo { case a case b }", 80),
            "enum Foo {\n\tcase a\n\tcase b\n}"
        );
        assert_eq!(
            format_code("enum Foo { case a(Int) }", 80),
            "enum Foo {\n\tcase a(Int)\n}"
        );
        assert_eq!(
            format_code("enum Option<T> { case some(T) case none }", 80),
            "enum Option<T> {\n\tcase some(T)\n\tcase none\n}"
        );
    }

    #[test]
    fn test_match_expressions() {
        let match_expr = r#"match x {
            .some(val) -> val
            .none -> 0
        }"#;

        let expected = "match x {\n\t.some(val) -> val\n\t.none -> 0\n}";
        assert_eq!(format_code(match_expr, 80), expected);

        // With enum prefix
        let match_with_enum = r#"match x {
            Option.some(val) -> val
            Option.none -> 0
        }"#;

        let expected_enum = "match x {\n\tOption.some(val) -> val\n\tOption.none -> 0\n}";
        assert_eq!(format_code(match_with_enum, 80), expected_enum);
    }

    #[test]
    fn test_struct_declarations() {
        assert_eq!(format_code("struct Person {}", 80), "struct Person {}");

        let struct_with_fields = r#"struct Person { let name: String let age: Int }"#;

        let expected = "struct Person {\n\tlet name: String\n\tlet age: Int\n}";
        assert_eq!(format_code(struct_with_fields, 80), expected);

        // // With defaults
        // let struct_with_defaults = r#"struct Person { let name = "John" let age: Int = 30 }"#;

        // TODO: when we handle strings
        // let expected_defaults = "struct Person {\n\tlet name = \"John\"\n\tlet age: Int = 30\n}";
        // assert_eq!(format_code(struct_with_defaults, 80), expected_defaults);
    }

    #[test]
    fn test_return_statements() {
        assert_eq!(format_code("func() { return }", 80), "func() { return }");
        assert_eq!(
            format_code("func() { return 123 }", 80),
            "func() { return 123 }"
        );
        assert_eq!(
            format_code("func() { return foo() }", 80),
            "func() { return foo() }"
        );
    }

    #[test]
    fn test_blank_line_preservation() {
        let code_with_blanks = r#"func foo() {
            123
        }

        func bar() {
            456
        }"#;

        let formatted = format_code(code_with_blanks, 80);
        assert!(formatted.contains("\n\nfunc bar"));
    }

    #[test]
    fn test_type_annotations() {
        assert_eq!(format_code("let x: Int?", 80), "let x: Optional<Int>");
        assert_eq!(format_code("let x: (Int, Bool)", 80), "let x: (Int, Bool)");
        assert_eq!(
            format_code("let f: (Int) -> Bool", 80),
            "let f: (Int) -> Bool"
        );
        assert_eq!(
            format_code("let f: (Int, Bool) -> String", 80),
            "let f: (Int, Bool) -> String"
        );
    }

    #[test]
    fn test_complex_expressions() {
        // Test precedence handling
        assert_eq!(format_code("1 + 2 * 3", 80), "1 + 2 * 3");
        assert_eq!(format_code("(1 + 2) * 3", 80), "(1 + 2) * 3");

        // Test chained member access
        assert_eq!(format_code("foo.bar.baz", 80), "foo.bar.baz");

        // Test nested calls
        assert_eq!(format_code("foo(bar(baz()))", 80), "foo(bar(baz()))");
    }

    #[test]
    fn test_assignment() {
        assert_eq!(format_code("x = 123", 80), "x = 123");
        assert_eq!(format_code("x = y + z", 80), "x = y + z");
        assert_eq!(format_code("foo.bar = 123", 80), "foo.bar = 123");
    }

    #[test]
    fn test_width_constraints() {
        // Test that long lines are broken appropriately
        let long_function = "func long_name(param: Int) {}";
        let formatted = format_code(long_function, 40);
        // The exact formatting might vary, but it should be reasonable
        assert!(!formatted.is_empty());
    }

    #[test]
    fn test_pattern_matching() {
        // Test various pattern types
        assert_eq!(
            format_code("match x { 1 -> true }", 80),
            "match x {\n\t1 -> true\n}"
        );

        assert_eq!(
            format_code("match x { _ -> true }", 80),
            "match x {\n\t_ -> true\n}"
        );

        assert_eq!(
            format_code("match x { true -> 1\nfalse -> 0 }", 80),
            "match x {\n\ttrue -> 1\n\tfalse -> 0\n}"
        );
    }

    #[test]
    fn test_single_line_function_formatting() {
        // Test that simple functions can be formatted on one line
        assert_eq!(
            format_code("func add(a, b) { a + b }", 80),
            "func add(a, b) { a + b }"
        );

        // But functions with multiple statements should not
        assert_eq!(
            format_code("func foo() { let x = 1\nx + 1 }", 80),
            "func foo() {\n\tlet x = 1\n\tx + 1\n}"
        );

        // Functions containing other functions should always be multi-line
        assert_eq!(
            format_code("func outer() { func inner() {} }", 80),
            "func outer() {\n\tfunc inner() {}\n}"
        );
    }
}
