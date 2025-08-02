use crate::{
    SymbolID,
    name::Name,
    parsed_expr::{self, IncompleteExpr, ParsedExpr},
    token_kind::TokenKind,
    type_checker::TypeError,
};

pub struct Visitor<C> {
    pub context: C,
}

#[allow(clippy::todo)]
impl<C> Visitor<C> {
    pub fn new(context: C) -> Self {
        Self { context }
    }

    pub fn visit(&mut self, parsed: ParsedExpr) -> Result<(), TypeError> {
        match parsed.expr {
            parsed_expr::Expr::Incomplete(incomplete_expr) => {
                self.visit_incomplete(&incomplete_expr)
            }
            parsed_expr::Expr::Attribute(name) => self.visit_attribute(name),
            parsed_expr::Expr::LiteralArray(parsed_exprs) => self.visit_literal_array(parsed_exprs),
            parsed_expr::Expr::LiteralInt(value) => self.visit_literal_int(&value),
            parsed_expr::Expr::LiteralFloat(value) => self.visit_literal_float(&value),
            parsed_expr::Expr::LiteralTrue => self.visit_literal_true(),
            parsed_expr::Expr::LiteralFalse => self.visit_literal_false(),
            parsed_expr::Expr::LiteralString(value) => self.visit_literal_string(value),
            parsed_expr::Expr::Unary(token_kind, rhs) => self.visit_unary(token_kind, rhs),
            parsed_expr::Expr::Binary(lhs, token_kind, rhs) => {
                self.visit_binary(lhs, token_kind, rhs)
            }
            parsed_expr::Expr::Tuple(items) => self.visit_tuple(items),
            parsed_expr::Expr::Block(items) => self.visit_block(items),
            parsed_expr::Expr::Call {
                callee,
                type_args,
                args,
            } => self.visit_call(callee, type_args, args),
            parsed_expr::Expr::ParsedPattern(pattern) => self.visit_parsed_pattern(pattern),
            parsed_expr::Expr::Return(parsed_expr) => self.visit_return(parsed_expr),
            parsed_expr::Expr::Break => self.visit_break(),
            parsed_expr::Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => self.visit_extend(name, generics, conformances, &body),
            parsed_expr::Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => self.visit_struct(name, generics, conformances, &body),
            parsed_expr::Expr::Property {
                name,
                type_repr,
                default_value,
            } => self.visit_property(name, type_repr, default_value),
            parsed_expr::Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => self.visit_type_repr(name, generics, conformances, introduces_type),
            parsed_expr::Expr::FuncTypeRepr(params, ret, introduces_type) => {
                self.visit_func_type_repr(params, ret, introduces_type)
            }
            parsed_expr::Expr::TupleTypeRepr(items, introduces_type) => {
                self.visit_tuple_type_repr(items, introduces_type)
            }
            parsed_expr::Expr::Member(Some(box receiver), name) => {
                self.visit_member(Some(&receiver), &name)
            }
            parsed_expr::Expr::Member(None, name) => self.visit_member(None, &name),
            parsed_expr::Expr::Init(symbol_id, func) => self.visit_init(symbol_id, func),
            parsed_expr::Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                attributes,
            } => self.visit_func(name, generics, params, &body, ret, captures, attributes),
            parsed_expr::Expr::Parameter(name, annotation) => {
                self.visit_parameter(name, annotation)
            }
            parsed_expr::Expr::CallArg { label, value } => self.visit_call_arg(label, value),
            parsed_expr::Expr::Let(name, annotation) => self.visit_let(name, annotation),
            parsed_expr::Expr::Assignment(lhs, rhs) => self.visit_assignment(lhs, rhs),
            parsed_expr::Expr::Variable(name) => self.visit_variable(name),
            parsed_expr::Expr::If(cond, conseq, alt) => self.visit_if(cond, conseq, alt),
            parsed_expr::Expr::Loop(cond, body) => self.visit_loop(cond, body),
            parsed_expr::Expr::EnumDecl {
                name,
                conformances,
                generics,
                body,
            } => self.visit_enum_decl(name, conformances, generics, &body),
            parsed_expr::Expr::EnumVariant(name, values) => self.visit_enum_variant(name, values),
            parsed_expr::Expr::Match(scrutinee, arms) => self.visit_match(scrutinee, arms),
            parsed_expr::Expr::MatchArm(pattern, body) => self.visit_match_arm(pattern, body),
            parsed_expr::Expr::PatternVariant(enum_name, variant_name, values) => {
                self.visit_pattern_variant(enum_name, variant_name, values)
            }
            parsed_expr::Expr::RecordLiteral(fields) => self.visit_record_literal(fields),
            parsed_expr::Expr::RecordField { label, value } => {
                self.visit_record_field(label, value)
            }
            parsed_expr::Expr::RecordTypeRepr {
                fields,
                row_var,
                introduces_type,
            } => self.visit_record_type_repr(fields, row_var, introduces_type),
            parsed_expr::Expr::RecordTypeField { label, ty } => {
                self.visit_record_type_field(label, ty)
            }
            parsed_expr::Expr::RowVariable(name) => self.visit_row_variable(name),
            parsed_expr::Expr::Spread(parsed_expr) => self.visit_spread(parsed_expr),
            parsed_expr::Expr::ProtocolDecl {
                name,
                associated_types,
                body,
                conformances,
            } => self.visit_protocol_decl(name, associated_types, &body, conformances),
            parsed_expr::Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => self.visit_func_signature(name, params, generics, ret),
            parsed_expr::Expr::Import(module_name) => self.visit_import(module_name),
        }
    }

    fn visit_incomplete(&mut self, incomplete_expr: &IncompleteExpr) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_attribute(&mut self, name: Name) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_literal_array(&mut self, parsed_exprs: Vec<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_literal_int(&mut self, value: &str) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_literal_float(&mut self, value: &str) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_literal_true(&mut self) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_literal_false(&mut self) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_literal_string(&mut self, value: String) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_unary(
        &mut self,
        token_kind: TokenKind,
        rhs: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_binary(
        &mut self,
        lhs: Box<ParsedExpr>,
        token_kind: TokenKind,
        rhs: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_tuple(&mut self, items: Vec<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_block(&mut self, items: Vec<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_call(
        &mut self,
        callee: Box<ParsedExpr>,
        type_args: Vec<ParsedExpr>,
        args: Vec<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_parsed_pattern(&mut self, pattern: parsed_expr::Pattern) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_return(&mut self, parsed_expr: Option<Box<ParsedExpr>>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_break(&mut self) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_extend(
        &mut self,
        name: Name,
        generics: Vec<ParsedExpr>,
        conformances: Vec<ParsedExpr>,
        body: &ParsedExpr,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_struct(
        &mut self,
        name: Name,
        generics: Vec<ParsedExpr>,
        conformances: Vec<ParsedExpr>,
        body: &ParsedExpr,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_property(
        &mut self,
        name: Name,
        type_repr: Option<Box<ParsedExpr>>,
        default_value: Option<Box<ParsedExpr>>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_type_repr(
        &mut self,
        name: Name,
        generics: Vec<ParsedExpr>,
        conformances: Vec<ParsedExpr>,
        introduces_type: bool,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_func_type_repr(
        &mut self,
        params: Vec<ParsedExpr>,
        ret: Box<ParsedExpr>,
        introduces_type: bool,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_tuple_type_repr(
        &mut self,
        items: Vec<ParsedExpr>,
        introduces_type: bool,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_member(&mut self, receiver: Option<&ParsedExpr>, name: &str) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_init(
        &mut self,
        symbol_id: Option<SymbolID>,
        func: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_func(
        &mut self,
        name: Option<Name>,
        generics: Vec<ParsedExpr>,
        params: Vec<ParsedExpr>,
        body: &ParsedExpr,
        ret: Option<Box<ParsedExpr>>,
        captures: Vec<SymbolID>,
        attributes: Vec<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_parameter(
        &mut self,
        name: Name,
        annotation: Option<Box<ParsedExpr>>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_call_arg(
        &mut self,
        label: Option<Name>,
        value: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_let(
        &mut self,
        name: Name,
        annotation: Option<Box<ParsedExpr>>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_assignment(
        &mut self,
        lhs: Box<ParsedExpr>,
        rhs: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_variable(&mut self, name: Name) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_if(
        &mut self,
        cond: Box<ParsedExpr>,
        conseq: Box<ParsedExpr>,
        alt: Option<Box<ParsedExpr>>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_loop(
        &mut self,
        cond: Option<Box<ParsedExpr>>,
        body: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_enum_decl(
        &mut self,
        name: Name,
        conformances: Vec<ParsedExpr>,
        generics: Vec<ParsedExpr>,
        body: &ParsedExpr,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_enum_variant(&mut self, name: Name, values: Vec<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_match(
        &mut self,
        scrutinee: Box<ParsedExpr>,
        arms: Vec<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_match_arm(
        &mut self,
        pattern: Box<ParsedExpr>,
        body: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_pattern_variant(
        &mut self,
        enum_name: Option<Name>,
        variant_name: Name,
        values: Vec<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_record_literal(&mut self, fields: Vec<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_record_field(&mut self, label: Name, value: Box<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_record_type_repr(
        &mut self,
        fields: Vec<ParsedExpr>,
        row_var: Option<Box<ParsedExpr>>,
        introduces_type: bool,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_record_type_field(
        &mut self,
        label: Name,
        ty: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_row_variable(&mut self, name: Name) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_spread(&mut self, parsed_expr: Box<ParsedExpr>) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_protocol_decl(
        &mut self,
        name: Name,
        associated_types: Vec<ParsedExpr>,
        body: &ParsedExpr,
        conformances: Vec<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_func_signature(
        &mut self,
        name: Name,
        params: Vec<ParsedExpr>,
        generics: Vec<ParsedExpr>,
        ret: Box<ParsedExpr>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn visit_import(&mut self, module_name: String) -> Result<(), TypeError> {
        todo!()
    }
}
