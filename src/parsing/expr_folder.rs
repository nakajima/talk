use std::rc::Rc;

use crate::{
    SymbolID,
    expr::{Expr, Pattern},
    name::Name,
    parser::ExprID,
    token_kind::TokenKind,
};

pub trait ExprFolder<'a> {
    fn get(&self, expr_id: &ExprID) -> Rc<Expr>;
    fn get_mult(&self, expr_ids: &Vec<ExprID>) -> Vec<Rc<Expr>> {
        expr_ids.iter().map(|i| self.get(i)).collect()
    }

    fn fold_mult(&mut self, expr_ids: &Vec<ExprID>) -> Vec<Rc<Expr>> {
        expr_ids.iter().map(|i| self.fold(i)).collect()
    }

    fn fold(&mut self, expr_id: &ExprID) -> Rc<Expr> {
        let expr = self.get(expr_id);
        use super::expr::Expr::*;
        let folded = match expr.as_ref() {
            LiteralArray(items) => self._fold_literal_array(expr.clone(), items),
            LiteralInt(val) => self._fold_int(expr.clone(), val),
            LiteralFloat(val) => self._fold_float(expr.clone(), val),
            LiteralTrue => self._fold_true(expr),
            LiteralFalse => self._fold_false(expr),
            Unary(token_kind, rhs) => self._fold_unary(expr.clone(), token_kind, rhs),
            Binary(lhs, token_kind, rhs) => self._fold_binary(expr.clone(), lhs, token_kind, rhs),
            Tuple(items) => self._fold_tuple(expr.clone(), items),
            Block(items) => self._fold_block(expr.clone(), items),
            Call {
                callee,
                type_args,
                args,
            } => self._fold_call(expr.clone(), callee, type_args, args),
            Pattern(pattern) => self._fold_pattern(expr.clone(), &pattern.clone()),
            Return(rhs) => self._fold_return(expr.clone(), rhs),
            Break => self._fold_break(expr),
            Struct(name, items, body) => self._fold_struct(expr.clone(), name, items, body),
            Property {
                name,
                type_repr,
                default_value,
            } => self._fold_property(expr.clone(), &name.clone(), type_repr, default_value),
            TypeRepr(name, items, introduces_type) => {
                self._fold_type_repr(expr.clone(), name, items, introduces_type)
            }
            FuncTypeRepr(items, ret, introduces_type) => {
                self._fold_func_type_repr(expr.clone(), items, ret, introduces_type)
            }
            TupleTypeRepr(items, introduces_type) => {
                self._fold_type_type_repr(expr.clone(), items, introduces_type)
            }
            Member(receiver, name) => self._fold_member(expr.clone(), receiver, name),
            Init(symbol_id, func_id) => self._fold_init(expr.clone(), symbol_id, func_id),
            Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
            } => self._fold_function(expr.clone(), name, generics, params, body, ret, captures),
            Parameter(name, type_repr) => self._fold_parameter(expr.clone(), name, type_repr),
            CallArg { label, value } => self._fold_call_arg(expr.clone(), label, value),
            Let(name, _) => self._fold_let(expr.clone(), name),
            Assignment(lhs, rhs) => self._fold_assignment(expr.clone(), lhs, rhs),
            Variable(name, _) => self._fold_variable(expr.clone(), name),
            If(cond, then, alt) => self._fold_if(expr.clone(), cond, then, alt),
            Loop(cond, body) => self._fold_loop(expr.clone(), cond, body),
            EnumDecl(name, items, body) => self._fold_enum_decl(expr.clone(), name, items, body),
            EnumVariant(name, items) => self._fold_enum_variant(expr.clone(), name, items),
            Match(pattern, items) => self._fold_match(expr.clone(), pattern, items),
            MatchArm(pattern, body) => self._fold_match_arm(expr.clone(), pattern, body),
            PatternVariant(enum_name, variant_name, items) => {
                self._fold_pattern_variable(expr.clone(), enum_name, variant_name, items)
            }
            ProtocolDecl {
                name,
                associated_types,
                body,
            } => self._fold_protocol_decl(expr.clone(), name, associated_types, body),
            FuncSignature {
                name,
                params,
                generics,
                ret,
            } => self._fold_func_signature(expr.clone(), name, params, generics, ret),
        };

        self.on_expr(*expr_id, folded)
    }

    fn on_expr(&mut self, _expr_id: ExprID, expr: Rc<Expr>) -> Rc<Expr> {
        expr
    }

    fn on_literal_array(&mut self, expr: Rc<Expr>, _items: Vec<Rc<Expr>>) -> Rc<Expr> {
        expr
    }

    fn _fold_literal_array(&mut self, expr: Rc<Expr>, items: &Vec<ExprID>) -> Rc<Expr> {
        let items = items.iter().map(|i| self.fold(i)).collect();
        self.on_literal_array(expr, items)
    }

    fn on_int(&mut self, expr: Rc<Expr>, _val: &String) -> Rc<Expr> {
        expr
    }
    fn _fold_int(&mut self, expr: Rc<Expr>, val: &String) -> Rc<Expr> {
        self.on_int(expr, val)
    }

    fn on_float(&mut self, expr: Rc<Expr>, _val: &String) -> Rc<Expr> {
        expr
    }
    fn _fold_float(&mut self, expr: Rc<Expr>, val: &String) -> Rc<Expr> {
        self.on_float(expr, val)
    }

    fn on_true(&mut self, expr: Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_true(&mut self, expr: Rc<Expr>) -> Rc<Expr> {
        self.on_true(expr)
    }

    fn on_false(&mut self, expr: Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_false(&mut self, expr: Rc<Expr>) -> Rc<Expr> {
        self.on_false(expr)
    }

    fn on_unary(&mut self, expr: Rc<Expr>, _token_kind: &TokenKind, _rhs: Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_unary(&mut self, expr: Rc<Expr>, token_kind: &TokenKind, rhs: &ExprID) -> Rc<Expr> {
        let rhs = self.fold(rhs);
        self.on_unary(expr, token_kind, rhs)
    }

    fn on_binary(
        &mut self,
        expr: Rc<Expr>,
        _lhs: Rc<Expr>,
        _token_kind: &TokenKind,
        _rhs: Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_binary(
        &mut self,
        expr: Rc<Expr>,
        lhs: &ExprID,
        token_kind: &TokenKind,
        rhs: &ExprID,
    ) -> Rc<Expr> {
        let lhs = self.fold(lhs);
        let rhs = self.fold(rhs);
        self.on_binary(expr, lhs, token_kind, rhs)
    }

    fn on_tuple(&mut self, expr: Rc<Expr>, _items: Vec<Rc<Expr>>) -> Rc<Expr> {
        expr
    }
    fn _fold_tuple(&mut self, expr: Rc<Expr>, items: &Vec<ExprID>) -> Rc<Expr> {
        let items = self.fold_mult(items);
        self.on_tuple(expr, items)
    }

    fn on_block(&mut self, expr: Rc<Expr>, _items: Vec<Rc<Expr>>) -> Rc<Expr> {
        expr
    }
    fn _fold_block(&mut self, expr: Rc<Expr>, items: &Vec<ExprID>) -> Rc<Expr> {
        let items = self.fold_mult(items);
        self.on_block(expr, items)
    }

    fn on_call(
        &mut self,
        expr: Rc<Expr>,
        _callee: Rc<Expr>,
        _type_args: Vec<Rc<Expr>>,
        _args: Vec<Rc<Expr>>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_call(
        &mut self,
        expr: Rc<Expr>,
        callee: &ExprID,
        type_args: &Vec<ExprID>,
        args: &Vec<ExprID>,
    ) -> Rc<Expr> {
        let callee = self.fold(callee);
        let type_args = self.fold_mult(type_args);
        let args = self.fold_mult(args);
        self.on_call(expr, callee, type_args, args)
    }

    fn on_pattern(&mut self, expr: Rc<Expr>, _pattern: &Pattern) -> Rc<Expr> {
        expr
    }
    fn _fold_pattern(&mut self, expr: Rc<Expr>, pattern: &Pattern) -> Rc<Expr> {
        self.on_pattern(expr, pattern)
    }

    fn on_return(&mut self, expr: Rc<Expr>, _rhs: &Option<Rc<Expr>>) -> Rc<Expr> {
        expr
    }
    fn _fold_return(&mut self, expr: Rc<Expr>, rhs: &Option<ExprID>) -> Rc<Expr> {
        let rhs = rhs.map(|i| self.fold(&i));
        self.on_return(expr, &rhs)
    }

    fn on_break(&mut self, expr: Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_break(&mut self, expr: Rc<Expr>) -> Rc<Expr> {
        expr
    }

    fn on_struct(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _items: Vec<Rc<Expr>>,
        _body: Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_struct(
        &mut self,

        expr: Rc<Expr>,
        name: &Name,
        items: &Vec<ExprID>,
        body: &ExprID,
    ) -> Rc<Expr> {
        let body = self.fold(body);
        let items = self.fold_mult(items);
        self.on_struct(expr, name, items, body)
    }

    fn on_property(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _type_repr: &Option<Rc<Expr>>,
        _default_value: &Option<Rc<Expr>>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_property(
        &mut self,
        expr: Rc<Expr>,
        name: &Name,
        type_repr: &Option<ExprID>,
        default_value: &Option<ExprID>,
    ) -> Rc<Expr> {
        let type_repr = type_repr.map(|i| self.fold(&i));
        let default_value = default_value.map(|i| self.fold(&i));
        self.on_property(expr, name, &type_repr, &default_value)
    }

    fn on_type_repr(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _items: Vec<Rc<Expr>>,
        _introduces_type: &bool,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_type_repr(
        &mut self,
        expr: Rc<Expr>,
        name: &Name,
        items: &Vec<ExprID>,
        introduces_type: &bool,
    ) -> Rc<Expr> {
        let items = self.fold_mult(items);
        self.on_type_repr(expr, name, items, introduces_type)
    }

    fn on_func_type_repr(
        &mut self,
        expr: Rc<Expr>,
        _items: Vec<Rc<Expr>>,
        _ret: Rc<Expr>,
        _introduces_type: &bool,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_func_type_repr(
        &mut self,

        expr: Rc<Expr>,
        items: &Vec<ExprID>,
        ret: &ExprID,
        introduces_type: &bool,
    ) -> Rc<Expr> {
        let items = self.fold_mult(items);
        let ret = self.fold(ret);
        self.on_func_type_repr(expr, items, ret, introduces_type)
    }

    fn on_type_type_repr(
        &mut self,
        expr: Rc<Expr>,
        _items: Vec<Rc<Expr>>,
        _introduces_type: &bool,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_type_type_repr(
        &mut self,
        expr: Rc<Expr>,
        items: &Vec<ExprID>,
        introduces_type: &bool,
    ) -> Rc<Expr> {
        let items = self.fold_mult(items);
        self.on_type_type_repr(expr, items, introduces_type)
    }

    fn on_init(
        &mut self,
        expr: Rc<Expr>,
        _symbol_id: &Option<SymbolID>,
        _func: Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_init(
        &mut self,
        expr: Rc<Expr>,
        symbol_id: &Option<SymbolID>,
        func_id: &ExprID,
    ) -> Rc<Expr> {
        let func = self.fold(func_id);
        self.on_init(expr, symbol_id, func)
    }

    fn on_function(
        &mut self,
        expr: Rc<Expr>,
        _name: &Option<Name>,
        _generics: Vec<Rc<Expr>>,
        _params: Vec<Rc<Expr>>,
        _body: Rc<Expr>,
        _ret: Option<Rc<Expr>>,
        _captures: Vec<SymbolID>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_function(
        &mut self,

        expr: Rc<Expr>,
        name: &Option<Name>,
        generics: &Vec<ExprID>,
        params: &Vec<ExprID>,
        body: &ExprID,
        ret: &Option<ExprID>,
        captures: &Vec<SymbolID>,
    ) -> Rc<Expr> {
        let generics = self.fold_mult(generics);
        let params = self.fold_mult(params);
        let body = self.fold(body);
        let ret = ret.map(|i| self.fold(&i));
        self.on_function(expr, name, generics, params, body, ret, captures.clone())
    }

    fn on_parameter(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _type_repr: &Option<Rc<Expr>>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_parameter(
        &mut self,
        expr: Rc<Expr>,
        name: &Name,
        type_repr: &Option<ExprID>,
    ) -> Rc<Expr> {
        let type_repr = type_repr.map(|i| self.fold(&i));
        self.on_parameter(expr, name, &type_repr)
    }

    fn on_call_arg(
        &mut self,
        expr: Rc<Expr>,
        _label: &Option<Name>,
        _value: &Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_call_arg(&mut self, expr: Rc<Expr>, label: &Option<Name>, value: &ExprID) -> Rc<Expr> {
        let value = self.fold(value);
        self.on_call_arg(expr, label, &value)
    }

    fn on_let(&mut self, expr: Rc<Expr>, _name: &Name) -> Rc<Expr> {
        expr
    }
    fn _fold_let(&mut self, expr: Rc<Expr>, name: &Name) -> Rc<Expr> {
        self.on_let(expr, name)
    }

    fn on_assignment(&mut self, expr: Rc<Expr>, _lhs: &Rc<Expr>, _rhs: &Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_assignment(&mut self, expr: Rc<Expr>, lhs: &ExprID, rhs: &ExprID) -> Rc<Expr> {
        let lhs = self.fold(lhs);
        let rhs = self.fold(rhs);

        self.on_assignment(expr, &lhs, &rhs)
    }

    fn on_variable(&mut self, expr: Rc<Expr>, _name: &Name) -> Rc<Expr> {
        expr
    }
    fn _fold_variable(&mut self, expr: Rc<Expr>, name: &Name) -> Rc<Expr> {
        self.on_variable(expr, name)
    }

    fn on_if(
        &mut self,
        expr: Rc<Expr>,
        _cond: &Rc<Expr>,
        _then: &Rc<Expr>,
        _alt: &Option<Rc<Expr>>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_if(
        &mut self,
        expr: Rc<Expr>,
        cond: &ExprID,
        then: &ExprID,
        alt: &Option<ExprID>,
    ) -> Rc<Expr> {
        let cond = self.fold(cond);
        let then = self.fold(then);
        let alt = alt.map(|i| self.fold(&i));
        self.on_if(expr, &cond, &then, &alt)
    }

    fn on_loop(&mut self, expr: Rc<Expr>, _cond: &Option<Rc<Expr>>, _body: &Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_loop(&mut self, expr: Rc<Expr>, cond: &Option<ExprID>, body: &ExprID) -> Rc<Expr> {
        let cond = cond.map(|i| self.fold(&i));
        let body = self.fold(body);
        self.on_loop(expr, &cond, &body)
    }

    fn on_member(
        &mut self,
        expr: Rc<Expr>,
        _receiver: &Option<Rc<Expr>>,
        _name: &String,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_member(
        &mut self,
        expr: Rc<Expr>,
        receiver: &Option<ExprID>,
        name: &String,
    ) -> Rc<Expr> {
        let receiver = receiver.map(|i| self.fold(&i));
        self.on_member(expr, &receiver, name)
    }

    fn on_enum_decl(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _items: Vec<Rc<Expr>>,
        _body: Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_enum_decl(
        &mut self,

        expr: Rc<Expr>,
        name: &Name,
        items: &Vec<ExprID>,
        body: &ExprID,
    ) -> Rc<Expr> {
        let body = self.fold(body);
        let items = self.fold_mult(items);
        self.on_enum_decl(expr, name, items, body)
    }

    fn on_enum_variant(&mut self, expr: Rc<Expr>, _name: &Name, _items: Vec<Rc<Expr>>) -> Rc<Expr> {
        expr
    }
    fn _fold_enum_variant(&mut self, expr: Rc<Expr>, name: &Name, items: &Vec<ExprID>) -> Rc<Expr> {
        let items = self.fold_mult(items);
        self.on_enum_variant(expr, name, items)
    }

    fn on_match(&mut self, expr: Rc<Expr>, _pattern: Rc<Expr>, _items: Vec<Rc<Expr>>) -> Rc<Expr> {
        expr
    }
    fn _fold_match(&mut self, expr: Rc<Expr>, pattern: &ExprID, items: &Vec<ExprID>) -> Rc<Expr> {
        let pattern = self.fold(pattern);
        let items = self.fold_mult(items);
        self.on_match(expr, pattern, items)
    }

    fn on_match_arm(&mut self, expr: Rc<Expr>, _pattern: Rc<Expr>, _body: Rc<Expr>) -> Rc<Expr> {
        expr
    }
    fn _fold_match_arm(&mut self, expr: Rc<Expr>, pattern: &ExprID, body: &ExprID) -> Rc<Expr> {
        let pattern = self.fold(pattern);
        let body = self.fold(body);
        self.on_match_arm(expr, pattern, body)
    }

    fn on_pattern_variable(
        &mut self,
        expr: Rc<Expr>,
        _enum_name: &Option<Name>,
        _variant_name: &Name,
        _items: Vec<Rc<Expr>>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_pattern_variable(
        &mut self,

        expr: Rc<Expr>,
        enum_name: &Option<Name>,
        variant_name: &Name,
        items: &Vec<ExprID>,
    ) -> Rc<Expr> {
        let items = self.fold_mult(items);
        self.on_pattern_variable(expr, enum_name, variant_name, items)
    }

    fn on_protocol_decl(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _associated_types: Vec<Rc<Expr>>,
        _body: Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_protocol_decl(
        &mut self,
        expr: Rc<Expr>,
        name: &Name,
        associated_types: &Vec<ExprID>,
        body: &ExprID,
    ) -> Rc<Expr> {
        let associated_types = self.fold_mult(associated_types);
        let body = self.fold(body);
        self.on_protocol_decl(expr, name, associated_types, body)
    }

    fn on_func_signature(
        &mut self,
        expr: Rc<Expr>,
        _name: &Name,
        _params: Vec<Rc<Expr>>,
        _generics: Vec<Rc<Expr>>,
        _ret: Rc<Expr>,
    ) -> Rc<Expr> {
        expr
    }
    fn _fold_func_signature(
        &mut self,
        expr: Rc<Expr>,
        name: &Name,
        params: &Vec<ExprID>,
        generics: &Vec<ExprID>,
        ret: &ExprID,
    ) -> Rc<Expr> {
        let params = self.fold_mult(params);
        let generics = self.fold_mult(generics);
        let ret = self.fold(ret);
        self.on_func_signature(expr, name, params, generics, ret)
    }
}
