use std::collections::HashMap;

use crate::NameResolved;
use crate::SymbolID;
use crate::SymbolKind;
use crate::SymbolTable;
use crate::expr::Expr::*;
use crate::expr::FuncName;
use crate::expr::Name;
use crate::parser::ExprID;
use crate::source_file::SourceFile;

#[derive(Default)]
pub struct NameResolver {
    symbol_table: SymbolTable,
    scopes: Vec<HashMap<String, SymbolID>>,
}

impl NameResolver {
    pub fn new() -> Self {
        NameResolver {
            symbol_table: SymbolTable::default(),
            scopes: vec![],
        }
    }

    pub fn resolve(mut self, mut source_file: SourceFile) -> SourceFile<NameResolved> {
        self.start_scope(); // Push global scope
        let ids: Vec<ExprID> = source_file.root_ids();
        self.resolve_nodes(ids, &mut source_file);
        source_file.to_resolved(self.symbol_table)
    }

    fn resolve_nodes(&mut self, node_ids: Vec<ExprID>, source_file: &mut SourceFile) {
        // 1) Hoist all funcs in this block before any recursion
        for &id in &node_ids {
            if let Func(Some(FuncName::Token(name)), params, body, ret) =
                source_file.get(id).unwrap()
            {
                let symbol_id = self.declare(name.clone(), SymbolKind::Func);
                source_file.nodes[id as usize] = Func(
                    Some(FuncName::Resolved(symbol_id)),
                    params.to_vec(),
                    *body,
                    *ret,
                );
            }
        }

        for node_id in node_ids {
            let expr = &mut source_file.get_mut(node_id).unwrap();
            match expr.clone() {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                LiteralTrue | LiteralFalse => continue,
                If(_, _, _) => todo!(),
                Loop(_, _) => todo!(),
                Member(_, _) => continue,
                Let(name, rhs) => {
                    match name {
                        Name::Raw(name_str) => {
                            let symbol_id = self.declare(name_str, SymbolKind::Local);
                            source_file.nodes[node_id as usize] =
                                Let(Name::Resolved(symbol_id), rhs);
                        }
                        Name::Resolved(_) => (),
                    };
                }
                Call(callee, args) => {
                    let mut to_resolve = args.clone();
                    to_resolve.push(callee);

                    self.resolve_nodes(to_resolve, source_file);
                }
                Assignment(lhs, rhs) => {
                    self.resolve_nodes(vec![lhs, rhs], source_file);
                }
                Unary(_, expr_id) => {
                    self.resolve_nodes(vec![expr_id], source_file);
                }
                Binary(lhs, _, rhs) => {
                    self.resolve_nodes(vec![lhs, rhs], source_file);
                }
                Tuple(items) => {
                    self.resolve_nodes(items.to_vec(), source_file);
                }
                Block(items) => {
                    self.start_scope();
                    self.resolve_nodes(items.to_vec(), source_file);
                    self.end_scope();
                }
                Func(_name, params, body, _ret) => {
                    // Get set when hoisting

                    self.start_scope();

                    for param in params.clone() {
                        let Some(Parameter(Name::Raw(name), _)) = source_file.get(param) else {
                            panic!("got a non variable param")
                        };

                        self.declare(name.clone(), SymbolKind::Param);
                    }

                    let mut to_resolve = params.clone();
                    to_resolve.push(body);
                    self.resolve_nodes(to_resolve, source_file);

                    self.end_scope();
                }
                Parameter(name, ty_repr) => match name {
                    Name::Raw(name_str) => {
                        let symbol_id = self.lookup(&name_str);
                        source_file.nodes[node_id as usize] =
                            Variable(Name::Resolved(symbol_id), ty_repr);
                    }
                    Name::Resolved(_) => (),
                },
                Variable(name, _) => match name {
                    Name::Raw(name_str) => {
                        let symbol_id = self.lookup(&name_str);
                        log::trace!("Replacing variable {} with {:?}", name_str, symbol_id);
                        source_file.nodes[node_id as usize] =
                            Variable(Name::Resolved(symbol_id), None);
                    }
                    Name::Resolved(_) => (),
                },
                TypeRepr(_) => todo!(),
                EnumDecl(_, _items, _items1) => todo!(),
                EnumVariant(_, _items) => todo!(),
                Match(_, _items) => todo!(),
                MatchArm(_, _) => todo!(),
                PatternVariant(_, _, _items) => todo!(),
                MemberAccess(_, _) => todo!(),
            }
        }
    }

    fn declare(&mut self, name: String, kind: SymbolKind) -> SymbolID {
        log::trace!("declaring {} in {:?}", name, self.scopes);
        let symbol_id = self.symbol_table.add(&name, kind);
        self.scopes.last_mut().unwrap().insert(name, symbol_id);
        log::trace!("new symbol table: {:?}", self.symbol_table);
        symbol_id
    }

    fn lookup(&self, name: &str) -> SymbolID {
        // self.scopes.last().unwrap().get(name)
        self.scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(name).copied())
            .unwrap_or(SymbolID(0))
    }

    fn start_scope(&mut self) {
        log::trace!("scope started: {:?}", self.scopes);
        self.scopes.push(Default::default());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{expr::Expr, parser::parse};

    fn resolve(code: &'static str) -> SourceFile<NameResolved> {
        let tree = parse(code).expect("parse failed");
        let resolver = NameResolver::default();
        resolver.resolve(tree)
    }

    #[test]
    fn resolves_literal_int_unchanged() {
        let tree = resolve("123");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root, &LiteralInt("123"));
    }

    #[test]
    fn resolves_literal_float_unchanged() {
        let tree = resolve("3.14");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root, &LiteralFloat("3.14"));
    }

    #[test]
    fn resolves_simple_variable_to_depth_0() {
        let tree = resolve("hello");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root, &Variable(Name::Resolved(SymbolID(0)), None));
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");
        let root = tree.roots()[0].unwrap();
        if let Func(_, params, body_id, _ret) = root {
            assert_eq!(params.len(), 1);
            let x_param = tree.get(params[0]).unwrap();
            assert_eq!(x_param, &Variable(Name::Resolved(SymbolID(1)), None));

            let Block(exprs) = &tree.get(*body_id).unwrap() else {
                panic!("didn't get a block")
            };

            assert_eq!(exprs.len(), 1);
            let x = tree.get(exprs[0]).unwrap();
            assert_eq!(x, &Variable(Name::Resolved(SymbolID(1)), None));
        } else {
            panic!("expected Func node");
        }
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func(x, y) { func(x) { x \n y }\nx }\n");
        let outer = tree.roots()[0].unwrap();
        // outer Func has its body as an inner Func
        let Func(_, _, outer_body_id, _ret) = outer else {
            panic!("did not get outer func")
        };
        let Block(outer_body) = &tree.get(*outer_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner = tree.get(outer_body[0]).unwrap();
        let Func(_, _, inner_body_id, _ret) = inner else {
            panic!("didn't get inner func")
        };

        let Block(inner_body) = &tree.get(*inner_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner_x = tree.get(inner_body[0]).unwrap();
        assert_eq!(inner_x, &Variable(Name::Resolved(SymbolID(3)), None));

        let inner_y = tree.get(inner_body[1]).unwrap();
        assert_eq!(inner_y, &Variable(Name::Resolved(SymbolID(2)), None));

        let outer_x = tree.get(outer_body[1]).unwrap();
        assert_eq!(outer_x, &Variable(Name::Resolved(SymbolID(1)), None));
    }

    #[test]
    fn resolves_let_expr() {
        let tree = resolve(
            "
        let x = 123
        let y = 345
        x
        y
        ",
        );

        let Expr::Let(_, Some(int)) = tree.get(tree.root_ids()[0]).unwrap() else {
            panic!("didnt get assignment")
        };

        assert_eq!(*tree.get(*int).unwrap(), LiteralInt("123"));

        assert_eq!(
            *tree.get(tree.root_ids()[2]).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID(1)), None)
        );
        assert_eq!(
            *tree.get(tree.root_ids()[0]).unwrap(),
            Let(Name::Resolved(SymbolID(1)), Some(0))
        );

        assert_eq!(
            *tree.get(tree.root_ids()[3]).unwrap(),
            Variable(Name::Resolved(SymbolID(2)), None)
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        // parse a block with a single let,
        // followed by a bare `x` at top level:
        let tree = parse("{ let x = 123 } x").unwrap();
        let resolver = NameResolver::new();
        let tree = resolver.resolve(tree);

        // The first root is the Block, the second is the Variable("x")
        let roots = tree.root_ids();
        // That `x` should resolve to the global‐fallback ID 0,
        // not to the block’s own `x` (which would have been >0).
        let second = tree.get(roots[1]).unwrap();
        assert_eq!(second, &Variable(Name::Resolved(SymbolID(0)), None));
    }
}

// TODO:

// named recursive binds
// parameter ordering
// captured vs. shadowed vs. free
// arbitrary nesting depth
//   non‐statement AST nodes (tuples, blocks)
