use std::collections::HashMap;

use crate::expr::Expr::*;
use crate::expr::FuncName;
use crate::parse_tree::ParseTree;
use crate::parser::ExprID;

use super::symbol_table::{SymbolID, SymbolKind, SymbolTable};

#[derive(Default)]
pub struct NameResolver<'a> {
    symbol_table: SymbolTable,
    scopes: Vec<HashMap<&'a str, SymbolID>>,
}

impl<'a> NameResolver<'a> {
    pub fn new() -> Self {
        NameResolver {
            symbol_table: SymbolTable::default(),
            scopes: vec![],
        }
    }

    pub fn resolve(mut self, parse_tree: &mut ParseTree) -> (SymbolTable, &mut ParseTree) {
        self.start_scope(); // Push global scope
        let ids: Vec<ExprID> = parse_tree.root_ids();
        self.resolve_nodes(ids, parse_tree);
        (self.symbol_table, parse_tree)
    }

    fn resolve_nodes(&mut self, node_ids: Vec<ExprID>, parse_tree: &mut ParseTree) {
        // 1) Hoist all funcs in this block before any recursion
        for &id in &node_ids {
            if let Func(Some(FuncName::Token(name)), params, body, ret) =
                parse_tree.get(id).unwrap()
            {
                let symbol_id = self.declare(name, SymbolKind::Func);
                parse_tree.nodes[id as usize] = Func(
                    Some(FuncName::Resolved(symbol_id)),
                    params.to_vec(),
                    *body,
                    *ret,
                );
            }
        }

        for node_id in node_ids {
            let node = &mut parse_tree.get_mut(node_id).unwrap();

            match node.clone() {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                Let(name, rhs) => {
                    let symbol_id = self.declare(name, SymbolKind::Local);
                    parse_tree.nodes[node_id as usize] = ResolvedLet(symbol_id, rhs);
                    log::warn!("resolved let: {:?}", self.scopes);
                }
                Call(callee, args) => {
                    let mut to_resolve = args.clone();
                    to_resolve.push(callee);

                    self.resolve_nodes(to_resolve, parse_tree);
                }
                Assignment(lhs, rhs) => {
                    self.resolve_nodes(vec![lhs, rhs], parse_tree);
                }
                Unary(_, expr_id) => {
                    self.resolve_nodes(vec![expr_id], parse_tree);
                }
                Binary(lhs, _, rhs) => {
                    self.resolve_nodes(vec![lhs, rhs], parse_tree);
                }
                Tuple(items) => {
                    self.resolve_nodes(items.to_vec(), parse_tree);
                }
                Block(items) => {
                    self.start_scope();
                    self.resolve_nodes(items.to_vec(), parse_tree);
                    self.end_scope();
                }
                Func(_name, params, body, _ret) => {
                    // Get set when hoisting

                    self.start_scope();

                    for param in params.clone() {
                        let Some(Parameter(name, _)) = parse_tree.get(param) else {
                            panic!("got a non variable param")
                        };

                        self.declare(name, SymbolKind::Param);
                    }

                    let mut to_resolve = params.clone();
                    to_resolve.push(body);
                    self.resolve_nodes(to_resolve, parse_tree);

                    self.end_scope();
                }
                Parameter(name, ty_repr) => {
                    let symbol_id = self.lookup(name);
                    log::trace!("Replacing param {} with {:?}", name, symbol_id);
                    parse_tree.nodes[node_id as usize] = ResolvedVariable(symbol_id, ty_repr);
                }
                Variable(name) => {
                    let symbol_id = self.lookup(name);
                    log::trace!("Replacing variable {} with {:?}", name, symbol_id);
                    parse_tree.nodes[node_id as usize] = ResolvedVariable(symbol_id, None);
                }
                ResolvedLet(_, _) => continue,
                ResolvedVariable(_, _) => continue,
                TypeRepr(_) => todo!(),
            }
        }
    }

    fn declare(&mut self, name: &'a str, kind: SymbolKind) -> SymbolID {
        log::trace!("declaring {} in {:?}", name, self.scopes);
        let symbol_id = self.symbol_table.add(name, kind);
        self.scopes.last_mut().unwrap().insert(name, symbol_id);
        log::trace!("new symbol table: {:?}", self.symbol_table);
        symbol_id
    }

    fn lookup(&self, name: &str) -> SymbolID {
        // self.scopes.last().unwrap().get(name)
        self.scopes
            .iter()
            .rev()
            .find_map(|frame| frame.get(&name).copied())
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

    fn resolve(code: &'static str) -> ParseTree {
        let mut tree = parse(code).expect("parse failed");
        let resolver = NameResolver::default();
        resolver.resolve(&mut tree);

        tree
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
        assert_eq!(root, &ResolvedVariable(SymbolID(0), None));
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");
        let root = tree.roots()[0].unwrap();
        if let Func(_, params, body_id, _ret) = root {
            assert_eq!(params.len(), 1);
            let x_param = tree.get(params[0]).unwrap();
            assert_eq!(x_param, &ResolvedVariable(SymbolID(1), None));

            let Block(exprs) = &tree.get(*body_id).unwrap() else {
                panic!("didn't get a block")
            };

            assert_eq!(exprs.len(), 1);
            let x = tree.get(exprs[0]).unwrap();
            assert_eq!(x, &ResolvedVariable(SymbolID(1), None));
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
        assert_eq!(inner_x, &ResolvedVariable(SymbolID(3), None));

        let inner_y = tree.get(inner_body[1]).unwrap();
        assert_eq!(inner_y, &ResolvedVariable(SymbolID(2), None));

        let outer_x = tree.get(outer_body[1]).unwrap();
        assert_eq!(outer_x, &ResolvedVariable(SymbolID(1), None));
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

        let Expr::ResolvedLet(_, Some(int)) = tree.get(tree.root_ids()[0]).unwrap() else {
            panic!("didnt get assignment")
        };

        assert_eq!(*tree.get(*int).unwrap(), LiteralInt("123"));

        assert_eq!(
            *tree.get(tree.root_ids()[2]).unwrap(),
            Expr::ResolvedVariable(SymbolID(1), None)
        );
        assert_eq!(
            *tree.get(tree.root_ids()[0]).unwrap(),
            ResolvedLet(SymbolID(1), Some(0))
        );

        assert_eq!(
            *tree.get(tree.root_ids()[3]).unwrap(),
            ResolvedVariable(SymbolID(2), None)
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        // parse a block with a single let,
        // followed by a bare `x` at top level:
        let mut tree = parse("{ let x = 123 } x").unwrap();
        let resolver = NameResolver::new();
        let (_symtab, tree) = resolver.resolve(&mut tree);

        // The first root is the Block, the second is the Variable("x")
        let roots = tree.root_ids();
        // That `x` should resolve to the global‐fallback ID 0,
        // not to the block’s own `x` (which would have been >0).
        use crate::expr::Expr::*;
        let second = tree.get(roots[1]).unwrap();
        assert_eq!(second, &ResolvedVariable(SymbolID(0), None));
    }
}

// TODO:

// named recursive binds
// parameter ordering
// captured vs. shadowed vs. free
// arbitrary nesting depth
//   non‐statement AST nodes (tuples, blocks)
