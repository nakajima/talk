use crate::token_kind::TokenKind;

use super::expr::{Expr::*, VarDepth};
use super::parse_tree::ParseTree;
use super::parser::NodeID;

#[derive(Default)]
pub struct NameResolver {
    // https://en.wikipedia.org/wiki/De_Bruijn_index
    names_stack: Vec<&'static str>,
}

impl NameResolver {
    pub fn new() -> Self {
        NameResolver {
            names_stack: vec![],
        }
    }

    pub fn resolve(&mut self, mut parse_tree: ParseTree) -> ParseTree {
        let ids: Vec<NodeID> = parse_tree.root_ids();
        let mut name_counter_stack: Vec<u8> = vec![0];
        Self::resolve_nodes(
            ids,
            &mut parse_tree,
            &mut self.names_stack,
            &mut name_counter_stack,
        );
        parse_tree
    }

    fn resolve_nodes(
        node_ids: Vec<NodeID>,
        parse_tree: &mut ParseTree,
        names_stack: &mut Vec<&'static str>,
        name_counter_stack: &mut Vec<u8>,
    ) {
        for node_id in node_ids {
            let node = parse_tree.get(node_id).unwrap();

            match node {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                Let(name) => {
                    names_stack.push(name);

                    if let Some(counter) = name_counter_stack.last_mut() {
                        *counter += 1;
                    }
               }
                Assignment(lhs, rhs) => {
                    Self::resolve_nodes(
                        vec![*lhs, *rhs],
                        parse_tree,
                        names_stack,
                        name_counter_stack,
                    );
                }
                Unary(_, expr_id) => {
                    Self::resolve_nodes(
                        vec![*expr_id],
                        parse_tree,
                        names_stack,
                        name_counter_stack,
                    );
                }
                Binary(lhs, _, rhs) => {
                    Self::resolve_nodes(
                        vec![*lhs, *rhs],
                        parse_tree,
                        names_stack,
                        name_counter_stack,
                    );
                }
                Tuple(items) => {
                    Self::resolve_nodes(
                        items.to_vec(),
                        parse_tree,
                        names_stack,
                        name_counter_stack,
                    );
                }
                Block(items) => {
                    Self::resolve_nodes(
                        items.to_vec(),
                        parse_tree,
                        names_stack,
                        name_counter_stack,
                    );
                }
                Func(name, params, body) => {
                    // If it's a named function, we want the name so we can recur.
                    if let Some(name) = name {
                        if let TokenKind::Identifier(name) = name.kind {
                            names_stack.push(name);
                            *name_counter_stack.last_mut().unwrap() += 1;
                        }
                    }

                    name_counter_stack.push(params.len() as u8);

                    for param in params {
                        let Parameter(name) = parse_tree.get(*param).unwrap() else {
                            panic!("got a non variable param")
                        };
                        names_stack.push(name);
                    }

                    let mut to_resolve = params.clone();
                    to_resolve.push(*body);
                    Self::resolve_nodes(to_resolve, parse_tree, names_stack, name_counter_stack);

                    for _ in 0..name_counter_stack.pop().unwrap() {
                        names_stack.pop();
                    }
                }

                Parameter(name) => {
                    let depth = names_stack
                        .iter()
                        .rev()
                        .position(|n| n == name)
                        .unwrap_or(0); // free names 
                    parse_tree.nodes[node_id as usize] = ResolvedVariable(depth as VarDepth);
                }

                Variable(name) => {
                    let depth = names_stack
                        .iter()
                        .rev()
                        .position(|n| n == name)
                        .unwrap_or(0); // free names 
                    parse_tree.nodes[node_id as usize] = ResolvedVariable(depth as VarDepth);
                }
                ResolvedVariable(_) => continue,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{expr::Expr, parser::parse};

    fn resolve(code: &'static str) -> ParseTree {
        let tree = parse(code).expect("parse failed");
        let mut resolver = NameResolver::default();
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
        assert_eq!(root, &ResolvedVariable(0));
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");
        let root = tree.roots()[0].unwrap();
        if let Func(_, params, body_id) = root {
            assert_eq!(params.len(), 1);
            let x_param = tree.get(params[0]).unwrap();
            assert_eq!(x_param, &ResolvedVariable(0));

            let Block(exprs) = &tree.get(*body_id).unwrap() else {
                panic!("didn't get a block")
            };

            assert_eq!(exprs.len(), 1);
            let x = tree.get(exprs[0]).unwrap();
            assert_eq!(x, &ResolvedVariable(0));
        } else {
            panic!("expected Func node");
        }
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func(x, y) { func(x) { x \n y }\nx }\n");
        let outer = tree.roots()[0].unwrap();
        // outer Func has its body as an inner Func
        let Func(_, _, outer_body_id) = outer else {
            panic!("did not get outer func")
        };
        let Block(outer_body) = &tree.get(*outer_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner = tree.get(outer_body[0]).unwrap();
        let Func(_, _, inner_body_id) = inner else {
            panic!("didn't get inner func")
        };

        let Block(inner_body) = &tree.get(*inner_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner_x = tree.get(inner_body[0]).unwrap();
        assert_eq!(inner_x, &ResolvedVariable(0));

        let inner_y = tree.get(inner_body[1]).unwrap();
        assert_eq!(inner_y, &ResolvedVariable(1));

        let outer_x = tree.get(outer_body[1]).unwrap();
        assert_eq!(outer_x, &ResolvedVariable(1));
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

        let Expr::Assignment(let_expr, int) = tree.get(tree.root_ids()[0]).unwrap() else {
            panic!("didnt get assignment")
        };

        println!("{:?}", tree.nodes);

        assert_eq!(*tree.get(*int).unwrap(), LiteralInt("123"));

        assert_eq!(*tree.get(tree.root_ids()[2]).unwrap(), ResolvedVariable(1));
        assert_eq!(*tree.get(*let_expr).unwrap(), ResolvedVariable(1));

        assert_eq!(*tree.get(tree.root_ids()[3]).unwrap(), ResolvedVariable(0));
    }
}

// TODO:

// named recursive binds
// parameter ordering
// captured vs. shadowed vs. free
// arbitrary nesting depth
//   non‐statement AST nodes (tuples, blocks)
