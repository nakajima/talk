use crate::token_kind::TokenKind;

use super::expr::{ExprKind::*, VarDepth};
use super::parse_tree::ParseTree;
use super::parser::NodeID;

pub struct NameResolver<'a> {
    parse_tree: &'a mut ParseTree,
    // https://en.wikipedia.org/wiki/De_Bruijn_index
    names_stack: Vec<&'static str>,
}

impl<'a> NameResolver<'a> {
    pub fn resolve(&mut self) {
        let ids: Vec<NodeID> = self.parse_tree.root_ids();
        Self::resolve_nodes(ids, self.parse_tree, &mut self.names_stack);
    }

    fn resolve_nodes(
        node_ids: Vec<NodeID>,
        parse_tree: &mut ParseTree,
        names_stack: &mut Vec<&'static str>,
    ) {
        for node_id in node_ids {
            let node = parse_tree.get(node_id).unwrap();

            match &node.kind {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                Unary(_, expr_id) => Self::resolve_nodes(vec![*expr_id], parse_tree, names_stack),
                Binary(lhs, _, rhs) => {
                    Self::resolve_nodes(vec![*lhs, *rhs], parse_tree, names_stack);
                }
                Tuple(items) => Self::resolve_nodes(items.to_vec(), parse_tree, names_stack),
                EmptyTuple => continue,
                Block(items) => {
                    Self::resolve_nodes(items.to_vec(), parse_tree, names_stack);
                }
                Func(name, params, body) => {
                    let Tuple(params_tuple) = &parse_tree.get(*params).unwrap().kind else {
                        unreachable!()
                    };

                    let mut locals_count = params_tuple.len();

                    // If it's a named function, we want the name so we can recur.
                    if let Some(name) = name {
                        if let TokenKind::Identifier(name) = name.kind {
                            locals_count += 1;
                            names_stack.push(name);
                        }
                    }

                    for param in params_tuple {
                        if let Variable(name) = parse_tree.get(*param).unwrap().kind {
                            names_stack.push(name);
                        }
                    }

                    Self::resolve_nodes(vec![*body], parse_tree, names_stack);

                    for _ in 0..locals_count {
                        names_stack.pop();
                    }
                }

                Variable(name) => {
                    let depth = names_stack
                        .iter()
                        .rev()
                        .position(|n| n == name)
                        .unwrap_or(0); // free names 
                    parse_tree.nodes[node_id as usize].kind = ResolvedVariable(depth as VarDepth);
                }
                ResolvedVariable(_) => continue,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn resolve(code: &'static str) -> ParseTree {
        let mut tree = parse(code).expect("parse failed");
        let mut resolver = NameResolver {
            parse_tree: &mut tree,
            names_stack: vec![],
        };
        resolver.resolve();
        tree
    }

    #[test]
    fn resolves_literal_int_unchanged() {
        let tree = resolve("123");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root.kind, LiteralInt("123"));
    }

    #[test]
    fn resolves_literal_float_unchanged() {
        let tree = resolve("3.14");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root.kind, LiteralFloat("3.14"));
    }

    #[test]
    fn resolves_simple_variable_to_depth_0() {
        let tree = resolve("hello");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root.kind, ResolvedVariable(0));
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");
        let root = tree.roots()[0].unwrap();
        if let Func(_, _, body_id) = root.kind {
            let Block(exprs) = &tree.get(body_id).unwrap().kind else {
                panic!("didn't get a block")
            };

            assert_eq!(exprs.len(), 1);
            let x = tree.get(exprs[0]).unwrap();
            assert_eq!(x.kind, ResolvedVariable(0));
        } else {
            panic!("expected Func node");
        }
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func(x, y) { func(x) { x \n y }\nx }\n");
        let outer = tree.roots()[0].unwrap();
        // outer Func has its body as an inner Func
        let Func(_, _, outer_body_id) = outer.kind else {
            panic!("did not get outer func")
        };
        let Block(outer_body) = &tree.get(outer_body_id).unwrap().kind else {
            panic!("outer body not a block")
        };

        let inner = tree.get(outer_body[0]).unwrap();
        let Func(_, _, inner_body_id) = inner.kind else {
            panic!("didn't get inner func")
        };

        let Block(inner_body) = &tree.get(inner_body_id).unwrap().kind else {
            panic!("outer body not a block")
        };

        let inner = tree.get(inner_body[0]).unwrap();
        assert_eq!(inner.kind, ResolvedVariable(0));

        let inner = tree.get(inner_body[1]).unwrap();
        assert_eq!(inner.kind, ResolvedVariable(1));

        let outer_x = tree.get(outer_body[1]).unwrap();
        assert_eq!(outer_x.kind, ResolvedVariable(1));
    }
}
