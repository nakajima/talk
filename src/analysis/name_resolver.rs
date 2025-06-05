use std::collections::HashMap;

use crate::NameResolved;
use crate::SymbolID;
use crate::SymbolKind;
use crate::SymbolTable;
use crate::expr::Expr::*;
use crate::expr::Pattern;
use crate::name::Name;
use crate::parser::ExprID;
use crate::prelude::PRELUDE;
use crate::source_file::SourceFile;

pub struct NameResolver {
    symbol_table: SymbolTable,
    scopes: Vec<HashMap<String, SymbolID>>,
}

impl Default for NameResolver {
    fn default() -> Self {
        let symbol_table = PRELUDE.symbols.clone();
        let initial_scope = symbol_table.build_name_scope();

        NameResolver {
            symbol_table,
            scopes: vec![initial_scope],
        }
    }
}

impl NameResolver {
    pub fn new() -> Self {
        let symbol_table = SymbolTable::default();
        let initial_scope = symbol_table.build_name_scope();

        NameResolver {
            symbol_table,
            scopes: vec![initial_scope],
        }
    }

    pub fn resolve(mut self, mut source_file: SourceFile) -> SourceFile<NameResolved> {
        let ids: Vec<ExprID> = source_file.root_ids();
        self.resolve_nodes(ids, &mut source_file);
        source_file.to_resolved(self.symbol_table)
    }

    fn resolve_nodes(&mut self, node_ids: Vec<ExprID>, source_file: &mut SourceFile) {
        // 1) First pass: Hoist enums and their variants
        for &id in &node_ids {
            let Some(EnumDecl(Name::Raw(name_str), generics, body_expr)) =
                source_file.get(id).cloned()
            else {
                continue;
            };

            // Declare the enum type
            let enum_symbol = self.declare(name_str.clone(), SymbolKind::Enum, id);

            self.resolve_nodes(generics.clone(), source_file);

            source_file.nodes[id as usize] =
                EnumDecl(Name::Resolved(enum_symbol, name_str), generics, body_expr);

            // Hoist variants
            self.hoist_enum_variants(body_expr, source_file);
        }

        // 1) Hoist all funcs in this block before any recursion
        for &id in &node_ids {
            if let Func {
                name: Some(Name::Raw(name)),
                generics,
                params,
                body,
                ret,
            } = source_file.get(id).unwrap().clone()
            {
                let symbol_id = self.declare(name.clone(), SymbolKind::Func, id);

                // if let Some(ret) = ret {
                //     self.resolve_nodes(vec![ret], source_file)
                // };

                // self.resolve_nodes(generics.clone(), source_file);

                source_file.nodes[id as usize] = Func {
                    name: Some(Name::Resolved(symbol_id, name)),
                    generics,
                    params,
                    body,
                    ret,
                };
            }
        }

        for node_id in node_ids {
            let expr = &mut source_file.get_mut(node_id).unwrap();
            match expr.clone() {
                LiteralInt(_) => continue,
                LiteralFloat(_) => continue,
                LiteralTrue | LiteralFalse => continue,
                Return(rhs) => {
                    if let Some(rhs) = rhs {
                        self.resolve_nodes(vec![rhs], source_file);
                    }
                }
                If(condi, conseq, alt) => {
                    if let Some(alt) = alt {
                        self.resolve_nodes(vec![condi, conseq, alt], source_file);
                    } else {
                        self.resolve_nodes(vec![condi, conseq], source_file);
                    }
                }
                Loop(cond, body) => {
                    if let Some(cond) = cond {
                        self.resolve_nodes(vec![cond, body], source_file);
                    } else {
                        self.resolve_nodes(vec![body], source_file);
                    }
                }
                Member(receiver, _member) => {
                    if let Some(receiver) = receiver {
                        self.resolve_nodes(vec![receiver], source_file);
                    }
                }
                Let(name, rhs) => {
                    let name = match name {
                        Name::Raw(name_str) => {
                            let symbol_id =
                                self.declare(name_str.clone(), SymbolKind::Local, node_id);
                            Name::Resolved(symbol_id, name_str)
                        }
                        Name::Resolved(_, _) => name,
                    };

                    if let Some(rhs) = rhs {
                        self.resolve_nodes(vec![rhs], source_file);
                    }

                    source_file.nodes[node_id as usize] = Let(name, rhs);
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
                Func {
                    generics,
                    params,
                    body,
                    ret,
                    ..
                } => {
                    self.start_scope();

                    self.resolve_nodes(generics, source_file);

                    for param in params.clone() {
                        let Some(Parameter(Name::Raw(name), ty_id)) = source_file.get(param) else {
                            panic!("got a non variable param")
                        };

                        self.declare(name.clone(), SymbolKind::Param, node_id);

                        if let Some(ty_id) = ty_id {
                            self.resolve_nodes(vec![*ty_id], source_file);
                        }
                    }

                    let mut to_resolve = params.clone();
                    to_resolve.push(body);

                    if let Some(ret) = ret {
                        to_resolve.push(ret);
                    }

                    self.resolve_nodes(to_resolve, source_file);
                    self.end_scope();
                }
                Parameter(name, ty_repr) => {
                    if let Some(ty_repr) = ty_repr {
                        self.resolve_nodes(vec![ty_repr], source_file)
                    };

                    match name {
                        Name::Raw(name_str) => {
                            let symbol_id = self.lookup(&name_str);
                            source_file.nodes[node_id as usize] =
                                Parameter(Name::Resolved(symbol_id, name_str), ty_repr);
                        }
                        Name::Resolved(_, _) => (),
                    }
                }
                Variable(name, _) => match name {
                    Name::Raw(name_str) => {
                        let symbol_id = self.lookup(&name_str);
                        log::trace!("Replacing variable {} with {:?}", name_str, symbol_id);
                        source_file.nodes[node_id as usize] =
                            Variable(Name::Resolved(symbol_id, name_str), None);
                    }
                    Name::Resolved(_, _) => (),
                },
                TypeRepr(name, generics, is_type_parameter_decl) => {
                    log::trace!(
                        "Resolving TypeRepr: {:?}, generics: {:?}, is_param_decl: {}",
                        name,
                        generics,
                        is_type_parameter_decl
                    );

                    let resolved_name_for_node = match name.clone() {
                        Name::Raw(raw_name_str) => {
                            if is_type_parameter_decl {
                                // Declaration site of a type parameter (e.g., T in `enum Option<T>`)
                                // Ensure it's declared in the current scope.
                                let symbol_id = self.declare(
                                    raw_name_str.clone(),
                                    SymbolKind::TypeParameter,
                                    node_id,
                                );
                                Name::Resolved(symbol_id, raw_name_str)
                            } else {
                                // Usage site of a type name (e.g., T in `case some(T)`, or `Int`)
                                // Look up an existing symbol.
                                let symbol_id = self.lookup(&raw_name_str);
                                Name::Resolved(symbol_id, raw_name_str)
                            }
                        }
                        Name::Resolved(_, _) => name, // Already resolved, no change needed to the name itself.
                    };

                    // Update the existing TypeRepr node with the resolved name.
                    // The node type remains TypeRepr.
                    source_file.nodes[node_id as usize] = TypeRepr(
                        resolved_name_for_node,
                        generics.clone(), // Keep original generics ExprIDs
                        is_type_parameter_decl,
                    );

                    // Recursively resolve any type arguments within this TypeRepr.
                    self.resolve_nodes(generics, source_file);
                }
                FuncTypeRepr(args, ret, _) => {
                    self.resolve_nodes(args, source_file);
                    self.resolve_nodes(vec![ret], source_file);
                }
                TupleTypeRepr(types, _) => {
                    self.resolve_nodes(types, source_file);
                }
                EnumDecl(name, generics, body) => {
                    match name {
                        Name::Raw(name_str) => {
                            let symbol_id =
                                self.declare(name_str.clone(), SymbolKind::Enum, node_id);
                            source_file.nodes[node_id as usize] = EnumDecl(
                                Name::Resolved(symbol_id, name_str),
                                generics.clone(),
                                body,
                            )
                        }
                        _ => continue,
                    }

                    self.resolve_nodes(generics, source_file);
                    self.resolve_nodes(vec![body], source_file);
                }
                EnumVariant(_, values) => {
                    self.resolve_nodes(values, source_file);
                }
                Match(scrutinee, arms) => {
                    // Resolve the scrutinee expression
                    self.resolve_nodes(vec![scrutinee], source_file);
                    // Each arm will manage its own scope for pattern bindings.
                    // The Match expression itself doesn't introduce a new scope for *bindings*
                    // that span across arms or affect expressions outside the match.
                    self.resolve_nodes(arms, source_file);
                }
                MatchArm(pattern, body) => {
                    self.start_scope(); // New scope for this arm's bindings
                    self.resolve_nodes(vec![pattern], source_file);
                    self.resolve_nodes(vec![body], source_file);
                    self.end_scope();
                }
                Pattern(pattern) => {
                    let pattern = self.resolve_pattern(pattern, source_file, node_id);
                    source_file.nodes[node_id as usize] = Pattern(pattern);
                }
                PatternVariant(_, _, _items) => todo!(),
            }
        }
    }

    fn resolve_pattern(
        &mut self,
        pattern: Pattern,
        source_file: &mut SourceFile,
        node_id: ExprID,
    ) -> Pattern {
        match pattern {
            Pattern::Bind(Name::Raw(name_str)) => {
                let symbol = self.declare(name_str.clone(), SymbolKind::PatternBind, node_id);
                Pattern::Bind(Name::Resolved(symbol, name_str))
            }
            Pattern::Variant {
                enum_name,
                variant_name,
                fields,
            } => {
                let enum_name = if let Some(Name::Raw(enum_name)) = enum_name {
                    let symbol = self.declare(enum_name.clone(), SymbolKind::PatternBind, node_id);
                    Some(Name::Resolved(symbol, enum_name))
                } else {
                    None
                };

                let fields = fields
                    .iter()
                    .map(|f| self.resolve_pattern(f.clone(), source_file, node_id))
                    .collect();

                Pattern::Variant {
                    enum_name,
                    variant_name,
                    fields,
                }
            }
            _ => pattern,
        }
    }

    pub fn resolve_builtin(&self, name: &Name) -> Option<SymbolID> {
        match name {
            Name::Raw(name_str) => self.symbol_table.lookup(name_str),
            _ => None,
        }
    }

    // New helper method to hoist enum variants
    fn hoist_enum_variants(&mut self, body_expr_id: ExprID, source_file: &mut SourceFile) {
        let Block(variant_ids) = source_file.get(body_expr_id).unwrap().clone() else {
            panic!("Expected Block for enum body");
        };

        for variant_id in variant_ids {
            let variant_expr = source_file.get(variant_id).unwrap().clone();

            if let EnumVariant(Name::Raw(variant_name), field_types) = variant_expr {
                self.resolve_nodes(field_types.clone(), source_file);

                // Update the AST
                source_file.nodes[variant_id as usize] =
                    EnumVariant(Name::Raw(variant_name), field_types);
            }
        }
    }

    // Helper method to get enum symbol from variant symbol
    pub fn get_enum_for_variant(&self, variant_symbol: SymbolID) -> Option<SymbolID> {
        if let Some(symbol_info) = self.symbol_table.get(&variant_symbol) {
            match &symbol_info.kind {
                SymbolKind::EnumVariant(enum_symbol) => Some(*enum_symbol),
                _ => None,
            }
        } else {
            None
        }
    }

    fn declare(&mut self, name: String, kind: SymbolKind, expr_id: ExprID) -> SymbolID {
        log::trace!(
            "declaring {} in {:?} at depth {}",
            name,
            self.scopes,
            self.scopes.len() - 1
        );
        let symbol_id = self.symbol_table.add(&name, kind, expr_id);
        self.scopes.last_mut().unwrap().insert(name, symbol_id);
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
        assert_eq!(root, &LiteralInt("123".into()));
    }

    #[test]
    fn resolves_literal_float_unchanged() {
        let tree = resolve("3.14");
        let root = tree.roots()[0].unwrap();
        assert_eq!(root, &LiteralFloat("3.14".into()));
    }

    #[test]
    fn resolved_builtin() {
        let tree = resolve("Int");
        let root = tree.roots()[0].unwrap();
        assert_eq!(
            root,
            &Variable(Name::Resolved(SymbolID(-1), "Int".into()), None)
        );
    }

    #[test]
    fn resolves_simple_variable_to_depth_0() {
        let tree = resolve("hello");
        let root = tree.roots()[0].unwrap();
        assert_eq!(
            root,
            &Variable(Name::Resolved(SymbolID(0), "hello".into()), None)
        );
    }

    #[test]
    fn resolves_shadowed_variable_in_lambda() {
        let tree = resolve("func(x) { x }\n");
        let root = tree.roots()[0].unwrap();

        if let Func { params, body, .. } = root {
            assert_eq!(params.len(), 1);
            let x_param = tree.get(params[0]).unwrap();
            assert_eq!(
                x_param,
                &Parameter(Name::Resolved(SymbolID::at(1), "x".into()), None)
            );

            let Block(exprs) = &tree.get(*body).unwrap() else {
                panic!("didn't get a block")
            };

            assert_eq!(exprs.len(), 1);
            let x = tree.get(exprs[0]).unwrap();
            assert_eq!(
                x,
                &Variable(Name::Resolved(SymbolID::at(1), "x".into()), None)
            );
        } else {
            panic!("expected Func node");
        }
    }

    #[test]
    fn resolves_nested_shadowing_correctly() {
        let tree = resolve("func(x, y) { func(x) { x \n y }\nx }\n");
        let outer = tree.roots()[0].unwrap();
        // outer Func has its body as an inner Func
        let Func {
            body: outer_body_id,
            ..
        } = outer
        else {
            panic!("did not get outer func")
        };
        let Block(outer_body) = &tree.get(*outer_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner = tree.get(outer_body[0]).unwrap();
        let Func {
            body: inner_body_id,
            ..
        } = inner
        else {
            panic!("didn't get inner func")
        };

        let Block(inner_body) = &tree.get(*inner_body_id).unwrap() else {
            panic!("outer body not a block")
        };

        let inner_x = tree.get(inner_body[0]).unwrap();
        assert_eq!(
            inner_x,
            &Variable(Name::Resolved(SymbolID::at(3), "x".into()), None)
        );

        let inner_y = tree.get(inner_body[1]).unwrap();
        assert_eq!(
            inner_y,
            &Variable(Name::Resolved(SymbolID::at(2), "y".into()), None)
        );

        let outer_x = tree.get(outer_body[1]).unwrap();
        assert_eq!(
            outer_x,
            &Variable(Name::Resolved(SymbolID::at(1), "x".into()), None)
        );
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

        assert_eq!(
            *tree.get(*let_expr).unwrap(),
            Let(Name::Resolved(SymbolID::at(1), "x".into()), None)
        );

        assert_eq!(*tree.get(*int).unwrap(), LiteralInt("123".into()));

        assert_eq!(
            *tree.get(tree.root_ids()[2]).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID::at(1), "x".into()), None)
        );
        assert_eq!(
            *tree.get(tree.root_ids()[3]).unwrap(),
            Variable(Name::Resolved(SymbolID::at(2), "y".into()), None)
        );
    }

    #[test]
    fn resolves_let_rhs() {
        let tree = resolve(
            "
        let x = Optional.none
        ",
        );

        let Expr::Assignment(_, rhs) = tree.get(tree.root_ids()[0]).unwrap() else {
            panic!("didnt get assignment")
        };

        assert_eq!(
            *tree.get(*rhs).unwrap(),
            Expr::Member(Some(1), "none".into())
        );

        assert_eq!(
            *tree.get(1).unwrap(),
            Variable(Name::Resolved(SymbolID::OPTIONAL, "Optional".into()), None)
        );
    }

    #[test]
    fn block_scoping_prevents_let_leak() {
        // parse a block with a single let,
        // followed by a bare `x` at top level:
        let tree = parse("{ let x = 123 } x").unwrap();
        let resolver = NameResolver::default();
        let tree = resolver.resolve(tree);

        // The first root is the Block, the second is the Variable("x")
        let roots = tree.root_ids();
        // That `x` should resolve to the global‐fallback ID 0,
        // not to the block's own `x` (which would have been >0).
        let second = tree.get(roots[1]).unwrap();
        assert_eq!(
            second,
            &Variable(Name::Resolved(SymbolID(0), "x".into()), None)
        );
    }

    #[test]
    fn resolves_enum_variant() {
        let resolved = resolve(
            "
        enum Fizz {
            case foo, bar
        }

        Fizz.foo
        ",
        );

        assert_eq!(
            *resolved.roots()[0].unwrap(),
            Expr::EnumDecl(Name::Resolved(SymbolID::at(1), "Fizz".into()), vec![], 2)
        );
        assert_eq!(*resolved.get(2).unwrap(), Expr::Block(vec![0, 1]));
        assert_eq!(
            *resolved.get(0).unwrap(),
            EnumVariant(Name::Raw("foo".into()), vec![])
        );
        assert_eq!(
            *resolved.get(1).unwrap(),
            EnumVariant(Name::Raw("bar".into()), vec![])
        );

        assert_eq!(
            *resolved.roots()[1].unwrap(),
            Expr::Member(Some(4), "foo".into())
        );
    }

    #[test]
    fn resolves_enum_variant_with_args() {
        let resolved = resolve(
            "
        enum Fizz {
            case foo(Int), bar
        }

        Fizz.foo(123)
        ",
        );

        assert_eq!(
            *resolved.roots()[0].unwrap(),
            Expr::EnumDecl(Name::Resolved(SymbolID::at(1), "Fizz".into()), vec![], 3)
        );
        assert_eq!(*resolved.get(3).unwrap(), Expr::Block(vec![1, 2]));
        assert_eq!(
            *resolved.get(1).unwrap(),
            EnumVariant(Name::Raw("foo".into()), vec![0])
        );
        assert_eq!(
            *resolved.get(2).unwrap(),
            EnumVariant(Name::Raw("bar".into()), vec![])
        );

        assert_eq!(*resolved.roots()[1].unwrap(), Call(6, vec![7]));
        assert_eq!(
            *resolved.get(6).unwrap(),
            Expr::Member(Some(5), "foo".into())
        );
        assert_eq!(
            *resolved.get(5).unwrap(),
            Expr::Variable(Name::Resolved(SymbolID::at(1), "Fizz".into()), None)
        );
    }
}

// TODO:

// named recursive binds
// parameter ordering
// captured vs. shadowed vs. free
// arbitrary nesting depth
//   non‐statement AST nodes (tuples, blocks)
