use derive_visitor::{DriveMut, VisitorMut};

use crate::{
    MemberKind, MemberSymbol, NameResolved, SourceFile, SymbolID, SymbolKind, SymbolTable,
    environment::Environment,
    name::Name,
    parsed_expr::{self, Expr, ParsedExpr},
};

#[derive(VisitorMut)]
#[visitor(ParsedExpr(enter))]
struct InitInserter {
    struct_id: SymbolID,
    initializer: ParsedExpr,
}

impl InitInserter {
    fn enter_parsed_expr(&mut self, parsed_expr: &mut ParsedExpr) {
        if let Expr::Struct {
            name: Name::Resolved(symbol_id, _),
            body:
                box ParsedExpr {
                    expr: Expr::Block(exprs),
                    ..
                },
            ..
        } = &mut parsed_expr.expr
            && self.struct_id == *symbol_id
        {
            exprs.insert(0, self.initializer.clone());
        }
    }
}

#[derive(VisitorMut)]
#[visitor(ParsedExpr(enter))]
struct SelfReturnInserter<'a> {
    env: &'a mut Environment,
    struct_id: SymbolID,
}

impl<'a> SelfReturnInserter<'a> {
    fn enter_parsed_expr(&mut self, expr: &mut ParsedExpr) {
        if let Expr::Init(
            sym,
            box ParsedExpr {
                expr:
                    Expr::Func {
                        body:
                            box ParsedExpr {
                                expr: Expr::Block(items),
                                ..
                            },
                        ..
                    },
                ..
            },
        ) = &mut expr.expr
            && *sym == Some(self.struct_id)
        {
            items.push(gen_expr(
                self.env,
                Expr::Variable(Name::_Self(self.struct_id)),
            ));
        }
    }
}

pub fn synthesize_inits(
    source_file: &mut SourceFile<NameResolved>,
    symbol_table: &mut SymbolTable,
    env: &mut Environment,
) {
    let types = symbol_table
        .types
        .keys()
        .cloned()
        .collect::<Vec<SymbolID>>();
    for sym in types {
        if symbol_table
            .members_for(&sym, MemberKind::Initializer)
            .clone()
            .is_empty()
        {
            tracing::trace!("Synthesizing init for {sym:?}");
            // We need to generate an initializer for this struct
            let mut param_exprs: Vec<ParsedExpr> = vec![];
            let mut body_exprs: Vec<ParsedExpr> = vec![];
            let properties: Vec<MemberSymbol> = symbol_table
                .members_for(&sym, MemberKind::Property)
                .iter()
                .map(|c| c.to_owned().clone())
                .collect();
            for property in properties {
                let param_sym = symbol_table.add(
                    &property.name,
                    crate::SymbolKind::Param,
                    env.synth_expr_id(),
                    None,
                );

                #[allow(clippy::todo)]
                let Some(ParsedExpr {
                    expr:
                        parsed_expr::Expr::Property {
                            type_repr: Some(type_repr),
                            ..
                        },
                    ..
                }) = ParsedExpr::find_in(source_file.roots(), property.expr_id)
                else {
                    todo!(
                        "We don't handle this case yet: {:?}",
                        ParsedExpr::find_in(source_file.roots(), property.expr_id)
                    );
                };

                param_exprs.push(gen_expr(
                    env,
                    Expr::Parameter(
                        Name::Resolved(param_sym, property.name.to_string()),
                        Some(type_repr.clone()),
                    ),
                ));

                let member_expr = Expr::Member(
                    Some(gen_expr(env, Expr::Variable(Name::_Self(sym))).into()),
                    property.name.clone().into(),
                );
                let assignment_expr = Expr::Assignment(
                    gen_expr(env, member_expr).into(),
                    gen_expr(
                        env,
                        Expr::Variable(Name::Resolved(param_sym, property.name)),
                    )
                    .into(),
                );

                body_exprs.push(gen_expr(env, assignment_expr));
            }

            // Make sure the func always returns self
            let self_ret = gen_expr(env, Expr::Variable(Name::_Self(sym)));
            body_exprs.push(self_ret);

            let body = gen_expr(env, Expr::Block(body_exprs));

            let func = gen_expr(
                env,
                Expr::Func {
                    name: Some(Name::Resolved(sym, "init".to_string())),
                    generics: vec![],
                    params: param_exprs,
                    body: Box::new(body),
                    ret: None,
                    captures: vec![],
                    attributes: vec![],
                },
            );

            #[allow(clippy::expect_used)]
            let struct_info = symbol_table
                .get(&sym)
                .cloned()
                .expect("didn't get struct for struct???");

            let init = gen_expr(env, Expr::Init(Some(sym), Box::new(func)));

            let definition = struct_info.definition.clone();
            let init_sym = symbol_table.add(
                "init",
                SymbolKind::SyntheticConstructor,
                init.id,
                definition,
            );

            symbol_table.add_initializer(sym, "init".to_string(), init.id, init_sym);

            let mut inserter = InitInserter {
                struct_id: sym,
                initializer: init,
            };

            for root in source_file.roots_mut() {
                root.drive_mut(&mut inserter);
            }

            // let Some(Expr::Struct { body, .. }) = source_file.get(&struct_info.expr_id).cloned()
            // else {
            //     tracing::error!(
            //         "didn't get struct from expr id: {:?}",
            //         source_file.get(&struct_info.expr_id)
            //     );
            //     return;
            // };

            // let Some(Expr::Block(existing_body_ids)) = source_file.get_mut(&body) else {
            //     tracing::error!("didn't get block body");
            //     return;
            // };

            //

            // existing_body_ids.insert(0, init_expr);
        } else {
            let mut inserter = SelfReturnInserter {
                env,
                struct_id: sym,
            };

            for root in source_file.roots_mut() {
                root.drive_mut(&mut inserter);
            }
        }
    }
}

fn gen_expr(env: &mut Environment, expr: Expr) -> ParsedExpr {
    ParsedExpr {
        id: env.synth_expr_id(),
        expr,
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::{
        NameResolved, SourceFile, SymbolID, SymbolTable,
        compiling::driver::Driver,
        environment::Environment,
        name::Name,
        parsed_expr::{Expr, ParsedExpr},
        synthesis::synthesize_inits,
    };

    pub fn resolve_with_symbols(
        code: &'static str,
    ) -> (SourceFile<NameResolved>, SymbolTable, Environment) {
        let mut driver = Driver::with_str(code);
        let resolved = driver.parse().into_iter().next().unwrap().resolved(
            &mut driver.symbol_table,
            &driver.config,
            &Default::default(),
        );
        let source_file = resolved.source_file(&PathBuf::from("-")).unwrap().clone();

        (source_file, driver.symbol_table, resolved.env)
    }

    #[test]
    fn synthesizes_init() {
        let (mut resolved, mut symbol_table, mut env) = resolve_with_symbols(
            "
        struct Person {
            let age: Int
        }
        ",
        );

        synthesize_inits(&mut resolved, &mut symbol_table, &mut env);

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(items),
                    ..
                },
            ..
        } = &resolved.roots()[0].expr
        else {
            panic!("didn't get struct: {:?}", resolved.roots()[0]);
        };

        let Expr::Init(_, func_expr) = &items[0].expr else {
            panic!("didn't get init")
        };

        let Expr::Func {
            name,
            generics,
            params,
            body,
            ret,
            captures,
            ..
        } = &func_expr.expr
        else {
            panic!("didn't get init func")
        };

        let Some(Name::Resolved(_, init_name)) = name else {
            panic!("didn't get init");
        };
        assert_eq!(init_name, "init");
        assert!(generics.is_empty());
        assert_eq!(params.len(), 1);
        assert_eq!(ret, &None);
        assert!(captures.is_empty());

        let Expr::Block(body_exprs) = &body.expr else {
            panic!("didn't get body")
        };

        assert_eq!(body_exprs.len(), 2);
        let Expr::Assignment(lhs, rhs) = &body_exprs[0].expr else {
            panic!("didn't get assignment");
        };

        let Expr::Member(_, name) = &lhs.expr else {
            panic!("didn't get member");
        };

        assert_eq!(name, &"age".into());

        assert_eq!(
            rhs.expr,
            Expr::Variable(Name::Resolved(SymbolID::resolved(3), "age".into()))
        );
    }

    #[test]
    fn synthesizes_generic_init() {
        let (mut resolved, mut symbol_table, mut env) = resolve_with_symbols(
            "
        struct Person<T> {
            let age: T 
        }
        ",
        );

        synthesize_inits(&mut resolved, &mut symbol_table, &mut env);

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(items),
                    ..
                },
            ..
        } = &resolved.roots()[0].expr
        else {
            panic!("didn't get struct: {:?}", resolved.roots()[0]);
        };

        let Expr::Init(_, func_expr) = &items[0].expr else {
            panic!("didn't get init")
        };

        let Expr::Func {
            name,
            generics,
            params,
            body,
            ret,
            captures,
            ..
        } = &func_expr.expr
        else {
            panic!("didn't get init func")
        };

        let Some(Name::Resolved(_, init_name)) = name else {
            panic!("didn't get init");
        };
        assert_eq!(init_name, "init");
        assert_eq!(generics.len(), 1);
        assert_eq!(params.len(), 1);
        assert_eq!(ret, &None);
        assert!(captures.is_empty());

        let Expr::Block(body_exprs) = &body.expr else {
            panic!("didn't get body")
        };

        assert_eq!(body_exprs.len(), 2);
        let Expr::Assignment(lhs, rhs) = &body_exprs[0].expr else {
            panic!("didn't get assignment");
        };

        let Expr::Member(_, name) = &lhs.expr else {
            panic!("didn't get member");
        };

        assert_eq!(name, &"age".into());

        assert_eq!(
            rhs.expr,
            Expr::Variable(Name::Resolved(SymbolID::resolved(4), "age".into()))
        );

        // let Expr::Parameter(_, Some(ty)) = &params[0].expr else {
        //     panic!("didn't get param")
        // };

        // assert_eq!(
        //     *ty,
        //     Box::new(any_expr!(Expr::TypeRepr {
        //         name: Name::Resolved(SymbolID::ANY, "T".to_string()),
        //         generics: vec![],
        //         conformances: vec![],
        //         introduces_type: false
        //     }))
        // )
    }
}
