use crate::{
    NameResolved, SourceFile, SymbolTable, environment::Environment,
};

pub fn synthesize_inits(
    source_file: &mut SourceFile<NameResolved>,
    symbol_table: &mut SymbolTable,
    env: &mut Environment,
) {
    // for (sym, table) in symbol_table.types.clone() {
    //     if table.initializers.is_empty() {
    //         tracing::trace!("Synthesizing init for {sym:?}");
    //         let mut body_exprs: Vec<ExprID> = vec![];

    //         // We need to generate an initializer for this struct
    //         let mut params: Vec<ExprID> = vec![];
    //         for property in table.properties {
    //             let param_sym = symbol_table.add(
    //                 &property.name,
    //                 crate::SymbolKind::Param,
    //                 -(source_file.nodes.len() as i32),
    //                 None,
    //             );

    //             let assignment_receiver = source_file.add(
    //                 env.next_expr_id(),
    //                 Expr::Variable(Name::_Self(sym)),
    //                 ExprMeta::generated(),
    //             );
    //             let assignment_lhs = source_file.add(
    //                 env.next_expr_id(),
    //                 Expr::Member(Some(assignment_receiver), property.name.clone()),
    //                 ExprMeta::generated(),
    //             );
    //             let assignment_rhs = source_file.add(
    //                 env.next_expr_id(),
    //                 Expr::Variable(Name::Resolved(param_sym, property.name.clone()), None),
    //                 ExprMeta::generated(),
    //             );
    //             let assignment = source_file.add(
    //                 env.next_expr_id(),
    //                 Expr::Assignment(assignment_lhs, assignment_rhs),
    //                 ExprMeta::generated(),
    //             );
    //             body_exprs.push(assignment);

    //             params.push(source_file.add(
    //                 env.next_expr_id(),
    //                 Expr::Parameter(
    //                     Name::Resolved(param_sym, property.name.to_string()),
    //                     property.type_id,
    //                 ),
    //                 ExprMeta::generated(),
    //             ));
    //         }

    //         // Make sure the func always returns self
    //         let self_ret = source_file.add(
    //             env.next_expr_id(),
    //             Expr::Variable(Name::_Self(sym), None),
    //             ExprMeta::generated(),
    //         );
    //         body_exprs.push(self_ret);

    //         let body = source_file.add(
    //             env.next_expr_id(),
    //             Expr::Block(body_exprs),
    //             ExprMeta::generated(),
    //         );

    //         let name = Some(Name::Raw("PLACEHOLD".into()));
    //         let init_func = source_file.add(
    //             env.next_expr_id(),
    //             Expr::Func {
    //                 name,
    //                 generics: vec![],
    //                 params: params.clone(),
    //                 body,
    //                 ret: None,
    //                 captures: vec![],
    //             },
    //             ExprMeta::generated(),
    //         );

    //         #[allow(clippy::expect_used)]
    //         let struct_info = symbol_table
    //             .get(&sym)
    //             .cloned()
    //             .expect("didn't get struct for struct???");

    //         let init_expr = source_file.add(
    //             env.next_expr_id(),
    //             Expr::Init(Some(sym), init_func),
    //             ExprMeta::generated(),
    //         );
    //         let definition = struct_info.definition.clone();
    //         let init_sym = symbol_table.add(
    //             "init",
    //             SymbolKind::SyntheticConstructor,
    //             init_expr,
    //             definition,
    //         );

    //         // Make sure it's resolved
    //         source_file.nodes.insert(
    //             init_func,
    //             Expr::Func {
    //                 name: Some(Name::Resolved(init_sym, "init".into())),
    //                 generics: vec![],
    //                 params: params.clone(),
    //                 body,
    //                 ret: None,
    //                 captures: vec![],
    //             },
    //         );

    //         let Some(Expr::Struct { body, .. }) = source_file.get(&struct_info.expr_id).cloned()
    //         else {
    //             tracing::error!(
    //                 "didn't get struct from expr id: {:?}",
    //                 source_file.get(&struct_info.expr_id)
    //             );
    //             return;
    //         };

    //         let Some(Expr::Block(existing_body_ids)) = source_file.get_mut(&body) else {
    //             tracing::error!("didn't get block body");
    //             return;
    //         };

    //         symbol_table.add_initializer(sym, init_expr);

    //         existing_body_ids.insert(0, init_expr);
    //     }
    // }
}

#[cfg(test)]
mod tests {
    // use std::path::PathBuf;

    // use crate::{
    //     NameResolved, SourceFile, SymbolID, SymbolTable, compiling::driver::Driver,
    //     environment::Environment, expr::Expr, name::Name, synthesis::synthesize_inits,
    // };

    // pub fn resolve_with_symbols(
    //     code: &'static str,
    // ) -> (SourceFile<NameResolved>, SymbolTable, Environment) {
    //     let mut driver = Driver::with_str(code);
    //     let resolved = driver
    //         .parse()
    //         .into_iter()
    //         .next()
    //         .unwrap()
    //         .resolved(&mut driver.symbol_table, &driver.config);
    //     let source_file = resolved.source_file(&PathBuf::from("-")).unwrap().clone();

    //     (source_file, driver.symbol_table, resolved.env)
    // }

    // #[test]
    // fn synthesizes_init() {
    //     let (mut resolved, mut symbol_table, mut env) = resolve_with_symbols(
    //         "
    //     struct Person {
    //         let age: Int
    //     }
    //     ",
    //     );

    //     synthesize_inits(&mut resolved, &mut symbol_table, &mut env);

    //     let Some(Expr::Struct { body, .. }) = resolved.get(&resolved.root_ids()[0]) else {
    //         panic!("didn't get struct: {:?}", resolved.roots()[0]);
    //     };

    //     let Some(Expr::Block(ids)) = resolved.get(body) else {
    //         panic!("didn't get struct body")
    //     };

    //     let Some(Expr::Init(_, func_id)) = resolved.get(&ids[0]) else {
    //         panic!("didn't get init")
    //     };

    //     let Some(Expr::Func {
    //         name,
    //         generics,
    //         params,
    //         body,
    //         ret,
    //         captures,
    //     }) = resolved.get(func_id)
    //     else {
    //         panic!("didn't get init func")
    //     };

    //     let Some(Name::Resolved(_, init_name)) = name else {
    //         panic!("didn't get init");
    //     };
    //     assert_eq!(init_name, "init");
    //     assert!(generics.is_empty());
    //     assert_eq!(params.len(), 1);
    //     assert_eq!(ret, &None);
    //     assert!(captures.is_empty());

    //     let Some(Expr::Block(body_ids)) = resolved.get(body) else {
    //         panic!("didn't get body")
    //     };

    //     assert_eq!(body_ids.len(), 2);
    //     let Some(&Expr::Assignment(lhs, rhs)) = resolved.get(&body_ids[0]) else {
    //         panic!("didn't get assignment");
    //     };

    //     let Expr::Member(_, name) = resolved.get(&lhs).unwrap() else {
    //         panic!("didn't get member");
    //     };

    //     assert_eq!(name, "age");

    //     assert_eq!(
    //         resolved.get(&rhs).unwrap(),
    //         &Expr::Variable(Name::Resolved(SymbolID::resolved(3), "age".into()), None)
    //     );
    // }
}
