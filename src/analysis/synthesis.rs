use crate::{
    NameResolved, SourceFile, SymbolKind, SymbolTable,
    expr::{Expr, ExprMeta},
    name::Name,
    parser::ExprID,
};

pub fn synthesize_inits(
    source_file: &mut SourceFile<NameResolved>,
    symbol_table: &mut SymbolTable,
) {
    for (sym, table) in symbol_table.types.clone() {
        if table.initializers.is_empty() {
            let mut body_exprs: Vec<ExprID> = vec![];

            // We need to generate an initializer for this struct
            let mut params: Vec<ExprID> = vec![];
            for property in table.properties {
                let param_sym = symbol_table.add(
                    &property.name,
                    crate::SymbolKind::Param,
                    -(source_file.nodes.len() as i32),
                    None,
                );

                let assignment_receiver = source_file.add(
                    Expr::Variable(Name::_Self(sym), None),
                    ExprMeta::generated(),
                );
                let assignment_lhs = source_file.add(
                    Expr::Member(Some(assignment_receiver), property.name.clone()),
                    ExprMeta::generated(),
                );
                let assignment_rhs = source_file.add(
                    Expr::Variable(Name::Resolved(param_sym, property.name.clone()), None),
                    ExprMeta::generated(),
                );
                let assignment = source_file.add(
                    Expr::Assignment(assignment_lhs, assignment_rhs),
                    ExprMeta::generated(),
                );
                body_exprs.push(assignment);

                params.push(source_file.add(
                    Expr::Parameter(
                        Name::Resolved(param_sym, property.name.to_string()),
                        property.type_id,
                    ),
                    ExprMeta::generated(),
                ));
            }

            let body = source_file.add(Expr::Block(body_exprs), ExprMeta::generated());

            let name = Some(Name::Raw("PLACEHOLD".into()));
            let init_func = source_file.add(
                Expr::Func {
                    name,
                    generics: vec![],
                    params: params.clone(),
                    body,
                    ret: None,
                    captures: vec![],
                },
                ExprMeta::generated(),
            );

            let struct_info = symbol_table
                .get(&sym)
                .cloned()
                .expect("didn't get struct for struct???");

            let init_expr =
                source_file.add(Expr::Init(Some(sym), init_func), ExprMeta::generated());
            let definition = struct_info.definition.clone();
            let init_sym = symbol_table.add(
                "init",
                SymbolKind::SyntheticConstructor,
                init_expr,
                definition,
            );

            // Make sure it's resolved
            source_file.nodes[init_func as usize] = Expr::Func {
                name: Some(Name::Resolved(init_sym, "init".into())),
                generics: vec![],
                params: params.clone(),
                body,
                ret: None,
                captures: vec![],
            };

            let Some(Expr::Struct(_, _, body)) = source_file.get(&struct_info.expr_id).cloned()
            else {
                log::error!(
                    "didn't get struct from expr id: {:?}",
                    source_file.get(&struct_info.expr_id)
                );
                return;
            };

            let Some(Expr::Block(existing_body_ids)) = source_file.get_mut(&body) else {
                log::error!("didn't get block body");
                return;
            };

            symbol_table.add_initializer(sym, init_expr);

            existing_body_ids.insert(0, init_expr);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        NameResolved, SourceFile, SymbolID, SymbolTable, expr::Expr, name::Name,
        name_resolver::NameResolver, parser::parse, synthesis::synthesize_inits,
    };

    pub fn resolve_with_symbols(code: &'static str) -> (SourceFile<NameResolved>, SymbolTable) {
        let mut symbol_table = SymbolTable::base();
        let tree = parse(code, "-".into());
        let resolver = NameResolver::new(&mut symbol_table);
        let resolved = resolver.resolve(tree, &mut symbol_table);
        (resolved, symbol_table.clone())
    }

    #[test]
    fn synthesizes_init() {
        let (mut resolved, mut symbol_table) = resolve_with_symbols(
            "
        struct Person {
            let age: Int
        }
        ",
        );

        synthesize_inits(&mut resolved, &mut symbol_table);

        let Some(Expr::Struct(_, _, body)) = resolved.roots()[0] else {
            panic!("didn't get struct")
        };

        let Some(Expr::Block(ids)) = resolved.get(body) else {
            panic!("didn't get struct body")
        };

        let Some(Expr::Init(_, func_id)) = resolved.get(&ids[0]) else {
            panic!("didn't get init")
        };

        let Some(Expr::Func {
            name,
            generics,
            params,
            body,
            ret,
            captures,
        }) = resolved.get(func_id)
        else {
            panic!("didn't get init func")
        };

        assert_eq!(name, &Some(Name::Resolved(SymbolID(4), "init".into())));
        assert!(generics.is_empty());
        assert_eq!(params.len(), 1);
        assert_eq!(ret, &None);
        assert!(captures.is_empty());

        let Some(Expr::Block(body_ids)) = resolved.get(body) else {
            panic!("didn't get body")
        };

        assert_eq!(body_ids.len(), 1);
        assert_eq!(resolved.get(&body_ids[0]), Some(&Expr::Assignment(5, 6)));
    }
}
