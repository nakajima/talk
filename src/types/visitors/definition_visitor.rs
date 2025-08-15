use crate::{
    SymbolID,
    expr_id::ExprID,
    name::Name,
    parsed_expr::{Expr, ParsedExpr},
    types::{ty::TypeParameter, type_checking_session::TypeCheckingSession},
};
use derive_visitor::Visitor;
use std::collections::BTreeMap;

#[derive(PartialEq, Debug)]
pub enum Definition {
    TypeParameter(TypeParameter),
    Concrete(SymbolID),
    Infer,
}

#[derive(PartialEq, Debug)]
pub enum TypeScheme {
    Func {
        quantified_vars: Vec<TypeParameter>,
        params: Vec<Definition>,
        returns: Definition,
    },
}

type GenericScope = BTreeMap<SymbolID, TypeParameter>;

#[derive(Visitor)]
#[visitor(ParsedExpr(enter))]
pub struct DefinitionVisitor<'a> {
    pub definitions: BTreeMap<ExprID, TypeScheme>,
    session: &'a mut TypeCheckingSession<'a>,
    generic_scopes: Vec<GenericScope>,
    last_type_parameter_id: u32,
}

impl<'a> DefinitionVisitor<'a> {
    pub fn new(session: &'a mut TypeCheckingSession<'a>) -> Self {
        Self {
            definitions: Default::default(),
            session,
            generic_scopes: Default::default(),
            last_type_parameter_id: 0,
        }
    }

    fn start_scope(&mut self) {
        self.generic_scopes.push(Default::default());
    }

    fn end_scope(&mut self) {
        self.generic_scopes.pop();
    }

    pub fn enter_parsed_expr(&mut self, parsed: &ParsedExpr) {
        match &parsed.expr {
            Expr::Func {
                name,
                generics,
                params,
                body,
                ret,
                captures,
                attributes,
            } => {
                self.start_scope();
                let mut quantified_vars: Vec<TypeParameter> = generics
                    .iter()
                    .map(|generic| {
                        let Expr::TypeRepr {
                            name: Name::Resolved(sym, _),
                            ..
                        } = &generic.expr
                        else {
                            unreachable!();
                        };
                        self.declare(sym)
                    })
                    .collect();

                let params = params
                    .iter()
                    .map(|param| {
                        if let Expr::Parameter(
                            _,
                            Some(box ParsedExpr {
                                expr:
                                    Expr::TypeRepr {
                                        name: Name::Resolved(sym, _),
                                        ..
                                    },
                                ..
                            }),
                        ) = &param.expr
                        {
                            if let Some(type_parameter) = self.lookup(sym) {
                                Definition::TypeParameter(type_parameter)
                            } else {
                                // If the parameter type annotation hasn't been declared for the function, it must be concrete (like Int)
                                Definition::Concrete(*sym)
                            }
                        } else {
                            let type_parameter = self.new_type_parameter();
                            quantified_vars.push(type_parameter);
                            Definition::TypeParameter(type_parameter)
                        }
                    })
                    .collect();

                let returns = if let Some(box ParsedExpr {
                    expr:
                        Expr::TypeRepr {
                            name: Name::Resolved(sym, _),
                            ..
                        },
                    ..
                }) = ret
                {
                    if let Some(type_parameter) = self.lookup(sym) {
                        Definition::TypeParameter(type_parameter)
                    } else {
                        // If the parameter type annotation hasn't been declared for the function, it must be concrete (like Int)
                        Definition::Concrete(*sym)
                    }
                } else {
                    let type_parameter = self.new_type_parameter();
                    quantified_vars.push(type_parameter);
                    Definition::TypeParameter(type_parameter)
                };

                self.definitions.insert(
                    parsed.id,
                    TypeScheme::Func {
                        quantified_vars,
                        params,
                        returns,
                    },
                );

                self.end_scope();
            }
            Expr::TypeRepr {
                name,
                generics,
                conformances,
                introduces_type,
            } => (),
            Expr::LiteralArray(parsed_exprs) => (),
            Expr::Call {
                callee,
                type_args,
                args,
            } => (),
            Expr::ParsedPattern(pattern) => (),
            Expr::Extend {
                name,
                generics,
                conformances,
                body,
            } => (),
            Expr::Struct {
                name,
                generics,
                conformances,
                body,
            } => (),
            Expr::Property {
                name,
                is_static,
                type_repr,
                default_value,
            } => (),
            Expr::Method { func, is_static } => (),

            Expr::FuncTypeRepr(parsed_exprs, parsed_expr, _) => (),
            Expr::TupleTypeRepr(parsed_exprs, _) => (),
            Expr::Init(symbol_id, parsed_expr) => (),

            Expr::Parameter(name, parsed_expr) => (),
            Expr::EnumDecl {
                name,
                conformances,
                generics,
                body,
            } => (),
            Expr::EnumVariant(name, parsed_exprs) => (),
            Expr::ProtocolDecl {
                name,
                associated_types,
                body,
                conformances,
            } => (),
            Expr::FuncSignature {
                name,
                params,
                generics,
                ret,
            } => (),
            _ => (),
        }
    }

    #[allow(clippy::unwrap_used)]
    fn declare(&mut self, symbol_id: &SymbolID) -> TypeParameter {
        let param = self.new_type_parameter();

        self.generic_scopes
            .last_mut()
            .unwrap()
            .insert(*symbol_id, param);

        param
    }

    #[allow(clippy::unwrap_used)]
    fn lookup(&mut self, symbol_id: &SymbolID) -> Option<TypeParameter> {
        self.generic_scopes
            .last_mut()
            .unwrap()
            .get(symbol_id)
            .cloned()
    }

    fn new_type_parameter(&mut self) -> TypeParameter {
        self.last_type_parameter_id += 1;
        TypeParameter(self.last_type_parameter_id)
    }
}

#[cfg(test)]
mod tests {
    use derive_visitor::Drive;

    use super::*;
    use crate::{
        SymbolTable,
        environment::Environment,
        name_resolver::{NameResolver, Scope},
        parser::parse,
        synthesis::synthesize_inits,
    };

    fn visit(code: &'static str) -> (Vec<ParsedExpr>, BTreeMap<ExprID, TypeScheme>) {
        let parsed = parse(code, "-");
        let symbol_table = &mut SymbolTable::base();
        let mut resolved = NameResolver::new(
            Scope::new(crate::builtins::default_name_scope()),
            Default::default(),
            "-",
            &Default::default(),
        )
        .resolve(parsed, symbol_table);

        synthesize_inits(&mut resolved, symbol_table, &mut Environment::new());

        let meta = resolved.meta.borrow();
        let mut session = TypeCheckingSession::new(resolved.roots(), &meta, symbol_table);

        let mut visitor = DefinitionVisitor::new(&mut session);

        for root in resolved.roots() {
            root.drive(&mut visitor);
        }

        let definitions = visitor.definitions;

        (resolved.roots().clone(), definitions)
    }

    #[test]
    fn visits_non_generic_func() {
        let (roots, definitions) = visit("func inty(x: Int) -> Int { x }");
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme::Func {
                quantified_vars: vec![],
                params: vec![Definition::Concrete(SymbolID::INT)],
                returns: Definition::Concrete(SymbolID::INT)
            }
        );
    }
}
