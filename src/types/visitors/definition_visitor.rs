use crate::{
    SymbolID,
    expr_id::ExprID,
    name::Name,
    parsed_expr::{Expr, ParsedExpr},
    type_checker::TypeError,
    types::{
        constraint::Constraint, row::Label, ty::TypeParameter, type_var::TypeVar,
        visitors::inference_visitor::NominalRowSet,
    },
};
use derive_visitor::Visitor;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Definition {
    TypeParameter(TypeParameter),
    Concrete(SymbolID),
    Infer,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeSchemeKind<Def> {
    Func {
        quantified_vars: Vec<TypeParameter>,
        params: Vec<Def>,
        returns: Def,
        constraints: Vec<Constraint>,
    },
    Property {
        name: Name,
        value: Def,
    },
    Nominal {
        name: Name,
        quantified_vars: Vec<TypeParameter>,
        constraints: Vec<Constraint>,
        methods: Vec<(Label, TypeScheme<Def>)>,
        properties: Vec<(Label, Def)>,
        canonical_rows: NominalRowSet,
    },
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeScheme<Def> {
    pub kind: TypeSchemeKind<Def>,
    pub named_generics: BTreeMap<SymbolID, TypeParameter>,
}

#[derive(Clone, Debug, Default)]
pub struct NominalScope {
    meta_methods: Vec<(Label, TypeScheme<Definition>)>,
    meta_properties: Vec<(Label, Definition)>,
    methods: Vec<(Label, TypeScheme<Definition>)>,
    properties: Vec<(Label, Definition)>,
}

#[derive(Clone, Debug, Default)]
pub struct GenericScope {
    type_parameters: BTreeMap<SymbolID, TypeParameter>,
    in_nominal_context: bool,
}

#[derive(Visitor, Debug, Default)]
#[visitor(ParsedExpr)]
pub struct DefinitionVisitor {
    pub definitions: BTreeMap<ExprID, TypeScheme<Definition>>,
    generic_scopes: Vec<GenericScope>,
    nominal_scopes: Vec<NominalScope>,
    last_type_parameter_id: u32,
    errors: Vec<TypeError>,
}

impl DefinitionVisitor {
    pub fn new() -> Self {
        Self {
            definitions: Default::default(),
            generic_scopes: Default::default(),
            nominal_scopes: Default::default(),
            last_type_parameter_id: 0,
            errors: vec![],
        }
    }

    fn start_scope(&mut self, in_nominal_context: bool) {
        self.generic_scopes.push(GenericScope {
            type_parameters: Default::default(),
            in_nominal_context,
        });
    }

    fn start_nominal_scope(&mut self) {
        self.nominal_scopes.push(NominalScope {
            properties: Default::default(),
            methods: Default::default(),
            meta_properties: Default::default(),
            meta_methods: Default::default(),
        })
    }

    fn end_scope(&mut self) {
        self.generic_scopes.pop();
    }

    fn end_nominal_scope(&mut self) -> NominalScope {
        self.nominal_scopes.pop().expect("no nominal scope to end")
    }

    // Helper to extract symbol from TypeRepr
    fn get_type_repr_symbol(&self, expr: &ParsedExpr) -> Option<(SymbolID, String)> {
        if let Expr::TypeRepr {
            name: Name::Resolved(sym, name_str),
            ..
        } = &expr.expr
        {
            Some((*sym, name_str.to_string()))
        } else {
            None
        }
    }

    fn handle_generics_list(&mut self, generics: &[ParsedExpr]) -> Vec<TypeParameter> {
        let mut result = vec![];
        for generic in generics {
            if let Some((sym, name)) = self.get_type_repr_symbol(generic) {
                result.push(self.declare(&sym, &name));
            }
        }
        result
    }

    // Helper to resolve a type annotation
    fn resolve_type_annotation(&self, sym: SymbolID) -> Definition {
        if let Some(type_param) = self.lookup(&sym) {
            Definition::TypeParameter(type_param)
        } else {
            Definition::Concrete(sym)
        }
    }

    // Helper to process a parameter
    fn process_parameter(
        &mut self,
        param: &ParsedExpr,
        quantified_vars: &mut Vec<TypeParameter>,
    ) -> Definition {
        tracing::trace!(
            "process parameter: {:?}, in nominal: {:?}",
            param,
            self.in_nominal_context()
        );
        match &param.expr {
            Expr::Parameter(_, Some(type_expr)) => self
                .get_type_repr_symbol(type_expr)
                .map(|(sym, _string)| self.resolve_type_annotation(sym))
                .unwrap_or(Definition::Infer),
            Expr::Parameter(_, None) if !self.in_nominal_context() => {
                // No annotation - create implicit type parameter
                let type_param = self.new_type_parameter();
                quantified_vars.push(type_param);
                Definition::TypeParameter(type_param)
            }
            _ => Definition::Infer, // Shouldn't happen but graceful fallback
        }
    }

    pub fn enter_parsed_expr(&mut self, parsed: &ParsedExpr) {
        match &parsed.expr {
            Expr::Func {
                generics,
                params,
                ret,
                ..
            } => {
                self.start_scope(self.in_nominal_context());

                // Collect explicit generics
                let mut quantified_vars: Vec<TypeParameter> = if self.in_nominal_context() {
                    self.current_type_parameters()
                } else {
                    vec![]
                };

                for generic in generics {
                    if let Some((sym, name)) = self.get_type_repr_symbol(generic) {
                        let type_param = self.declare(&sym, &name);
                        quantified_vars.push(type_param);
                    }
                }

                // Process parameters
                let params = params
                    .iter()
                    .map(|p| self.process_parameter(p, &mut quantified_vars))
                    .collect();

                // Process return type
                let returns = ret
                    .as_ref()
                    .and_then(|r| self.get_type_repr_symbol(r))
                    .map(|sym| self.resolve_type_annotation(sym.0))
                    .unwrap_or(Definition::Infer);

                self.definitions.insert(
                    parsed.id,
                    TypeScheme {
                        named_generics: self.collect_named_generics(),
                        kind: TypeSchemeKind::Func {
                            quantified_vars,
                            params,
                            returns,
                            constraints: vec![],
                        },
                    },
                );
            }
            Expr::Struct { name, generics, .. } | Expr::EnumDecl { name, generics, .. } => {
                self.start_scope(true);
                self.start_nominal_scope();
                let quantified_vars = self.handle_generics_list(generics);

                self.definitions.insert(
                    parsed.id,
                    TypeScheme {
                        named_generics: self.collect_named_generics(),
                        kind: TypeSchemeKind::Nominal {
                            canonical_rows: Default::default(),
                            name: name.clone(),
                            quantified_vars,
                            constraints: vec![],

                            methods: Default::default(),
                            properties: Default::default(),
                        },
                    },
                );
            }
            Expr::Property {
                name,
                type_repr,
                is_static,
                ..
            } => {
                let property_def = if let Some(type_repr) = type_repr
                    && let Some(def) = self
                        .get_type_repr_symbol(type_repr)
                        .map(|(sym, _string)| self.resolve_type_annotation(sym))
                {
                    def
                } else {
                    Definition::Infer
                };

                let Some(nominal_scope) = self.nominal_scopes.last_mut() else {
                    unreachable!("no nominal scope");
                };

                if *is_static {
                    nominal_scope
                        .meta_properties
                        .push((Label::String(name.name_str().to_string()), property_def.clone()));
                } else {
                    nominal_scope
                        .properties
                        .push((Label::String(name.name_str().to_string()), property_def.clone()));
                }

                self.definitions.insert(
                    parsed.id,
                    TypeScheme {
                        kind: TypeSchemeKind::Property {
                            name: name.clone(),
                            value: property_def,
                        },
                        named_generics: Default::default(),
                    },
                );
            }
            Expr::EnumVariant(_, values) => {
                if values.is_empty() {
                    return;
                }

                let params = values
                    .iter()
                    .map(|p| {
                        if let Some((symbol_id, _)) = self.get_type_repr_symbol(p) {
                            self.resolve_type_annotation(symbol_id)
                        } else {
                            self.errors.push(TypeError::Unknown(
                                "Unable to determine enum variant value".to_string(),
                            ));

                            Definition::Infer
                        }
                    })
                    .collect();

                self.definitions.insert(
                    parsed.id,
                    TypeScheme {
                        named_generics: Default::default(),
                        kind: TypeSchemeKind::Func {
                            quantified_vars: self.current_type_parameters(),
                            params,
                            returns: Definition::Infer,
                            constraints: vec![],
                        },
                    },
                );
            }
            _ => (),
        }
    }

    pub fn exit_parsed_expr(&mut self, parsed: &ParsedExpr) {
        match &parsed.expr {
            Expr::Func { .. } => {
                self.end_scope();
            }
            Expr::Struct { .. } | Expr::EnumDecl { .. } => {
                self.end_scope();
                self.end_nominal_scope();
            }
            _ => (),
        }
    }

    fn collect_named_generics(&self) -> BTreeMap<SymbolID, TypeParameter> {
        let mut result = BTreeMap::<SymbolID, TypeParameter>::default();
        for scope in self.generic_scopes.iter() {
            result.extend(scope.type_parameters.clone())
        }
        result
    }

    #[allow(clippy::unwrap_used)]
    fn declare(&mut self, symbol_id: &SymbolID, name: &str) -> TypeParameter {
        tracing::trace!("declaring {name} -> {:?}", self.last_type_parameter_id + 1);

        let param = self.new_type_parameter();

        self.generic_scopes
            .last_mut()
            .unwrap()
            .type_parameters
            .insert(*symbol_id, param);

        param
    }

    fn current_type_parameters(&self) -> Vec<TypeParameter> {
        let mut result = vec![];
        for scope in self.generic_scopes.iter() {
            result.extend(scope.type_parameters.values())
        }
        result
    }

    #[allow(clippy::unwrap_used)]
    fn in_nominal_context(&self) -> bool {
        self.generic_scopes
            .last()
            .map(|s| s.in_nominal_context)
            .unwrap_or(false)
    }

    #[allow(clippy::unwrap_used)]
    fn lookup(&self, symbol_id: &SymbolID) -> Option<TypeParameter> {
        self.generic_scopes
            .last()
            .unwrap()
            .type_parameters
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
        SymbolTable, btreemap,
        environment::Environment,
        name_resolver::{NameResolver, Scope},
        parser::parse,
        synthesis::synthesize_inits,
    };

    fn visit(code: &'static str) -> (Vec<ParsedExpr>, BTreeMap<ExprID, TypeScheme<Definition>>) {
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

        let mut visitor = DefinitionVisitor::new();

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
            &TypeScheme {
                named_generics: Default::default(),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![],
                    params: vec![Definition::Concrete(SymbolID::INT)],
                    returns: Definition::Concrete(SymbolID::INT),
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_generic_func() {
        let (roots, definitions) = visit("func fizz<T>(x: T) -> T { x }");
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![Definition::TypeParameter(TypeParameter(1))],
                    returns: Definition::TypeParameter(TypeParameter(1)),
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_generic_func_without_ret_annotation() {
        let (roots, definitions) = visit("func fizz<T>(x: T) { x }");
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![Definition::TypeParameter(TypeParameter(1))],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_polymorphic_func_with_no_annotation() {
        let (roots, definitions) = visit("func fizz(x) { x }");
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: Default::default(),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![Definition::TypeParameter(TypeParameter(1))],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_non_generic_struct() {
        let (roots, definitions) = visit("struct Person {}");
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: Default::default(),
                kind: TypeSchemeKind::Nominal {
                    canonical_rows: Default::default(),
                    name: Name::Resolved(SymbolID::ANY, "Person".to_string()),
                    quantified_vars: vec![],
                    constraints: vec![],

                    methods: Default::default(),
                    properties: Default::default(),
                }
            }
        );
    }

    #[test]
    fn visits_generic_struct() {
        let (roots, definitions) = visit(
            "struct Person<T> {
                let age: T
            }",
        );
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Nominal {
                    name: Name::Resolved(SymbolID::ANY, "Person".to_string()),
                    canonical_rows: Default::default(),
                    quantified_vars: vec![TypeParameter(1)],
                    constraints: vec![],

                    methods: Default::default(),
                    properties: Default::default(),
                }
            }
        );
    }

    #[test]
    fn visits_generic_struct_init() {
        let (roots, definitions) = visit(
            "struct Person<T> {
                let age: T

                init(age) {
                    self.age = age
                }
            }",
        );

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let Expr::Init(_, func) = &body_exprs[1].expr else {
            unreachable!()
        };

        let definition = definitions.get(&func.id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![Definition::Infer],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_non_generic_property() {
        let (roots, definitions) = visit(
            "struct Person {
                let age: Int

                init(age) {
                    self.age = age
                }
            }",
        );

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let definition = definitions.get(&body_exprs[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                kind: TypeSchemeKind::Property {
                    name: Name::Resolved(SymbolID::ANY, "age".to_string()),
                    value: Definition::Concrete(SymbolID::INT)
                },
                named_generics: Default::default(),
            }
        );
    }

    #[test]
    fn visits_generic_property() {
        let (roots, definitions) = visit(
            "struct Person<T> {
                let age: T

                init(age) {
                    self.age = age
                }
            }",
        );

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let definition = definitions.get(&body_exprs[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                kind: TypeSchemeKind::Property {
                    name: Name::Resolved(SymbolID::ANY, "age".to_string()),
                    value: Definition::TypeParameter(TypeParameter(1))
                },
                named_generics: Default::default(),
            }
        );
    }

    #[test]
    fn visits_non_generic_method() {
        let (roots, definitions) = visit(
            "struct Person {
                let age: Int

                init(age) {
                    self.age = age
                }

                func getAge() {
                    self.age
                }
            }",
        );

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let Expr::Method { func, .. } = &body_exprs[2].expr else {
            unreachable!()
        };

        let definition = definitions.get(&func.id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: Default::default(),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![],
                    params: vec![],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_generic_struct_method() {
        let (roots, definitions) = visit(
            "struct Person<T> {
                let age: T

                func getAge() {
                    self.age
                }
            }",
        );

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let Expr::Method { func, .. } = &body_exprs[2].expr else {
            unreachable!()
        };

        let definition = definitions.get(&func.id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_generic_struct_generic_method() {
        let (roots, definitions) = visit(
            "struct Person<T> {
                let age: T

                func getAge<U>(u: U) {
                    self.age
                }
            }",
        );

        let Expr::Struct {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let Expr::Method { func, .. } = &body_exprs[2].expr else {
            unreachable!()
        };

        let definition = definitions.get(&func.id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID(2) => TypeParameter(1), SymbolID(5) => TypeParameter(2)),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1), TypeParameter(2)],
                    params: vec![Definition::TypeParameter(TypeParameter(2))],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_nongeneric_enum() {
        let (roots, definitions) = visit("enum Fizz { case buzz }");

        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: Default::default(),
                kind: TypeSchemeKind::Nominal {
                    constraints: vec![],

                    canonical_rows: Default::default(),
                    name: Name::Resolved(SymbolID::ANY, "Fizz".to_string()),
                    quantified_vars: vec![],
                    methods: Default::default(),
                    properties: Default::default(),
                }
            }
        );
    }

    #[test]
    fn visits_generic_enum() {
        let (roots, definitions) = visit(
            "enum Person<T> {
                case hi(T), bye
            }",
        );
        let definition = definitions.get(&roots[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Nominal {
                    name: Name::Resolved(SymbolID::ANY, "Person".to_string()),
                    canonical_rows: Default::default(),
                    quantified_vars: vec![TypeParameter(1)],
                    constraints: vec![],

                    methods: Default::default(),
                    properties: Default::default(),
                }
            }
        );

        let Expr::EnumDecl {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let definition = definitions.get(&body_exprs[0].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: Default::default(),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![Definition::TypeParameter(TypeParameter(1))],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }

    #[test]
    fn visits_generic_enum_method() {
        let (roots, definitions) = visit(
            "enum Person<T> {
                case age(T)

                func getAge() {
                    self
                }
            }",
        );

        let Expr::EnumDecl {
            body:
                box ParsedExpr {
                    expr: Expr::Block(body_exprs),
                    ..
                },
            ..
        } = &roots[0].expr
        else {
            unreachable!()
        };

        let definition = definitions.get(&body_exprs[1].id).unwrap();
        assert_eq!(
            definition,
            &TypeScheme {
                named_generics: btreemap!(SymbolID::ANY => TypeParameter(1)),
                kind: TypeSchemeKind::Func {
                    quantified_vars: vec![TypeParameter(1)],
                    params: vec![],
                    returns: Definition::Infer,
                    constraints: vec![],
                }
            }
        );
    }
}
