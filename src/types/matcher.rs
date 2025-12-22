use indexmap::{IndexSet, indexset};

use crate::{
    diagnostic::{Diagnostic, Severity},
    name_resolution::symbol::Symbol,
    types::{
        ty::Ty,
        type_error::TypeError,
        type_session::Types,
        typed_ast::{TypedExpr, TypedPattern, TypedPatternKind},
    },
};

pub struct MatcherCheckResult {
    pub diagnostics: IndexSet<Diagnostic<TypeError>>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum RequiredConstructor {
    LiteralTrue,
    LiteralFalse,
    Int,
    Variant { name: String },
    Tuple,
    Record,
    Nominal,
    Infinite,
}

impl RequiredConstructor {
    fn satisfied_by(&self, pattern: &TypedPattern<Ty>) -> bool {
        if let TypedPatternKind::Or(patterns) = &pattern.kind {
            return patterns.iter().any(|pattern| self.satisfied_by(pattern));
        }

        match self {
            Self::LiteralTrue => matches!(pattern.kind, TypedPatternKind::LiteralTrue),
            Self::LiteralFalse => matches!(pattern.kind, TypedPatternKind::LiteralFalse),
            Self::Int => todo!(),
            Self::Variant { name } => todo!(),
            Self::Tuple => todo!(),
            Self::Record => todo!(),
            Self::Nominal => todo!(),
            Self::Infinite => false,
        }
    }
}

pub enum ConstructorSet {
    Finite(IndexSet<RequiredConstructor>),
    Infinite,
}

type PatternMatrixRow<'a> = Vec<&'a TypedPattern<Ty>>;
type PatternMatrix<'a> = Vec<PatternMatrixRow<'a>>;

pub struct Matcher<'a> {
    pub scrutinee: TypedExpr<Ty>,
    pub patterns: Vec<TypedPattern<Ty>>,
    types: &'a Types,
}

impl<'a> Matcher<'a> {
    pub fn check(self) -> MatcherCheckResult {
        let mut diagnostics: IndexSet<Diagnostic<TypeError>> = Default::default();
        let matrix = self.pattern_matrix();
        let required = self.required_constructors(&self.scrutinee.ty);
        let mut handled = IndexSet::<RequiredConstructor>::default();
        for row in &matrix {
            let Some(head) = row.first() else {
                continue;
            };

            let satisfied = self.satisfied_constructors(head, &required);

            if handled.is_superset(&satisfied) {
                println!("{head:?}");
                diagnostics.insert(Diagnostic {
                    id: row.first().map(|r| r.id).unwrap_or(self.scrutinee.id),
                    severity: Severity::Warn,
                    kind: TypeError::UselessMatchArm,
                });
            }

            handled.extend(satisfied);
        }

        if !required.is_empty() {
            diagnostics.insert(Diagnostic {
                id: self.scrutinee.id,
                severity: Severity::Error,
                kind: TypeError::NonExhaustiveMatch(required.into_iter().collect()),
            });
        }

        MatcherCheckResult { diagnostics }
    }

    pub fn satisfied_constructors(
        &self,
        head: &TypedPattern<Ty>,
        required: &IndexSet<RequiredConstructor>,
    ) -> IndexSet<RequiredConstructor> {
        required
            .into_iter()
            .filter(|&constructor| constructor.satisfied_by(head))
            .cloned()
            .collect()
    }

    pub fn pattern_matrix(&'a self) -> PatternMatrix<'a> {
        self.patterns.iter().map(|p| vec![p]).collect()
    }

    pub fn required_constructors(&self, scrutinee: &Ty) -> IndexSet<RequiredConstructor> {
        match scrutinee {
            Ty::Primitive(sym) => match *sym {
                Symbol::Bool => indexset! {
                    RequiredConstructor::LiteralTrue,
                    RequiredConstructor::LiteralFalse
                },
                Symbol::Int => indexset! {
                    RequiredConstructor::Infinite,
                },
                _ => unreachable!(),
            },
            Ty::Tuple(items) => todo!(),
            Ty::Record(symbol, row) => todo!(),
            Ty::Nominal { symbol, type_args } => todo!(),
            Ty::Func(..) | Ty::Constructor { .. } | Ty::Param(..) => {
                indexset! { RequiredConstructor::Infinite }
            }
        }
    }
}

#[cfg(test)]
pub mod tests {
    use indexmap::indexset;

    use super::*;
    use crate::{
        compiling::driver::{Driver, DriverConfig, Source},
        diagnostic::Severity,
        node_id::NodeID,
        types::typed_ast::{TypedExpr, TypedExprKind, TypedStmt, TypedStmtKind},
    };

    fn matcher_for<'a>(code: &str) -> Matcher<'a> {
        let typed = Driver::new(vec![Source::from(code)], DriverConfig::new("MatcherTests"))
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let TypedStmt {
            kind:
                TypedStmtKind::Expr(TypedExpr {
                    kind: TypedExprKind::Match(box scrutinee, arms),
                    ..
                }),
            ..
        } = typed
            .phase
            .ast
            .stmts
            .into_iter()
            .last()
            .expect("didn't get last stmt")
        else {
            panic!("didn't get match expr");
        };

        let types = Box::new(typed.phase.types);
        let types = Box::leak(types);

        Matcher {
            scrutinee,
            patterns: arms.into_iter().map(|arm| arm.pattern).collect(),
            types,
        }
    }

    #[test]
    fn match_bools() {
        assert!(
            matcher_for("match true { true -> 1, false -> 2, }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert!(
            matcher_for("match true { true | false -> 1 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert!(
            matcher_for("match true { _ -> 1 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert_eq!(
            matcher_for("match true { true -> 1}").check().diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::LiteralFalse]) }
            }
        );

        assert_eq!(
            matcher_for("match true { true | false -> 1, true -> 2 }")
                .check()
                .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Warn, kind: TypeError::UselessMatchArm }
            }
        )
    }

    #[test]
    fn match_ints() {
        assert_eq!(
            matcher_for("match 123 { 1 -> 1, 2 -> 2, _ -> 1 }")
                .check()
                .diagnostics,
            indexset! {}
        );

        assert!(
            matcher_for("match true { true | false -> 1 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert!(
            matcher_for("match true { _ -> 1 }")
                .check()
                .diagnostics
                .is_empty()
        );

        assert_eq!(
            matcher_for("match true { true -> 1}").check().diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Error, kind: TypeError::NonExhaustiveMatch(vec![RequiredConstructor::LiteralFalse]) }
            }
        );

        assert_eq!(
            matcher_for("match true { true | false -> 1, true -> 2 }")
                .check()
                .diagnostics,
            indexset! {
                Diagnostic { id: NodeID::ANY, severity: Severity::Warn, kind: TypeError::UselessMatchArm }
            }
        )
    }
}
