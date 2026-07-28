//! The parse-tree assertion DSL shared by desugar and resolution
//! tests (ADR 0043 Stage 5: the Rust parser and its test suite are
//! deleted; `parse` runs the self-hosted frontend).
#[cfg(test)]
pub mod tests {
    use crate::ast::{AST, Parsed};
    use crate::node_id::FileID;

    #[macro_export]
    macro_rules! expr {
        ($expr:pat) => {
            Expr {
                id: _,
                span: _,
                kind: $expr,
            }
        };
    }

    #[macro_export]
    macro_rules! invocation {
        // type_args: Vec<TypeAnnotation>,
        // args: Vec<CallArg>,
        ($receiver:expr, $member:expr, $args:expr) => {
            $crate::node_kinds::expr::Expr {
                id: NodeID::ANY,
                span: Span::ANY,
                kind: ExprKind::Call {
                    callee: any_expr!($crate::node_kinds::expr::ExprKind::Member(
                        Some(any_expr!($receiver).into()),
                        $member.into(),
                        Span::ANY,
                    ))
                    .into(),
                    type_args: vec![],
                    args: $args,
                    trailing_block: None,
                    desugared_operator: None,
                },
            }
        };
    }

    #[macro_export]
    macro_rules! expr_stmt {
        ($expr:pat) => {
            Stmt {
                id: _,
                span: _,
                kind: StmtKind::Expr(Expr {
                    id: _,
                    span: _,
                    kind: $expr,
                }),
            }
        };
    }

    #[macro_export]
    macro_rules! any_expr_stmt {
        ($expr:expr) => {
            $crate::node_kinds::stmt::Stmt {
                id: $crate::node_id::NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                kind: $crate::node_kinds::stmt::StmtKind::Expr(
                    $crate::parsing::node_kinds::expr::Expr {
                        id: $crate::node_id::NodeID::ANY,
                        span: $crate::parsing::span::Span::ANY,
                        kind: $expr,
                    },
                ),
            }
            .into()
        };
    }

    #[macro_export]
    macro_rules! any_decl {
        ($expr:expr) => {
            $crate::node_kinds::decl::Decl {
                id: NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                visibility: $crate::node_kinds::decl::Visibility::default(),
                kind: $expr,
            }
        };
    }

    #[macro_export]
    macro_rules! annotation {
        ($expr:expr) => {
            $crate::parsing::node_kinds::type_annotation::TypeAnnotation {
                id: NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                kind: $expr,
            }
        };
    }

    #[macro_export]
    macro_rules! nominal_annotation {
        ($expr:expr) => {
            $crate::parsing::node_kinds::type_annotation::TypeAnnotation {
                id: NodeID::ANY,
                span: $crate::parsing::span::Span::ANY,
                kind: $crate::parsing::node_kinds::type_annotation::TypeAnnotationKind::Nominal {
                    name: $expr.to_string().into(),
                    name_span: $crate::parsing::span::Span::ANY,
                    generics: Default::default(),
                },
            }
        };
    }

    #[macro_export]
    macro_rules! any_stmt {
        ($expr:expr) => {
            $crate::node_kinds::stmt::Stmt {
                id: NodeID::ANY,
                kind: $expr,
                span: $crate::parsing::span::Span::ANY,
            }
        };
    }

    pub fn parse(code: &'static str) -> AST<Parsed> {
        crate::compiling::frontend::parse_ast(code, FileID(0), "-")
            .unwrap()
            .0
    }
}
