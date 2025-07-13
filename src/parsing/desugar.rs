use std::collections::VecDeque;

use crate::{
    expr::Expr,
    name::Name,
    parser::{ExprID, Parser, ParserError},
};

pub fn desugar_source_file(parser: &mut Parser) -> Result<(), ParserError> {
    for id in parser.parse_tree.root_ids() {
        desugar_expr(id, parser)?;
    }

    Ok(())
}

pub fn desugar_exprs(ids: &[ExprID], parser: &mut Parser) -> Result<(), ParserError> {
    for id in ids {
        desugar_expr(*id, parser)?;
    }

    Ok(())
}

pub fn desugar_expr(id: ExprID, parser: &mut Parser) -> Result<(), ParserError> {
    let Some(expr) = parser.parse_tree.get(&id).cloned() else {
        return Err(ParserError::UnknownError("Could not desugar expr".into()));
    };

    match &expr {
        Expr::TypeRepr {
            suffixes,
            introduces_type,
            ..
        } => {
            if !introduces_type {
                let mut rev_suffixes = VecDeque::from(suffixes.clone());
                while let Some(_) = rev_suffixes.pop_front() {
                    let tok = parser.push_source_location();
                    let new_inner = parser.add_expr(expr.clone(), tok)?;
                    println!("wrapping {expr:?}");
                    parser.parse_tree.nodes.insert(
                        id,
                        Expr::TypeRepr {
                            name: Name::Raw("Optional".to_string()),
                            generics: vec![new_inner],
                            conformances: vec![],
                            introduces_type: false,
                            suffixes: rev_suffixes.iter().rev().cloned().collect(),
                        },
                    );
                }
            }
        }
        Expr::Incomplete(_) => (),
        Expr::LiteralArray(items) => desugar_exprs(items, parser)?,
        Expr::LiteralInt(_) => (),
        Expr::LiteralFloat(_) => (),
        Expr::LiteralTrue => (),
        Expr::LiteralFalse => (),
        Expr::LiteralString(_) => (),
        Expr::Unary(_, rhs) => desugar_expr(*rhs, parser)?,
        Expr::Binary(lhs, _, rhs) => desugar_exprs(&[*lhs, *rhs], parser)?,
        Expr::Tuple(items) => desugar_exprs(items, parser)?,
        Expr::Block(items) => desugar_exprs(items, parser)?,
        Expr::Call {
            callee,
            type_args,
            args,
        } => {
            desugar_expr(*callee, parser)?;
            desugar_exprs(type_args, parser)?;
            desugar_exprs(args, parser)?;
        }
        Expr::Pattern(_) => (),
        Expr::Return(id) => {
            if let Some(id) = id {
                desugar_expr(*id, parser)?;
            }
        }
        Expr::Break => (),
        Expr::Extend { generics, body, .. } => {
            desugar_exprs(generics, parser)?;
            desugar_expr(*body, parser)?;
        }
        Expr::Struct { generics, body, .. } => {
            desugar_exprs(generics, parser)?;
            desugar_expr(*body, parser)?;
        }
        Expr::Property { type_repr, .. } => {
            if let Some(type_repr) = type_repr {
                desugar_expr(*type_repr, parser)?;
            }
        }
        Expr::Await(_) => (),
        Expr::FuncTypeRepr(items, ret, _) => {
            desugar_exprs(items, parser)?;
            desugar_expr(*ret, parser)?;
        }
        Expr::TupleTypeRepr(items, _) => {
            desugar_exprs(items, parser)?;
        }
        Expr::Member(_, _) => (),
        Expr::Init(_, func) => desugar_expr(*func, parser)?,
        Expr::Func {
            generics,
            params,
            body,
            ret,
            ..
        } => {
            desugar_exprs(generics, parser)?;
            desugar_exprs(params, parser)?;
            desugar_expr(*body, parser)?;
            if let Some(ret) = ret {
                desugar_expr(*ret, parser)?;
            }
        }
        Expr::Parameter(_, ty) => {
            if let Some(ty) = ty {
                desugar_expr(*ty, parser)?
            }
        }
        Expr::CallArg { .. } => (),
        Expr::Let(_, ty) => {
            if let Some(ty) = ty {
                desugar_expr(*ty, parser)?
            }
        }
        Expr::Assignment(lhs, rhs) => desugar_exprs(&[*lhs, *rhs], parser)?,
        Expr::Variable(_, _) => (),
        Expr::If(_, then, alt) => {
            desugar_expr(*then, parser)?;
            if let Some(alt) = alt {
                desugar_expr(*alt, parser)?
            }
        }
        Expr::Loop(_, body) => desugar_expr(*body, parser)?,
        Expr::EnumDecl { generics, body, .. } => {
            desugar_expr(*body, parser)?;
            desugar_exprs(generics, parser)?;
        }
        Expr::EnumVariant(_, items) => desugar_exprs(items, parser)?,
        Expr::Match(_, _) => (),
        Expr::MatchArm(_, _) => (),
        Expr::PatternVariant(_, _, _) => (),
        Expr::ProtocolDecl { body, .. } => desugar_expr(*body, parser)?,
        Expr::FuncSignature {
            params,
            generics,
            ret,
            ..
        } => {
            desugar_exprs(params, parser)?;
            desugar_exprs(generics, parser)?;
            desugar_expr(*ret, parser)?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::{
        SourceFile,
        compiling::compilation_session::SharedCompilationSession,
        environment::Environment,
        filler::{Filler, FullExpr},
        lexer::Lexer,
        parser::parse_fill,
        token::Token,
        token_kind::TokenKind,
    };

    use super::*;

    fn desugar(code: &'static str) -> SourceFile {
        let lexer = Lexer::new(code);
        let mut env = Environment::new();
        let mut parser = Parser::new(
            SharedCompilationSession::default(),
            lexer,
            "-".into(),
            &mut env,
        );
        parser.parse();

        desugar_source_file(&mut parser).unwrap();
        parser.parse_tree
    }

    #[test]
    fn desugars_optionals() {
        let desugared = desugar("func foo(bar: Int?) -> Int? {}");
        let filled = Filler::new(desugared).fill_root();
        use FullExpr::*;
        assert_eq!(
            filled[0],
            Func {
                name: Some("foo".into()),
                generics: vec![],
                params: vec![Parameter(
                    "bar".into(),
                    Some(TypeRepr {
                        name: "Optional".into(),
                        suffixes: vec![],
                        generics: vec![TypeRepr {
                            name: "Int".into(),
                            suffixes: vec![Token {
                                kind: TokenKind::QuestionMark,
                                start: 17,
                                end: 18,
                                line: 0,
                                col: 18
                            }],
                            generics: vec![],
                            conformances: vec![],
                            introduces_type: false
                        }],
                        conformances: vec![],
                        introduces_type: false
                    })
                    .into()
                )],
                body: Block(vec![]).into(),
                ret: Some(TypeRepr {
                    name: "Optional".into(),
                    suffixes: vec![],
                    generics: vec![TypeRepr {
                        name: "Int".into(),
                        suffixes: vec![Token {
                            kind: TokenKind::QuestionMark,
                            start: 26,
                            end: 27,
                            line: 0,
                            col: 27
                        }],
                        generics: vec![],
                        conformances: vec![],
                        introduces_type: false
                    }],
                    conformances: vec![],
                    introduces_type: false
                })
                .into(),
                captures: vec![],
                effects: vec![]
            }
        )
    }

    #[test]
    fn desugars_basic_await() {
        let desugared = desugar(
            "
        func foo() {
            await bar();
        }",
        );

        let full = Filler::new(desugared).fill_root();
        assert_eq!(
            full[0],
            FullExpr::Func {
                name: Some("foo".into()),
                generics: vec![],
                params: vec![],
                body: FullExpr::Block(vec![
                    // ??
                ])
                .into(),
                ret: None.into(),
                captures: vec![],
                effects: vec![],
            }
        )
    }
}
