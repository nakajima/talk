use std::{fmt::Debug, str::FromStr};

use crate::lowering::{
    lowerer::{BasicBlock, BasicBlockID, IRFunction, IRProgram, IRType, Instr, RefKind, Register},
    parser::lexer::{Lexer, Token, Tokind},
};

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken(Vec<Tokind>, Tokind),
    UnexpectedEOF,
}

#[derive(Debug)]
pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) previous: Option<Token>,
    pub(crate) current: Option<Token>,
    pub(crate) functions: Vec<IRFunction>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        let mut parser = Parser {
            lexer,
            previous: None,
            current: None,
            functions: vec![],
        };

        parser.advance();
        parser
    }

    fn parse(mut self) -> Result<IRProgram, ParserError> {
        self.skip_newlines();
        while let Some(current) = self.current.clone() {
            self.skip_newlines();

            if current.kind == Tokind::EOF {
                break;
            }

            let func = self.func()?;

            self.functions.push(func);
            self.skip_newlines();
        }

        Ok(IRProgram {
            functions: self.functions,
            symbol_table: None,
        })
    }

    fn func(&mut self) -> Result<IRFunction, ParserError> {
        self.consume(Tokind::Func)?;
        self.consume(Tokind::At)?;
        let name = self.identifier()?;
        let params = self.parameters()?;
        let ret = self.type_repr()?;

        let mut blocks: Vec<BasicBlock> = vec![];

        while !self.peek_matches(Tokind::Func) && !self.peek_matches(Tokind::EOF) {
            blocks.push(self.basic_block(blocks.len())?);
        }

        Ok(IRFunction {
            name,
            ty: IRType::Func(params.iter().map(|p| p.1.clone()).collect(), ret.into()),
            blocks,
        })
    }

    fn basic_block(&mut self, i: usize) -> Result<BasicBlock, ParserError> {
        let id = if i == 0 {
            self.consume(Tokind::Entry)?;
            0
        } else {
            self.consume(Tokind::Hash)?;
            let Some(Token {
                kind: Tokind::ConstInt(val),
                ..
            }) = self.advance()
            else {
                return Err(ParserError::UnexpectedToken(
                    vec![Tokind::ConstInt("".into())],
                    self.current.clone().unwrap().kind,
                ));
            };
            str::parse(&val).unwrap()
        };

        self.consume(Tokind::Colon)?;
        self.skip_newlines();

        let mut instructions = vec![];

        while let Some(Token {
            kind: Tokind::Percent | Tokind::Ret,
            ..
        }) = self.current
        {
            self.skip_newlines();
            instructions.push(self.instruction()?);
            self.skip_newlines();
        }

        Ok(BasicBlock {
            id: BasicBlockID(id as u32),
            label: None,
            instructions,
        })
    }

    fn instruction(&mut self) -> Result<Instr, ParserError> {
        let instr = if self.did_match(Tokind::Percent)? {
            let reg_id = self.integer()?;
            let dest = Register(reg_id);
            self.consume(Tokind::Equals)?;

            let Some(current) = self.current.clone() else {
                return Err(ParserError::UnexpectedEOF);
            };

            match &current.kind {
                Tokind::Int => {
                    self.advance();
                    let int = self.integer()?;
                    Ok(Instr::ConstantInt(dest, int))
                }
                Tokind::Identifier(name) => {
                    self.advance();
                    match name.as_str() {
                        "add" => {
                            let ty = self.type_repr()?;
                            let op1 = self.register()?;
                            self.consume(Tokind::Comma)?;
                            let op2 = self.register()?;
                            Ok(Instr::Add(dest, ty, op1, op2))
                        }
                        "sub" => {
                            let ty = self.type_repr()?;
                            let op1 = self.register()?;
                            self.consume(Tokind::Comma)?;
                            let op2 = self.register()?;
                            Ok(Instr::Sub(dest, ty, op1, op2))
                        }
                        "mul" => {
                            let ty = self.type_repr()?;
                            let op1 = self.register()?;
                            self.consume(Tokind::Comma)?;
                            let op2 = self.register()?;
                            Ok(Instr::Mul(dest, ty, op1, op2))
                        }
                        "div" => {
                            let ty = self.type_repr()?;
                            let op1 = self.register()?;
                            self.consume(Tokind::Comma)?;
                            let op2 = self.register()?;
                            Ok(Instr::Div(dest, ty, op1, op2))
                        }
                        _ => todo!("unhandled instr ident: {:?}", name),
                    }
                }
                Tokind::At => {
                    self.advance();
                    let name = self.identifier()?;
                    Ok(Instr::Ref(
                        dest,
                        IRType::Func(vec![], IRType::Void.into()),
                        RefKind::Func(name),
                    ))
                }
                _ => todo!(),
            }
        } else if self.did_match(Tokind::Ret)? {
            if let Ok(ty) = self.type_repr() {
                let reg = self.register()?;
                Ok(Instr::Ret(Some((ty, reg))))
            } else {
                Ok(Instr::Ret(None))
            }
        } else {
            todo!("unhandled instr token: {:?}", self.current)
        };

        self.consume(Tokind::Semicolon)?;

        instr
    }

    fn register(&mut self) -> Result<Register, ParserError> {
        self.consume(Tokind::Percent)?;
        let id = self.integer()?;
        Ok(Register(id))
    }

    fn integer<T: FromStr>(&mut self) -> Result<T, ParserError>
    where
        T::Err: Debug,
    {
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEOF);
        };

        let Tokind::ConstInt(ref val) = current.kind else {
            return Err(ParserError::UnexpectedToken(
                vec![Tokind::ConstInt("".into())],
                current.clone().kind,
            ));
        };

        self.advance();

        Ok(str::parse(val).expect("Could not parse integer"))
    }

    fn type_repr(&mut self) -> Result<IRType, ParserError> {
        let ty = match &self.current {
            Some(tok) => match tok.kind {
                Tokind::Int => {
                    self.advance();
                    IRType::Int
                }
                Tokind::Float => {
                    self.advance();
                    IRType::Float
                }
                Tokind::Bool => {
                    self.advance();
                    IRType::Bool
                }
                Tokind::Void => {
                    self.advance();
                    IRType::Void
                }
                Tokind::LeftParen => {
                    let params = self.parameters()?.into_iter().map(|p| p.1).collect();
                    let ret = self.type_repr()?;
                    IRType::Func(params, ret.into())
                }
                _ => todo!("{:?}", tok.kind),
            },
            _ => return Err(ParserError::UnexpectedEOF),
        };

        Ok(ty)
    }

    fn identifier(&mut self) -> Result<String, ParserError> {
        let Some(Token {
            kind: Tokind::Identifier(ident),
            ..
        }) = self.current.clone()
        else {
            return Err(ParserError::UnexpectedToken(
                vec![
                    self.current
                        .clone()
                        .expect("Could not get expected token")
                        .kind,
                ],
                Tokind::Identifier("_".into()),
            ));
        };

        self.advance();

        Ok(ident.to_string())
    }

    fn parameters(&mut self) -> Result<Vec<(Register, IRType)>, ParserError> {
        self.consume(Tokind::LeftParen)?;
        let mut results = vec![];
        while !self.did_match(Tokind::RightParen)? {
            let ty = self.type_repr()?;

            self.consume(Tokind::Percent)?;
            let Some(Token {
                kind: Tokind::ConstInt(val),
                ..
            }) = self.advance()
            else {
                todo!();
            };

            let register = Register(str::parse(&val).unwrap());

            results.push((register, ty))
        }

        Ok(results)
    }

    fn skip_newlines(&mut self) {
        while {
            if let Some(token) = &self.current {
                token.kind == Tokind::Newline
            } else {
                false
            }
        } {
            self.advance();
        }
    }

    fn peek_matches(&self, tokind: Tokind) -> bool {
        if let Some(current) = &self.current {
            current.kind == tokind
        } else {
            false
        }
    }

    fn advance(&mut self) -> Option<Token> {
        self.previous = self.current.clone();
        self.current = self.lexer.next().ok();
        self.previous.clone()
    }

    // Try to get a specific token. If it's a match, return true.
    pub(super) fn did_match(&mut self, expected: Tokind) -> Result<bool, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone() {
            if current.kind == expected {
                self.advance();
                return Ok(true);
            };
        }

        Ok(false)
    }

    // Try to get a specific token. If it's not a match, return an error.
    pub(super) fn consume(&mut self, expected: Tokind) -> Result<Token, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone() {
            if current.kind == expected {
                self.advance();
                return Ok(current);
            };
        }

        Err(ParserError::UnexpectedToken(
            vec![expected],
            self.current
                .clone()
                .expect("Could not get current token")
                .kind,
        ))
    }
}

pub fn parse(code: &str) -> Result<IRProgram, ParserError> {
    let lexer = Lexer::new(code);
    let parser = Parser::new(lexer);
    parser.parse()
}

#[cfg(test)]
mod tests {
    use crate::{
        check,
        lowering::{
            lowerer::{BasicBlockID, IRError, IRProgram, IRType, Instr, Lowerer, Register},
            parser::parser::parse,
        },
    };
    use indoc::formatdoc;

    fn lower(input: &'static str) -> Result<IRProgram, IRError> {
        let typed = check(input).unwrap();
        let lowerer = Lowerer::new(typed);
        lowerer.lower()
    }

    #[test]
    fn parses_fn() {
        let func = &parse(&formatdoc!(
            r#"
        func @main() int
          entry:
            %1 = int 1;
            %2 = int 2;
            %3 = add int %1, %2;
            ret int %3;
        "#
        ))
        .unwrap()
        .functions[0];

        assert_eq!(func.args().len(), 0);
        assert_eq!(func.ret(), &IRType::Int);

        let bb = &func.blocks[0];
        assert_eq!(bb.id, BasicBlockID(0));
        assert_eq!(bb.instructions[0], Instr::ConstantInt(Register(1), 1));
        assert_eq!(bb.instructions[1], Instr::ConstantInt(Register(2), 2));
        assert_eq!(
            bb.instructions[2],
            Instr::Add(Register(3), IRType::Int, Register(1), Register(2))
        );
        assert_eq!(
            bb.instructions[3],
            Instr::Ret(Some((IRType::Int, Register(3))))
        );
    }

    #[test]
    fn round_trips() {
        let program = lower(
            "
        func add(x) { 1 + x }
        ",
        )
        .unwrap();

        let func = crate::lowering::ir_printer::print(&program);
        let parsed = parse(&func).unwrap();

        assert_eq!(parsed.functions.len(), 2);
    }
}
