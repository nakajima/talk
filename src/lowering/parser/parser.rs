use std::{fmt::Debug, str::FromStr};

use crate::lowering::{
    instr::Instr,
    lowerer::{BasicBlock, BasicBlockID, IRFunction, IRProgram, IRType, RefKind, Register},
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

        while !self.peek_matches(Tokind::Hash)
            && !self.peek_matches(Tokind::Entry)
            && !self.peek_matches(Tokind::Func)
            && !self.peek_matches(Tokind::EOF)
        {
            self.skip_newlines();
            if self.current.is_none()
                || self.peek_matches(Tokind::Hash)
                || self.peek_matches(Tokind::Entry)
                || self.peek_matches(Tokind::Func)
                || self.peek_matches(Tokind::EOF)
            {
                break;
            }
            instructions.push(self.instruction()?);
            self.skip_newlines();
        }

        Ok(BasicBlock {
            id: BasicBlockID(id as u32),
            instructions,
        })
    }

    fn instruction(&mut self) -> Result<Instr, ParserError> {
        let instr = if self.peek_matches(Tokind::Percent) {
            self.parse_assignment_instr()?
        } else {
            self.parse_keyword_instr()?
        };

        self.consume(Tokind::Semicolon)?;

        Ok(instr)
    }

    fn parse_assignment_instr(&mut self) -> Result<Instr, ParserError> {
        self.consume(Tokind::Percent)?;
        let reg_id = self.integer()?;
        let dest = Register(reg_id);
        self.consume(Tokind::Equals)?;

        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEOF);
        };

        match current.kind {
            Tokind::Int => {
                self.advance();
                let int = self.integer()?;
                Ok(Instr::ConstantInt(dest, int))
            }
            Tokind::Float => {
                self.advance();
                let float = self.float()?;
                Ok(Instr::ConstantFloat(dest, float))
            }
            Tokind::Bool => {
                self.advance();
                let val = self.boolean()?;
                Ok(Instr::ConstantBool(dest, val))
            }
            Tokind::Add => {
                self.advance();
                let ty = self.type_repr()?;
                let op1 = self.register()?;
                self.consume(Tokind::Comma)?;
                let op2 = self.register()?;
                Ok(Instr::Add(dest, ty, op1, op2))
            }
            Tokind::Sub => {
                self.advance();
                let ty = self.type_repr()?;
                let op1 = self.register()?;
                self.consume(Tokind::Comma)?;
                let op2 = self.register()?;
                Ok(Instr::Sub(dest, ty, op1, op2))
            }
            Tokind::Mul => {
                self.advance();
                let ty = self.type_repr()?;
                let op1 = self.register()?;
                self.consume(Tokind::Comma)?;
                let op2 = self.register()?;
                Ok(Instr::Mul(dest, ty, op1, op2))
            }
            Tokind::Div => {
                self.advance();
                let ty = self.type_repr()?;
                let op1 = self.register()?;
                self.consume(Tokind::Comma)?;
                let op2 = self.register()?;
                Ok(Instr::Div(dest, ty, op1, op2))
            }
            Tokind::At => {
                self.advance();
                let name = self.identifier()?;
                Ok(Instr::Ref(
                    dest,
                    IRType::Func(vec![], IRType::Void.into()),
                    RefKind::Func(format!("@{}", name)),
                ))
            }
            Tokind::Phi => {
                self.advance();
                let ty = self.type_repr()?;
                self.consume(Tokind::LeftBracket)?;
                let mut items = vec![];
                while !self.peek_matches(Tokind::RightBracket) {
                    let bb = self.basic_block_id()?;
                    self.consume(Tokind::Colon)?;
                    let reg = self.register()?;
                    items.push((reg, bb));
                    self.did_match(Tokind::Comma)?;
                }
                self.consume(Tokind::RightBracket)?;
                Ok(Instr::Phi(dest, ty, items))
            }
            Tokind::Eq => {
                self.advance();
                let ty = self.type_repr()?;
                let op1 = self.register()?;
                let op2 = self.register()?;
                Ok(Instr::Eq(dest, ty, op1, op2))
            }
            Tokind::GetEnumTag => {
                self.advance();
                let scrutinee = self.register()?;
                Ok(Instr::GetEnumTag(dest, scrutinee))
            }
            Tokind::GetEnumValue => {
                self.advance();
                let ty = self.type_repr()?;
                let scrutinee = self.register()?;
                let tag = self.integer()?;
                let index = self.integer()?;
                Ok(Instr::GetEnumValue(dest, ty, scrutinee, tag, index))
            }
            Tokind::TagVariant => {
                self.advance();
                let tag = self.integer()?;
                self.consume(Tokind::LeftBracket)?;
                let values = self.call_args()?;
                self.consume(Tokind::RightBracket)?;
                let ty = self.type_repr()?;

                Ok(Instr::TagVariant(dest, ty, tag, values))
            }
            Tokind::Call => {
                self.advance();
                let ty = self.type_repr()?;
                let callee = self.callee()?;
                let args = self.call_args()?;
                Ok(Instr::Call {
                    dest_reg: Some(dest),
                    callee,
                    args,
                    ty,
                })
            }
            _ => todo!("unhandled assignment instr: {:?}", current.kind),
        }
    }

    fn parse_keyword_instr(&mut self) -> Result<Instr, ParserError> {
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEOF);
        };
        match current.kind {
            Tokind::Ret => {
                self.advance();
                if self.peek_matches(Tokind::Semicolon) {
                    return Ok(Instr::Ret(None));
                }
                if let Ok(ty) = self.type_repr() {
                    let reg = self.register()?;
                    Ok(Instr::Ret(Some((ty, reg))))
                } else {
                    Ok(Instr::Ret(None))
                }
            }
            Tokind::Jump => {
                self.advance();
                let bb = self.basic_block_id()?;
                Ok(Instr::Jump(bb))
            }
            Tokind::JumpIf => {
                self.advance();
                let cond = self.register()?;
                let bb = self.basic_block_id()?;
                Ok(Instr::JumpIf(cond, bb))
            }
            Tokind::JumpUnless => {
                self.advance();
                let cond = self.register()?;
                let bb = self.basic_block_id()?;
                Ok(Instr::JumpUnless(cond, bb))
            }
            Tokind::Unreachable => {
                self.advance();
                Ok(Instr::Unreachable)
            }
            Tokind::Call => {
                self.advance();
                let ty = self.type_repr()?;
                let callee = self.callee()?;
                let args = self.call_args()?;
                Ok(Instr::Call {
                    dest_reg: None,
                    callee,
                    args,
                    ty,
                })
            }
            _ => todo!("unhandled keyword instr: {:?}", current.kind),
        }
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
        if self.did_match(Tokind::RightParen)? {
            return Ok(results);
        }

        loop {
            let ty = self.type_repr()?;
            let reg = self.register()?;
            results.push((reg, ty));

            if self.did_match(Tokind::RightParen)? {
                break;
            }
            self.consume(Tokind::Comma)?;
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

    fn boolean(&mut self) -> Result<bool, ParserError> {
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEOF);
        };

        let val = match current.kind {
            Tokind::True => true,
            Tokind::False => false,
            _ => {
                return Err(ParserError::UnexpectedToken(
                    vec![Tokind::True, Tokind::False],
                    current.kind,
                ));
            }
        };
        self.advance();
        Ok(val)
    }

    fn float<T: FromStr>(&mut self) -> Result<T, ParserError>
    where
        T::Err: Debug,
    {
        let Some(current) = self.current.clone() else {
            return Err(ParserError::UnexpectedEOF);
        };

        let Tokind::ConstFloat(ref val) = current.kind else {
            return Err(ParserError::UnexpectedToken(
                vec![Tokind::ConstFloat("".into())],
                current.clone().kind,
            ));
        };

        self.advance();

        Ok(str::parse(val).expect("Could not parse float"))
    }

    fn basic_block_id(&mut self) -> Result<BasicBlockID, ParserError> {
        if self.did_match(Tokind::Entry)? {
            Ok(BasicBlockID(0))
        } else {
            self.consume(Tokind::Hash)?;
            let id = self.integer::<u32>()?;
            Ok(BasicBlockID(id))
        }
    }

    fn callee(&mut self) -> Result<String, ParserError> {
        self.consume(Tokind::At)?;
        let ident = self.identifier()?;
        Ok(format!("@{}", ident))
    }

    fn call_args(&mut self) -> Result<Vec<Register>, ParserError> {
        self.consume(Tokind::LeftParen)?;
        let mut args = vec![];
        if self.peek_matches(Tokind::RightParen) {
            self.advance();
            return Ok(args);
        }

        loop {
            args.push(self.register()?);
            if self.did_match(Tokind::RightParen)? {
                break;
            }
            self.consume(Tokind::Comma)?;
        }
        Ok(args)
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
            instr::Instr,
            lowerer::{BasicBlockID, IRError, IRProgram, IRType, Lowerer, RefKind, Register},
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
    fn parses_more_instructions() {
        let func = &parse(&formatdoc!(
            r#"
        func @main() int
          entry:
            %0 = bool true;
            jump_if %0 #1;
            unreachable;
          #1:
            %1 = call int @foo();
            %2 = phi int [entry: %0, #1: %1];
            ret int %2;
        "#
        ))
        .unwrap()
        .functions[0];

        let entry_bb = &func.blocks[0];
        assert_eq!(
            entry_bb.instructions[0],
            Instr::ConstantBool(Register(0), true)
        );
        assert_eq!(
            entry_bb.instructions[1],
            Instr::JumpIf(Register(0), BasicBlockID(1))
        );
        assert_eq!(entry_bb.instructions[2], Instr::Unreachable);

        let bb1 = &func.blocks[1];
        assert_eq!(
            bb1.instructions[0],
            Instr::Call {
                dest_reg: Some(Register(1)),
                callee: "@foo".to_string(),
                args: vec![],
                ty: IRType::Int,
            }
        );
        assert_eq!(
            bb1.instructions[1],
            Instr::Phi(
                Register(2),
                IRType::Int,
                vec![
                    (Register(0), BasicBlockID(0)),
                    (Register(1), BasicBlockID(1))
                ]
            )
        );
    }

    #[test]
    fn parses_various_instructions() {
        let func = &parse(&formatdoc!(
            r#"
        func @test() void
          entry:
            %0 = float 3.14;
            %1 = int 10;
            %2 = int 5;
            %3 = sub int %1, %2;
            %4 = mul int %1, %2;
            %5 = div int %1, %2;
            %6 = eq int %3 %5;
            %7 = @my_other_func;
            %8 = tag 0 [(%1)] int;
            %9 = gettag %8;
            %10 = getval int %8 0 0;
            jump #1;
          #1:
            jump_unless %6 #2;
            ret;
          #2:
            ret;
        "#
        ))
        .unwrap()
        .functions[0];

        let entry_bb = &func.blocks[0];
        assert_eq!(entry_bb.id, BasicBlockID(0));
        assert_eq!(
            entry_bb.instructions[0],
            Instr::ConstantFloat(Register(0), 3.14)
        );
        assert_eq!(
            entry_bb.instructions[1],
            Instr::ConstantInt(Register(1), 10)
        );
        assert_eq!(entry_bb.instructions[2], Instr::ConstantInt(Register(2), 5));
        assert_eq!(
            entry_bb.instructions[3],
            Instr::Sub(Register(3), IRType::Int, Register(1), Register(2))
        );
        assert_eq!(
            entry_bb.instructions[4],
            Instr::Mul(Register(4), IRType::Int, Register(1), Register(2))
        );
        assert_eq!(
            entry_bb.instructions[5],
            Instr::Div(Register(5), IRType::Int, Register(1), Register(2))
        );
        assert_eq!(
            entry_bb.instructions[6],
            Instr::Eq(Register(6), IRType::Int, Register(3), Register(5))
        );
        assert_eq!(
            entry_bb.instructions[7],
            Instr::Ref(
                Register(7),
                IRType::Func(vec![], IRType::Void.into()),
                RefKind::Func("@my_other_func".to_string())
            )
        );

        // The parser will just parse `int` as the type, it doesn't know it should be an enum type.
        // This is consistent with how other types are parsed.
        assert_eq!(
            entry_bb.instructions[8],
            Instr::TagVariant(Register(8), IRType::Int, 0, vec![Register(1)])
        );
        assert_eq!(
            entry_bb.instructions[9],
            Instr::GetEnumTag(Register(9), Register(8))
        );
        assert_eq!(
            entry_bb.instructions[10],
            Instr::GetEnumValue(Register(10), IRType::Int, Register(8), 0, 0)
        );
        assert_eq!(entry_bb.instructions[11], Instr::Jump(BasicBlockID(1)));

        let bb1 = &func.blocks[1];
        assert_eq!(bb1.id, BasicBlockID(1));
        assert_eq!(
            bb1.instructions[0],
            Instr::JumpUnless(Register(6), BasicBlockID(2))
        );
        assert_eq!(bb1.instructions[1], Instr::Ret(None));

        let bb2 = &func.blocks[2];
        assert_eq!(bb2.id, BasicBlockID(2));
        assert_eq!(bb2.instructions[0], Instr::Ret(None));
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
