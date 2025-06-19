use std::{
    fmt::Debug,
    iter::Peekable,
    num::ParseIntError,
    str::{Chars, FromStr},
};

use crate::{
    SymbolID,
    lowering::{
        instr::{FuncName, Instr},
        ir_module::IRModule,
        ir_type::IRType,
        lowerer::{BasicBlock, BasicBlockID, IRFunction},
        parsing::lexer::{Lexer, Token, Tokind},
        register::Register,
    },
};

#[derive(Debug)]
pub enum ParserError {
    UnexpectedToken(Vec<Tokind>, Tokind),
    UnexpectedEOF,
    Instruction(String),
}

impl From<ParseIntError> for ParserError {
    fn from(_: ParseIntError) -> Self {
        ParserError::UnexpectedEOF
    }
}

impl std::fmt::Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::fmt::Display for FuncName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for FuncName {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(FuncName(s.to_string()))
    }
}

pub fn parse_type_from_chars(chars: &mut Peekable<Chars>) -> Result<Option<IRType>, ParserError> {
    let mut arg = vec![];
    for ch in chars.by_ref() {
        log::trace!("matching: {ch}");
        match ch {
            ',' => {
                return Ok(Some(IRType::from_str(
                    &arg.into_iter().collect::<String>(),
                )?));
            }
            ')' => {
                return Ok(Some(IRType::from_str(
                    &arg.into_iter().collect::<String>(),
                )?));
            }
            _ => arg.push(ch),
        }
    }

    Ok(None)
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

    fn parse(mut self) -> Result<IRModule, ParserError> {
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

        Ok(IRModule {
            functions: self.functions,
        })
    }

    fn func(&mut self) -> Result<IRFunction, ParserError> {
        self.consume(Tokind::Func)?;
        self.consume(Tokind::At)?;
        let name = self.identifier()?;
        let params = self.parameters()?;
        let ret = self.type_repr()?;

        let mut blocks: Vec<BasicBlock> = vec![];
        self.skip_newlines();

        while self.peek_matches(Tokind::Hash) || self.peek_matches(Tokind::Entry) {
            self.skip_newlines();
            blocks.push(self.basic_block(blocks.len())?);
            self.skip_newlines();
        }

        Ok(IRFunction {
            name,
            ty: IRType::Func(params.iter().map(|p| p.1.clone()).collect(), ret.into()),
            blocks,
            env_ty: IRType::Struct(SymbolID(0), vec![]), //FIXME
            env_reg: Register(0),
        })
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

        while let Some(instruction) = self.instruction()? {
            instructions.push(instruction);

            self.skip_newlines();

            if self.peek_matches(Tokind::Hash)
                || self.peek_matches(Tokind::EOF)
                || self.peek_matches(Tokind::Func)
            {
                break;
            }
        }

        // self.advance();

        self.skip_newlines();

        Ok(BasicBlock {
            id: BasicBlockID(id as u32),
            instructions,
        })
    }

    fn instruction(&mut self) -> Result<Option<Instr>, ParserError> {
        let start_pos = self.current.clone().unwrap().start - 1;
        while !(self.peek_matches(Tokind::Semicolon) || self.peek_matches(Tokind::EOF)) {
            self.advance();
        }

        self.consume(Tokind::Semicolon).ok();

        let line_str = &self.lexer.code[start_pos..self.lexer.current].trim();
        log::trace!("attempting to parse: {line_str:?}");

        if line_str.trim().is_empty() {
            return Ok(None);
        }

        // Use the generated `FromStr` implementation to parse the line.
        line_str
            .trim()
            .parse::<Instr>()
            .map_err(|e| {
                ParserError::Instruction(format!(
                    "Failed to parse instruction: '{line_str}', error: {e}"
                ))
            })
            .map(Some)
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
        // println!("Adv: {:?}", self.current);
        self.previous.clone()
    }

    // Try to get a specific token. If it's a match, return true.
    pub(super) fn did_match(&mut self, expected: Tokind) -> Result<bool, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone()
            && current.kind == expected
        {
            self.advance();
            return Ok(true);
        };

        Ok(false)
    }

    fn type_repr(&mut self) -> Result<IRType, ParserError> {
        let ty = match self.current.clone() {
            Some(tok) => match &tok.kind {
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
                Tokind::Ptr => {
                    self.advance();
                    IRType::Pointer
                }
                Tokind::LeftParen => {
                    let params = self.parameters()?.into_iter().map(|p| p.1).collect();
                    let ret = self.type_repr()?;
                    IRType::Func(params, ret.into())
                }
                Tokind::LeftBrace => {
                    let mut types = vec![];
                    self.consume(Tokind::LeftBrace).ok();
                    while !self.did_match(Tokind::RightBrace)? {
                        types.push(self.type_repr()?);
                        self.consume(Tokind::Comma).ok();
                    }

                    IRType::Struct(SymbolID(0), types)
                }
                Tokind::Identifier(name) if name.starts_with("T") => {
                    self.advance();
                    IRType::TypeVar(name.clone())
                }
                _ => todo!("{:?}", tok.kind),
            },
            _ => {
                return Err(ParserError::UnexpectedToken(
                    vec![
                        Tokind::Int,
                        Tokind::Float,
                        Tokind::Bool,
                        Tokind::Void,
                        Tokind::LeftParen,
                        Tokind::LeftBrace,
                    ],
                    self.current
                        .as_ref()
                        .map(|t| t.kind.clone())
                        .unwrap_or(Tokind::EOF),
                ));
            }
        };

        Ok(ty)
    }

    // Try to get a specific token. If it's not a match, return an error.
    pub(super) fn consume(&mut self, expected: Tokind) -> Result<Token, ParserError> {
        self.skip_newlines();

        if let Some(current) = self.current.clone()
            && current.kind == expected
        {
            self.advance();
            return Ok(current);
        };

        Err(ParserError::UnexpectedToken(
            vec![expected],
            self.current
                .clone()
                .expect("Could not get current token")
                .kind,
        ))
    }
}

pub fn parse(code: &str) -> Result<IRModule, ParserError> {
    let lexer = Lexer::new(code);
    let parser = Parser::new(lexer);
    parser.parse()
}

#[cfg(test)]
mod tests {
    use crate::{
        compiling::driver::Driver,
        lowering::{
            instr::Instr,
            ir_error::IRError,
            ir_module::IRModule,
            ir_type::IRType,
            lowerer::{BasicBlockID, PhiPredecessors, RefKind},
            parsing::parser::parse,
            register::Register,
        },
    };
    use indoc::formatdoc;

    fn lower(input: &'static str) -> Result<IRModule, IRError> {
        let mut driver = Driver::with_str(input);
        let module = driver.lower().into_iter().next().unwrap().module();
        Ok(module)
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
            Instr::Ret(IRType::Int, Some(Register(3).into()))
        );
    }

    #[test]
    fn parses_more_instructions() {
        let func = &parse(&formatdoc!(
            r#"
        func @main() int
          entry:
            %0 = bool true;
            br %0 #1 #2;
          #1:
            %1 = call int @foo();
            %2 = phi int [entry: %0, #1: %1];
            ret int %2;
          #2:
            unreachable;
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
            Instr::Branch {
                cond: Register(0),
                true_target: BasicBlockID(1),
                false_target: BasicBlockID(2)
            }
        );

        let bb1 = &func.blocks[1];
        assert_eq!(
            bb1.instructions[0],
            Instr::Call {
                dest_reg: Register(1),
                callee: "@foo".into(),
                args: vec![].into(),
                ty: IRType::Int,
            }
        );
        assert_eq!(
            bb1.instructions[1],
            Instr::Phi(
                Register(2),
                IRType::Int,
                PhiPredecessors(vec![
                    (Register(0), BasicBlockID(0)),
                    (Register(1), BasicBlockID(1))
                ])
            )
        );
        assert_eq!(func.blocks[2].instructions, vec![Instr::Unreachable]);
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
            %6 = eq int %3, %5;
            %7 = ref () int @my_other_func;
            %8 = tagvar int 0 (%1);
            %9 = gettagof %8;
            %10 = enumvalue int %8 0 0;
            jump #1;
          #1:
            br %6 #2 #2;
            ret void;
          #2:
            ret void;
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
                IRType::Func(vec![], IRType::Int.into()),
                RefKind::Func("@my_other_func".to_string())
            )
        );

        // The parser will just parse `int` as the type, it doesn't know it should be an enum type.
        // This is consistent with how other types are parsed.
        assert_eq!(
            entry_bb.instructions[8],
            Instr::TagVariant(Register(8), IRType::Int, 0, vec![Register(1)].into())
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
            Instr::Branch {
                cond: Register(6),
                true_target: BasicBlockID(2),
                false_target: BasicBlockID(2)
            }
        );
        assert_eq!(bb1.instructions[1], Instr::Ret(IRType::Void, None));

        let bb2 = &func.blocks[2];
        assert_eq!(bb2.id, BasicBlockID(2));
        assert_eq!(bb2.instructions[0], Instr::Ret(IRType::Void, None));
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
        // println!("{}", func);
        let parsed = parse(&func).unwrap();

        assert_eq!(parsed.functions.len(), 5);
    }
}
