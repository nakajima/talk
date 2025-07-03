use std::str::FromStr;

use crate::{SymbolID, lowering::parsing::parser::ParserError};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IRType {
    Void,
    Int,
    Float,
    Bool,
    Byte,
    Func(Vec<IRType>, Box<IRType>),
    TypeVar(String),
    Enum(SymbolID, Vec<IRType>),
    Struct(
        SymbolID,
        Vec<IRType>, /* properties */
        Vec<IRType>, /* type vars */
    ),
    RawBuffer, // just bytes
    TypedBuffer {
        element: Box<IRType>, /* element */
    },
    Tuple {
        elements: Vec<IRType>,
    },
    Pointer {
        hint: Option<String>,
    },
}

impl IRType {
    pub const EMPTY_STRUCT: IRType = IRType::Struct(SymbolID(0), vec![], vec![]);

    // Make it easier to get a pointer with no type hint
    pub const POINTER: IRType = IRType::Pointer { hint: None };

    pub fn string() -> IRType {
        IRType::Struct(
            SymbolID::STRING,
            vec![IRType::Int, IRType::Int, IRType::POINTER],
            vec![],
        )
    }

    pub fn array(t: IRType) -> IRType {
        IRType::Struct(
            SymbolID::ARRAY,
            vec![IRType::Int, IRType::Int, IRType::POINTER],
            vec![t],
        )
    }

    pub fn closure() -> IRType {
        IRType::Struct(
            SymbolID::GENERATED_MAIN,
            vec![IRType::POINTER, IRType::POINTER],
            vec![],
        )
    }

    // How many bytes does this type take
    pub fn mem_size(&self) -> usize {
        match self {
            IRType::Byte => 1,
            IRType::Void => 0,
            IRType::Int => 8,
            IRType::Float => 8,
            IRType::Bool => 1,
            IRType::Func(_, _) => 8, // "pointer" that's just an index into module.functions
            #[allow(clippy::todo)]
            IRType::TypeVar(var) => {
                todo!("Cannot determine size of type variable {}", var)
            }
            IRType::Enum(_, irtypes) => irtypes.iter().map(|t| t.mem_size()).max().unwrap_or(0),
            IRType::Struct(_, irtypes, _) => irtypes.iter().map(IRType::mem_size).sum::<usize>(),
            IRType::Pointer { .. } => 8,
            IRType::Tuple { elements } => elements.iter().map(IRType::mem_size).sum::<usize>(),
            IRType::RawBuffer => IRType::POINTER.mem_size(),
            IRType::TypedBuffer { .. } => IRType::POINTER.mem_size(),
        }
    }
}

impl FromStr for IRType {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();

        // Handle function types like "(int, float) int"
        if s.starts_with('(') {
            let Some(end_of_args) = s.rfind(')') else {
                return Err(ParserError::UnexpectedEOF);
            };

            // Split into argument part and return type part
            let (args_str, ret_str) = s.split_at(end_of_args + 1);

            // Recursively parse arguments inside the parentheses
            let args_inner = &args_str[1..args_str.len() - 1];
            let mut args = vec![];
            if !args_inner.is_empty() {
                for arg_part in args_inner.split(',') {
                    args.push(IRType::from_str(arg_part.trim())?);
                }
            }

            // Recursively parse the return type
            let ret_ty = IRType::from_str(ret_str.trim())?;
            Ok(IRType::Func(args, Box::new(ret_ty)))
        } else if s.starts_with('{') {
            // Recursively parse arguments inside the parentheses
            let args_inner = &s[1..s.len() - 1];
            let mut args = vec![];
            if !args_inner.is_empty() {
                for arg_part in args_inner.split(',') {
                    args.push(IRType::from_str(arg_part.trim())?);
                }
            }

            // Recursively parse the return type
            Ok(IRType::Struct(SymbolID(0), args, vec![]))
        } else if s.starts_with('[') && s.ends_with(']') {
            Ok(IRType::TypedBuffer {
                element: IRType::from_str(&s[1..s.len() - 1])?.into(),
            })
        } else {
            // Handle simple, non-function types
            match s {
                "void" => Ok(IRType::Void),
                "int" => Ok(IRType::Int),
                "float" => Ok(IRType::Float),
                "bool" => Ok(IRType::Bool),
                "ptr" => Ok(IRType::POINTER),
                "byte" => Ok(IRType::Byte),
                "enum" => Ok(IRType::Enum(SymbolID(0), vec![])), // Basic enum
                _ if s.starts_with('T') => Ok(IRType::TypeVar(s.to_string())),
                _ => Err(ParserError::UnexpectedToken(
                    vec![],
                    crate::lowering::parsing::lexer::Tokind::Identifier(s.to_string()),
                )),
            }
        }
    }
}

impl std::fmt::Display for IRType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Void => f.write_str("void"),
            Self::Byte => f.write_str("Byte"),
            Self::Int => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::Bool => f.write_str("bool"),
            Self::RawBuffer => f.write_str("rawbuf"),
            Self::Tuple { elements } => write!(
                f,
                "({})",
                elements
                    .iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::Func(args, ret) => {
                write!(
                    f,
                    "({}) {}",
                    args.iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<String>>()
                        .join(", "),
                    ret
                )
            }
            Self::TypeVar(name) => f.write_str(name),
            Self::Enum(_, _generics) => f.write_str("enum"),
            Self::Struct(id, types, _) => write!(
                f,
                "{:?}{{{}}}",
                id,
                types
                    .iter()
                    .map(|t| format!("{t}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            IRType::Pointer { hint } => {
                if let Some(hint) = hint {
                    write!(f, "ptr({hint:?})")
                } else {
                    write!(f, "ptr")
                }
            }
            IRType::TypedBuffer { element } => write!(f, "[{element}]"),
        }
    }
}
