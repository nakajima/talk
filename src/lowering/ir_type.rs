use std::str::FromStr;

use crate::{
    SymbolID,
    interpreter::heap::Pointer,
    lowering::{ir_error::IRError, parsing::parser::ParserError},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IRType {
    Void,
    Int,
    Float,
    Bool,
    Func(Vec<IRType>, Box<IRType>),
    TypeVar(String),
    Enum(Vec<IRType>),
    Struct(SymbolID, Vec<IRType> /* properties */, Vec<IRType> /* type vars */),
    Array { element: Box<IRType>, /* element */ },
    Pointer,
}

impl IRType {
    pub const EMPTY_STRUCT: IRType = IRType::Struct(SymbolID(0), vec![], vec![]);

    pub fn array() -> IRType {
        IRType::Struct(
            SymbolID::ARRAY,
            vec![IRType::Int, IRType::Int, IRType::Pointer],
            vec![IRType::TypeVar("T".into())]
        )
    }

    pub fn closure() -> IRType {
        IRType::Struct(
            SymbolID::GENERATED_MAIN,
            vec![IRType::Pointer, IRType::Pointer],
            vec![]
        )
    }

    // How many bytes does this type take
    pub fn mem_size(&self) -> usize {
        match self {
            IRType::Void => 0,
            IRType::Int => 8,
            IRType::Float => 8,
            IRType::Bool => 1,
            IRType::Func(_, _) => 8, // "pointer" that's just an index into module.functions
            IRType::TypeVar(var) => todo!("Cannot determine size of type variable {}", var),
            IRType::Enum(irtypes) => irtypes.iter().map(|t| t.mem_size()).max().unwrap_or(0),
            IRType::Struct(_, irtypes, _) => irtypes.iter().map(IRType::mem_size).sum::<usize>(),
            IRType::Pointer => 8,
            IRType::Array { .. } => IRType::Pointer.mem_size(),
        }
    }

    pub fn get_element_pointer(&self, from: Pointer, index: usize) -> Result<Pointer, IRError> {
        match self {
            IRType::Struct(_, members, _) => {
                let mut offset = 0;
                (0..index).for_each(|i| {
                    offset += members[i].mem_size();
                });

                Ok(Pointer(from.0 + offset))
            }
            IRType::Array { element } => Ok(Pointer(from.0 + element.mem_size() * index)),
            _ => Err(IRError::InvalidPointer(format!(
                "Unable to index into {self:?}"
            ))),
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
            Ok(IRType::Array {
                element: IRType::from_str(&s[1..s.len() - 1])?.into(),
            })
        } else {
            // Handle simple, non-function types
            match s {
                "void" => Ok(IRType::Void),
                "int" => Ok(IRType::Int),
                "float" => Ok(IRType::Float),
                "bool" => Ok(IRType::Bool),
                "ptr" => Ok(IRType::Pointer),
                "enum" => Ok(IRType::Enum(vec![])), // Basic enum
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
            Self::Int => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::Bool => f.write_str("bool"),
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
            Self::Enum(_generics) => f.write_str("enum"),
            Self::Struct(_, types, _) => write!(
                f,
                "{{{}}}",
                types
                    .iter()
                    .map(|t| format!("{t}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            IRType::Pointer => write!(f, "ptr"),
            IRType::Array { element } => write!(f, "[{element}]"),
        }
    }
}
