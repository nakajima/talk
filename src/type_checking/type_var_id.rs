use crate::{SymbolID, name::Name, token_kind::TokenKind};

#[derive(Clone)]
pub struct TypeVarID {
    pub id: u32,
    pub kind: TypeVarKind,
}

impl PartialEq for TypeVarID {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for TypeVarID {}

impl std::hash::Hash for TypeVarID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.id);
    }
}

impl TypeVarID {
    pub fn new(id: u32, kind: TypeVarKind) -> Self {
        Self { id, kind }
    }

    pub fn is_canonical(&self) -> bool {
        matches!(self.kind, TypeVarKind::CanonicalTypeParameter(_))
    }

    pub fn canonicalized(&self) -> Option<TypeVarID> {
        if let TypeVarKind::Instantiated(parent_id) = self.kind {
            return Some(TypeVarID {
                id: parent_id,
                kind: TypeVarKind::Unbound,
            });
        }

        None
    }
}

impl std::fmt::Debug for TypeVarID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypeVarKind::BinaryOperand(op) => {
                write!(f, "T{}[{}]", self.id, op.as_str())
            }
            TypeVarKind::Blank => write!(f, "T{}[blank]", self.id),
            TypeVarKind::CallArg => write!(f, "T{}[arg]", self.id),
            TypeVarKind::CallReturn => write!(f, "T{}[ret]", self.id),
            TypeVarKind::FuncParam(name) => {
                write!(f, "T{}[param({})]", self.id, name)
            }
            TypeVarKind::FuncType => write!(f, "T{}[func]", self.id),
            TypeVarKind::SelfVar(sym) => write!(f, "T{}[self{sym:?}]", self.id),
            TypeVarKind::FuncNameVar(symbol_id) => {
                write!(f, "T{}[${}]", self.id, symbol_id.0)
            }
            TypeVarKind::FuncBody => write!(f, "T{}[body]", self.id),
            TypeVarKind::Let => write!(f, "T{}[let]", self.id),
            TypeVarKind::TypeRepr(name) => {
                write!(f, "T{}[<{:?}>]", self.id, name)
            }
            TypeVarKind::Member(name) => write!(f, "T{}[.{}]", self.id, name),
            TypeVarKind::Element => write!(f, "T{}[E]", self.id),
            TypeVarKind::VariantValue => write!(f, "T{}[variant]", self.id),
            TypeVarKind::PatternBind(name) => {
                write!(f, "T{}[->{}]", self.id, name.name_str())
            }
            TypeVarKind::CanonicalTypeParameter(name) => {
                write!(f, "T{}[{}']", self.id, name)
            }
            TypeVarKind::Placeholder(name) => {
                write!(f, "T{}[Placeholder {}]", self.id, name)
            }
            TypeVarKind::Instantiated(from) => {
                write!(f, "T{}[Inst.({})]", self.id, from)
            }
            TypeVarKind::Canonicalized(to) => {
                write!(f, "T{}[Can.({})]", self.id, to)
            }
            TypeVarKind::Combined(v1, v2) => {
                write!(f, "T{}[{}&{}]", self.id, v1, v2)
            }
            TypeVarKind::Unbound => write!(f, "T{}[?]", self.id),
        }
    }
}

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
    SelfVar(SymbolID),
    Blank,
    CallArg,
    CallReturn,
    FuncParam(String),
    FuncType,
    FuncNameVar(SymbolID),
    FuncBody,
    Let,
    TypeRepr(Name),
    Member(String),
    Element,
    VariantValue,
    PatternBind(Name),
    CanonicalTypeParameter(String),
    Placeholder(String),
    Instantiated(u32),
    Canonicalized(u32),
    BinaryOperand(TokenKind),
    Combined(u32, u32),
    Unbound,
}
