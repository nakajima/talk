use crate::{SymbolID, name::Name};

#[derive(Clone)]
pub struct TypeVarID(pub i32, pub TypeVarKind);

impl PartialEq for TypeVarID {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for TypeVarID {}

impl std::hash::Hash for TypeVarID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_i32(self.0);
    }
}

impl TypeVarID {
    pub fn canonicalized(&self) -> Option<TypeVarID> {
        if let TypeVarKind::Instantiated(parent_id) = self.1 {
            return Some(TypeVarID(parent_id, TypeVarKind::Unbound));
        }

        None
    }
}

impl std::fmt::Debug for TypeVarID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.1 {
            TypeVarKind::Blank => write!(f, "T{}[blank]", self.0),
            TypeVarKind::CallArg => write!(f, "T{}[arg]", self.0),
            TypeVarKind::CallReturn => write!(f, "T{}[ret]", self.0),
            TypeVarKind::FuncParam(name) => write!(f, "T{}[param({})]", self.0, name),
            TypeVarKind::FuncType => write!(f, "T{}[func]", self.0),
            TypeVarKind::FuncNameVar(symbol_id) => write!(f, "T{}[${}]", self.0, symbol_id.0),
            TypeVarKind::FuncBody => write!(f, "T{}[body]", self.0),
            TypeVarKind::Let => write!(f, "T{}[let]", self.0),
            TypeVarKind::TypeRepr(name) => write!(f, "T{}[<{:?}>]", self.0, name),
            TypeVarKind::Member(name) => write!(f, "T{}[.{}]", self.0, name),
            TypeVarKind::Element => write!(f, "T{}[E]", self.0),
            TypeVarKind::VariantValue => write!(f, "T{}[variant]", self.0),
            TypeVarKind::PatternBind(name) => write!(f, "T{}[->{}]", self.0, name.name_str()),
            TypeVarKind::CanonicalTypeParameter(name) => {
                write!(f, "T{}[C<{}>]", self.0, name)
            }
            TypeVarKind::Placeholder(name) => write!(f, "T{}[...{}]", self.0, name),
            TypeVarKind::Instantiated(from) => write!(f, "T{}[Inst.({})]", self.0, from),
            TypeVarKind::Unbound => write!(f, "T{}[?]", self.0),
        }
    }
}

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub enum TypeVarKind {
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
    Instantiated(i32),
    Unbound,
}
