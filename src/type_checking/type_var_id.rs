use crate::{SymbolID, name::Name, type_constraint::TypeConstraint};

#[derive(Clone)]
pub struct TypeVarID {
    pub id: i32,
    pub kind: TypeVarKind,
    pub constraints: Vec<TypeConstraint>,
}

impl PartialEq for TypeVarID {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for TypeVarID {}

impl std::hash::Hash for TypeVarID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_i32(self.id);
    }
}

impl TypeVarID {
    pub fn new(id: i32, kind: TypeVarKind, constraints: Vec<TypeConstraint>) -> Self {
        Self {
            id,
            kind,
            constraints,
        }
    }

    pub fn canonicalized(&self) -> Option<TypeVarID> {
        if let TypeVarKind::Instantiated(parent_id) = self.kind {
            return Some(TypeVarID {
                id: parent_id,
                kind: TypeVarKind::Unbound,
                constraints: self.constraints.clone(),
            });
        }

        None
    }
}

impl std::fmt::Debug for TypeVarID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypeVarKind::Blank => write!(f, "T{}[blank]", self.id),
            TypeVarKind::CallArg => write!(f, "T{}[arg]", self.id),
            TypeVarKind::CallReturn => write!(f, "T{}[ret]", self.id),
            TypeVarKind::FuncParam(name) => write!(f, "T{}[param({})]", self.id, name),
            TypeVarKind::FuncType => write!(f, "T{}[func]", self.id),
            TypeVarKind::FuncNameVar(symbol_id) => write!(f, "T{}[${}]", self.id, symbol_id.0),
            TypeVarKind::FuncBody => write!(f, "T{}[body]", self.id),
            TypeVarKind::Let => write!(f, "T{}[let]", self.id),
            TypeVarKind::TypeRepr(name) => write!(f, "T{}[<{:?}>]", self.id, name),
            TypeVarKind::Member(name) => write!(f, "T{}[.{}]", self.id, name),
            TypeVarKind::Element => write!(f, "T{}[E]", self.id),
            TypeVarKind::VariantValue => write!(f, "T{}[variant]", self.id),
            TypeVarKind::PatternBind(name) => write!(f, "T{}[->{}]", self.id, name.name_str()),
            TypeVarKind::CanonicalTypeParameter(name) => {
                write!(f, "T{}[C<{}>]", self.id, name)
            }
            TypeVarKind::Placeholder(name) => write!(f, "T{}[...{}]", self.id, name),
            TypeVarKind::Instantiated(from) => write!(f, "T{}[Inst.({})]", self.id, from),
            TypeVarKind::Unbound => write!(f, "T{}[?]", self.id),
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
