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
        let constraints_str = if self.constraints.is_empty() {
            "".into()
        } else {
            format!(
                ": {}",
                self.constraints
                    .iter()
                    .map(|i| format!("{:?}", i.protocol_id))
                    .collect::<Vec<String>>()
                    .join(", ")
            )
        };

        match &self.kind {
            TypeVarKind::Blank => write!(f, "T{}[blank{}]", self.id, constraints_str),
            TypeVarKind::CallArg => write!(f, "T{}[arg{}]", self.id, constraints_str),
            TypeVarKind::CallReturn => write!(f, "T{}[ret{}]", self.id, constraints_str),
            TypeVarKind::FuncParam(name) => {
                write!(f, "T{}[param({}){}]", self.id, name, constraints_str)
            }
            TypeVarKind::FuncType => write!(f, "T{}[func{}]", self.id, constraints_str),
            TypeVarKind::FuncNameVar(symbol_id) => {
                write!(f, "T{}[${}{}]", self.id, symbol_id.0, constraints_str)
            }
            TypeVarKind::FuncBody => write!(f, "T{}[body{}]", self.id, constraints_str),
            TypeVarKind::Let => write!(f, "T{}[let{}]", self.id, constraints_str),
            TypeVarKind::TypeRepr(name) => {
                write!(f, "T{}[<{:?}>{}]", self.id, name, constraints_str)
            }
            TypeVarKind::Member(name) => write!(f, "T{}[.{}{}]", self.id, name, constraints_str),
            TypeVarKind::Element => write!(f, "T{}[E{}]", self.id, constraints_str),
            TypeVarKind::VariantValue => write!(f, "T{}[variant{}]", self.id, constraints_str),
            TypeVarKind::PatternBind(name) => {
                write!(f, "T{}[->{}{}]", self.id, name.name_str(), constraints_str)
            }
            TypeVarKind::CanonicalTypeParameter(name) => {
                write!(f, "T{}[{}']", self.id, name)
            } //µ≤≥÷œ∑®†¥¨øπåß©˙∆˚¬…æ≈ç√¡™£¢∞§¶•ªº–≠
            TypeVarKind::Placeholder(name) => {
                write!(f, "T{}[...{}{}]", self.id, name, constraints_str)
            }
            TypeVarKind::Instantiated(from) => {
                write!(f, "T{}[Inst.({}){}]", self.id, from, constraints_str)
            }
            TypeVarKind::Canonicalized(to) => {
                write!(f, "T{}[Can.({}){}]", self.id, to, constraints_str)
            }
            TypeVarKind::Unbound => write!(f, "T{}[?{}]", self.id, constraints_str),
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
    Canonicalized(i32),
    Unbound,
}
