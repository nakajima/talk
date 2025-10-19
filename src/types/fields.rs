use crate::{
    compiling::module::ModuleId,
    label::Label,
    name_resolution::symbol::{ProtocolId, StructId, Symbol},
    node_id::NodeID,
    span::Span,
    types::type_session::ASTTyRepr,
};

#[derive(Debug, PartialEq, Clone)]
pub struct Property {
    pub symbol: Symbol,
    pub is_static: bool,
    pub ty_repr: ASTTyRepr,
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct Method {
    pub id: NodeID,
    pub span: Span,
    pub symbol: Symbol,
    pub is_static: bool,
    pub params: Vec<ASTTyRepr>,
    pub ret: ASTTyRepr,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MethodRequirement {
    pub id: NodeID,
    pub symbol: Symbol,
    pub generics: Vec<ASTTyRepr>,
    pub params: Vec<ASTTyRepr>,
    pub ret: Option<ASTTyRepr>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Initializer {
    pub symbol: Symbol,
    pub initializes_type_id: StructId,
    pub params: Vec<ASTTyRepr>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Variant {
    pub symbol: Symbol,
    pub tag: Label,
    pub fields: Vec<ASTTyRepr>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Associated {
    pub protocol_id: ProtocolId,
    pub symbol: Symbol,
}

impl Associated {
    pub fn import(self, module_id: ModuleId) -> Associated {
        Self {
            protocol_id: self.protocol_id.import(module_id),
            symbol: self.symbol.import(module_id),
        }
    }
}
