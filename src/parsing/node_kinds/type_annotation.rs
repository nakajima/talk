use derive_visitor::{Drive, DriveMut};

use crate::{
    impl_into_node, label::Label, name::Name, name_resolution::symbol::Symbol, node_id::NodeID,
    node_kinds::record_field::RecordFieldTypeAnnotation, parsing::span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub enum TypeAnnotationKind {
    SelfType(#[drive(skip)] Name),
    Func {
        params: Vec<TypeAnnotation>,
        returns: Box<TypeAnnotation>,
    },
    NominalPath {
        base: Box<TypeAnnotation>,
        #[drive(skip)]
        member: Label,
        #[drive(skip)]
        member_span: Span,
        member_generics: Vec<TypeAnnotation>,
    },
    Nominal {
        #[drive(skip)]
        name: Name,
        #[drive(skip)]
        name_span: Span,
        generics: Vec<TypeAnnotation>,
    },
    Tuple(Vec<TypeAnnotation>),
    Record {
        fields: Vec<RecordFieldTypeAnnotation>,
    },
}

impl TypeAnnotation {
    pub fn symbol(&self) -> Symbol {
        match &self.kind {
            TypeAnnotationKind::Nominal { name, .. } => name.symbol(),
            TypeAnnotationKind::SelfType(name) => name.symbol(),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Drive, DriveMut)]
pub struct TypeAnnotation {
    #[drive(skip)]
    pub id: NodeID,
    pub kind: TypeAnnotationKind,
    #[drive(skip)]
    pub span: Span,
}

impl_into_node!(TypeAnnotation);
