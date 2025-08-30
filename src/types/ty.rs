#[derive(Debug, PartialEq)]
pub enum Primitive {
    Int,
    Float,
    Bool,
}

#[derive(Debug, PartialEq)]
pub enum Ty {
    Primitive(Primitive),
}

#[allow(non_upper_case_globals)]
impl Ty {
    pub const Int: Ty = Ty::Primitive(Primitive::Int);
    pub const Float: Ty = Ty::Primitive(Primitive::Float);
    pub const Bool: Ty = Ty::Primitive(Primitive::Bool);
}
