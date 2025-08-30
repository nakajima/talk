#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MetaVar(u32);

#[derive(Debug, PartialEq, Clone)]
pub enum Kind {
    // Just like, a base Type. AKA a Star type
    Type,
    // Kind goes in, Kind comes out
    Arrow {
        in_kind: Box<Kind>,
        out_kind: Box<Kind>,
    },
    MetaVar(MetaVar),
}
