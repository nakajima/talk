#[derive(Debug, PartialEq, Eq)]
pub struct MetaVar(u32);

pub enum Kind {
    // Just like, a base Type
    Type,
    // Kind goes in, Kind comes out
    Arrow {
        in_kind: Box<Kind>,
        out_kind: Box<Kind>,
    },
    MetaVar(MetaVar),
}
