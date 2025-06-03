use crate::{Typed, source_file::SourceFile};

#[derive(Debug, Clone, PartialEq)]
pub enum Instr {}

pub struct Lowerer {
    _source_file: SourceFile<Typed>,
}
