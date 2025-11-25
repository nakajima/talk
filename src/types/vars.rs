use crate::id_generator::IDGenerator;

#[derive(Clone, Default)]
pub struct Vars {
    pub type_params: IDGenerator,
    pub row_params: IDGenerator,
    pub skolems: IDGenerator,
}

impl std::fmt::Debug for Vars {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vars(, ∀α: {}, ∀π: {})",
            self.type_params.last, self.row_params.last
        )
    }
}
