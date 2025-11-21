use crate::id_generator::IDGenerator;

#[derive(Clone, Default)]
pub struct Vars {
    pub ty_metas: IDGenerator,
    pub type_params: IDGenerator,
    pub row_metas: IDGenerator,
    pub row_params: IDGenerator,
    pub skolems: IDGenerator,
}

impl std::fmt::Debug for Vars {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vars(α: {}, ∀α: {}, π: {}, ∀π: {})",
            self.ty_metas.last, self.type_params.last, self.row_metas.last, self.row_params.last
        )
    }
}
