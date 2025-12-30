use crate::compiling::module::ModuleId;

pub trait Importable
where
    Self: Sized,
{
    fn import(self, _module_id: ModuleId) -> Self {
        self
    }
}
