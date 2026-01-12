use crate::types::ty::SomeType;

pub trait Mappable<T: SomeType, U: SomeType> {
    type Output;
    fn mapping(
        self,
        ty_map: &mut impl FnMut(T) -> U,
        row_map: &mut impl FnMut(T::RowType) -> U::RowType,
    ) -> Self::Output;
}
