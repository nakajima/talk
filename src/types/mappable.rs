use crate::types::{
    infer_row::InnerRow,
    infer_ty::{InnerTy, TypePhase},
};

pub trait Mappable<T: TypePhase, U: TypePhase> {
    type Output;
    fn mapping(
        self,
        ty_map: &mut impl FnMut(InnerTy<T>) -> InnerTy<U>,
        row_map: &mut impl FnMut(InnerRow<T>) -> InnerRow<U>,
    ) -> Self::Output;
}
