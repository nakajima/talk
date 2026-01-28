use crate::types::{infer_row::Row, infer_ty::Ty};

pub mod inference_pass;
pub mod specialization_pass;

// Helpers
pub fn uncurry_function(ty: Ty) -> (Vec<Ty>, Ty, Row) {
    match ty {
        Ty::Func(box param, box ret, box effects) => {
            let (mut params, final_ret, _) = uncurry_function(ret);
            if param != Ty::Void {
                params.insert(0, param);
            }
            (params, final_ret, effects)
        }
        other => (vec![], other, Row::Empty),
    }
}
