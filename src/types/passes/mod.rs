use crate::types::{infer_row::InferRow, infer_ty::InferTy};

pub mod inference_pass;

// Helpers
pub fn uncurry_function(ty: InferTy) -> (Vec<InferTy>, InferTy, InferRow) {
    match ty {
        InferTy::Func(box param, box ret, box effects) => {
            let (mut params, final_ret, _) = uncurry_function(ret);
            if param != InferTy::Void {
                params.insert(0, param);
            }
            (params, final_ret, effects)
        }
        other => (vec![], other, InferRow::Empty),
    }
}
