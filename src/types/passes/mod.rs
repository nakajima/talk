use crate::types::infer_ty::InferTy;

pub mod inference_pass;
// pub mod elaboration_pass;
// pub mod inference_pass;

// Helpers
pub fn uncurry_function(ty: InferTy) -> (Vec<InferTy>, InferTy) {
    match ty {
        InferTy::Func(box param, box ret) => {
            let (mut params, final_ret) = uncurry_function(ret);
            if param != InferTy::Void {
                params.insert(0, param);
            }
            (params, final_ret)
        }
        other => (vec![], other),
    }
}
