use indexmap::IndexSet;
use itertools::Itertools;
use tracing::instrument;

use super::{InferencePass, TypedRet};
use crate::{
    node_kinds::func::Func,
    types::{
        solve_context::SolveContext,
        type_error::TypeError,
        type_operations::{curry, substitute},
        typed_ast::{TypedFunc, TypedParameter},
    },
};

impl InferencePass<'_> {
    #[instrument(level = tracing::Level::TRACE, skip(self, context, func), fields(func.name = ?func.name))]
    pub(super) fn visit_func(
        &mut self,
        func: &Func,
        context: &mut SolveContext,
    ) -> TypedRet<TypedFunc> {
        let func_sym = func
            .name
            .symbol()
            .map_err(|_| TypeError::NameNotResolved(func.name.clone()))?;

        tracing::debug!("visit_func: {:?}, generics: {:?}", func.name, func.generics);

        for generic in func.generics.iter() {
            self.register_generic(generic, context);
        }

        let params = self.visit_params(&func.params, context)?;

        let effects = self.tracking_effects(&func.effects, context)?;

        let mut foralls = IndexSet::default();

        let body = self.with_current_callable(func_sym, |this| {
            if let Some(ret) = &func.ret {
                let ret = this.visit_type_annotation(ret, context)?;
                this.check_block(&func.body, ret.clone(), &mut context.next())
            } else {
                this.infer_block_with_returns(&func.body, &mut context.next())
            }
        })?;

        let effects_row = self
            .tracked_effect_rows
            .pop()
            .unwrap_or_else(|| unreachable!("we just pushed it pal"));

        foralls.extend(body.ret.collect_foralls());

        let params = params
            .iter()
            .map(|t| {
                let ty = substitute(&t.ty, &self.session.skolem_map);
                foralls.extend(ty.collect_foralls());
                TypedParameter { name: t.name, ty }
            })
            .collect_vec();

        let ret = substitute(&body.ret, &self.session.skolem_map);

        self.session.insert(
            func_sym,
            curry(
                params.iter().map(|t| t.ty.clone()),
                ret.clone(),
                effects_row.clone().into(),
            ),
            &mut Default::default(),
        );

        Ok(TypedFunc {
            name: func_sym,
            params,
            effects,
            effects_row,
            foralls,
            body,
            ret,
        })
    }
}
