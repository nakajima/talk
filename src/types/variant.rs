//! Enum variant constructor schemes. Peyton Jones, Vytiniotis, Weirich,
//! and Washburn's GADT typing work treats data constructors as ordinary
//! polymorphic functions at construction sites; this module keeps
//! payload/result projection behind the constructor-scheme API so pattern
//! typing, construction, lowering, and coverage do not inspect catalog fields
//! differently.

use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::types::catalog::Variant;
use crate::types::ty::{EffTail, Predicate, RowTail, Ty, match_pattern};

/// One use of an enum variant constructor after substituting the constructor
/// scheme at a construction, pattern, or coverage site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantInstantiation {
    pub argument_types: Vec<Ty>,
    pub result_type: Ty,
    pub givens: Vec<Predicate>,
    pub instantiations: Vec<(Symbol, Ty)>,
}

impl VariantInstantiation {
    pub fn refined_by_result(mut self, expected: &Ty) -> Option<Self> {
        let mut bindings = FxHashMap::default();
        if !match_pattern(&self.result_type, expected, &mut bindings) {
            return None;
        }
        if bindings.is_empty() {
            return Some(self);
        }
        let effs = FxHashMap::default();
        let rows = FxHashMap::default();
        self.argument_types = self
            .argument_types
            .into_iter()
            .map(|ty| ty.substitute(&bindings, &effs, &rows))
            .collect();
        self.result_type = self.result_type.substitute(&bindings, &effs, &rows);
        self.givens = self
            .givens
            .into_iter()
            .map(|predicate| predicate.substitute(&bindings, &effs, &rows))
            .collect();
        for (symbol, ty) in bindings {
            match self
                .instantiations
                .iter_mut()
                .find(|(existing, _)| *existing == symbol)
            {
                Some((_, existing_ty)) => *existing_ty = ty,
                None => self.instantiations.push((symbol, ty)),
            }
        }
        Some(self)
    }
}

impl Variant {
    fn constructor_parts(&self) -> (&[Ty], &Ty) {
        let Ty::Func(arguments, result, _) = &self.constructor_scheme.ty else {
            panic!("variant constructor scheme must be a function type");
        };
        (arguments, result)
    }

    pub fn argument_types(&self) -> &[Ty] {
        self.constructor_parts().0
    }

    pub fn result_type(&self) -> &Ty {
        self.constructor_parts().1
    }

    pub fn instantiate(
        &self,
        tys: &FxHashMap<Symbol, Ty>,
        effs: &FxHashMap<Symbol, EffTail>,
        rows: &FxHashMap<Symbol, RowTail>,
    ) -> VariantInstantiation {
        let (arguments, result) = self.constructor_parts();
        let argument_types = arguments
            .iter()
            .map(|argument| argument.substitute(tys, effs, rows))
            .collect();
        let result_type = result.substitute(tys, effs, rows);
        let givens = self
            .constructor_scheme
            .predicates
            .iter()
            .map(|predicate| predicate.substitute(tys, effs, rows))
            .collect();
        let instantiations = self
            .constructor_scheme
            .params
            .iter()
            .filter_map(|param| tys.get(&param.symbol).map(|ty| (param.symbol, ty.clone())))
            .collect();

        VariantInstantiation {
            argument_types,
            result_type,
            givens,
            instantiations,
        }
    }
}
