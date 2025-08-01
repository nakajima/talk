use tracing::Level;

use crate::{
    SymbolID,
    conformance::Conformance,
    environment::{Environment, free_type_vars},
    substitutions::Substitutions,
    ty::{RowKind, Ty},
    type_checker::TypeError,
    type_var_id::TypeVarKind,
};

pub struct ConformanceChecker<'a> {
    ty: &'a Ty,
    conformance: &'a Conformance,
    errors: Vec<ConformanceError>,
    env: &'a mut Environment,
}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum ConformanceError {
    TypeCannotConform(String),
    TypeDoesNotConform(String, String),
    MemberNotImplemented {
        ty: Box<Ty>,
        protocol: SymbolID,
        member: String,
    },
}

impl<'a> ConformanceChecker<'a> {
    pub fn new(ty: &'a Ty, conformance: &'a Conformance, env: &'a mut Environment) -> Self {
        Self {
            ty,
            conformance,
            errors: Default::default(),
            env,
        }
    }

    #[tracing::instrument(level = Level::TRACE, skip(self), fields(result))]
    pub fn check(mut self) -> Result<Vec<(Ty, Ty)>, TypeError> {
        let Ok(protocol) = self
            .env
            .lookup_symbol(&self.conformance.protocol_id)
            .cloned()
        else {
            return Err(TypeError::Unknown(
                "Cannot find protocol for conformance check".into(),
            ));
        };

        // Replace the protocol's associated types with the conformance's
        let mut substitutions = Substitutions::new();
        for (canonical, conforming) in protocol
            .unbound_vars()
            .into_iter()
            .zip(self.conformance.associated_types.iter())
        {
            substitutions.insert(canonical, conforming.clone());
        }

        // TODO: Update this to work with constraint-based rows
        // For now, we'll need to look up fields through constraints
        let mut unifications = vec![];
        
        // Temporary implementation - this needs to be updated to:
        // 1. Look up row constraints for the protocol's type_var
        // 2. Look up row constraints for our type's type_var  
        // 3. Compare the fields from those constraints
        
        if self.errors.is_empty() {
            Ok(unifications)
        } else {
            tracing::error!(
                "{} does not conform: {:?}",
                self.ty.to_string(),
                self.errors
            );
            Err(TypeError::ConformanceError(self.errors))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check;

    #[test]
    fn checks_basic() {
        let mut setup = check(
            "
        protocol Countable {}
        extend Int: Countable {}
        ",
        )
        .unwrap();

        let protocol = setup
            .env
            .types
            .values()
            .find(|t| t.name() == "Countable")
            .unwrap();

        let conformance = Conformance::new(protocol.symbol_id(), vec![]);
        let checker = ConformanceChecker::new(&Ty::Int, &conformance, &mut setup.env);
        let result = checker.check();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn errors_with_no_conformance() {
        let mut setup = check(
            "
        protocol Countable {}
        ",
        )
        .unwrap();

        let protocol = setup
            .env
            .types
            .values()
            .find(|t| t.name() == "Countable")
            .unwrap();

        let conformance = Conformance::new(protocol.symbol_id(), vec![]);
        let checker = ConformanceChecker::new(&Ty::Int, &conformance, &mut setup.env);
        let result = checker.check();
        assert!(result.is_err(), "{result:?}");
    }
}
