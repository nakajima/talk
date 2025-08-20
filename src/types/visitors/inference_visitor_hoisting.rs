use crate::{
    expr_id::ExprID,
    name::Name,
    parsed_expr::{Expr, ParsedExpr},
    type_checker::TypeError,
    types::{ty::Ty, type_var::TypeVarKind, visitors::inference_visitor::InferenceVisitor},
};

pub struct Hoister {}

impl Hoister {
    pub fn hoist<'a>(
        visitor: &mut InferenceVisitor<'a>,
        roots: &[ParsedExpr],
    ) -> Result<(), TypeError> {
        for root in roots {
            match &root.expr {
                Expr::Func {
                    name: Some(name), ..
                } => {
                    Self::hoist_func(visitor, root.id, name)?;
                }
                Expr::Struct { name, .. } => {
                    Self::hoist_struct(visitor, root.id, name)?;
                }
                Expr::EnumDecl { name, .. } => {
                    Self::hoist_enum(visitor, root.id, name)?;
                }
                _ => continue,
            }
        }
        Ok(())
    }

    pub fn hoist_func<'a>(
        visitor: &mut InferenceVisitor<'a>,
        id: ExprID,
        name: &Name,
    ) -> Result<(), TypeError> {
        let Some(scheme) = visitor.definitions.get(&id).cloned() else {
            return Err(TypeError::Unknown(format!(
                "Did not get definition for struct {:?}",
                name.name_str()
            )));
        };
        visitor.declare(&name.symbol_id()?, &Ty::RawScheme(scheme))?;
        Ok(())
    }

    pub fn hoist_struct<'a>(
        visitor: &mut InferenceVisitor<'a>,
        id: ExprID,
        name: &Name,
    ) -> Result<(), TypeError> {
        let Some(scheme) = visitor.definitions.get(&id).cloned() else {
            return Err(TypeError::Unknown(format!(
                "Did not get definition for struct {:?}",
                name.name_str()
            )));
        };
        visitor.declare(&name.symbol_id()?, &Ty::RawScheme(scheme))?;
        Ok(())
    }

    pub fn hoist_enum<'a>(
        visitor: &mut InferenceVisitor<'a>,
        id: ExprID,
        name: &Name,
    ) -> Result<(), TypeError> {
        let Some(scheme) = visitor.definitions.get(&id).cloned() else {
            return Err(TypeError::Unknown(format!(
                "Did not get definition for struct {:?}",
                name.name_str()
            )));
        };
        visitor.declare(&name.symbol_id()?, &Ty::RawScheme(scheme))?;

        Ok(())
    }
}
