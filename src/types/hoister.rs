use crate::{
    name::Name,
    parsed_expr::{Expr, ParsedExpr},
    type_checker::TypeError,
    types::{row::Row, ty::Ty, visitor::Visitor},
};

pub struct Hoister {}

impl Hoister {
    pub fn hoist<'a>(visitor: &mut Visitor<'a>, roots: &[ParsedExpr]) -> Result<(), TypeError> {
        for root in roots {
            match &root.expr {
                Expr::Func {
                    name: Some(name), ..
                } => {
                    Self::hoist_func(visitor, name)?;
                }
                Expr::Struct { name, .. } => {
                    Self::hoist_struct(visitor, name)?;
                }
                Expr::EnumDecl { name, .. } => {
                    Self::hoist_enum(visitor, name)?;
                }
                _ => continue,
            }
        }
        Ok(())
    }

    pub fn hoist_func<'a>(visitor: &mut Visitor<'a>, name: &Name) -> Result<(), TypeError> {
        let type_var = visitor.new_type_var();
        visitor.declare(&name.symbol_id()?, Ty::Var(type_var))?;
        Ok(())
    }

    pub fn hoist_struct<'a>(visitor: &mut Visitor<'a>, name: &Name) -> Result<(), TypeError> {
        let properties = visitor.new_row_type_var();
        let methods = visitor.new_row_type_var();

        let nominal = Ty::Nominal {
            name: name.clone(),
            properties: Row::Open(properties),
            methods: Row::Open(methods),
            type_params: vec![], // Will be filled during struct definition
            instantiations: Default::default(),
        };

        let meta_properties = visitor.new_row_type_var();
        let meta_methods = visitor.new_row_type_var();

        visitor.declare(
            &name.symbol_id()?,
            Ty::Metatype {
                ty: Box::new(nominal),
                properties: Row::Open(meta_properties),
                methods: Row::Open(meta_methods),
            },
        )?;
        Ok(())
    }

    pub fn hoist_enum<'a>(visitor: &mut Visitor<'a>, name: &Name) -> Result<(), TypeError> {
        let properties = visitor.new_row_type_var();
        let methods = visitor.new_row_type_var();

        let meta_properties = visitor.new_row_type_var();
        let meta_methods = visitor.new_row_type_var();

        let nominal = Ty::Nominal {
            name: name.clone(),
            properties: Row::Open(properties),
            methods: Row::Open(methods),
            type_params: vec![], // Will be filled during struct definition
            instantiations: Default::default(),
        };

        visitor.declare(
            &name.symbol_id()?,
            Ty::Metatype {
                ty: Box::new(nominal),
                properties: Row::Open(meta_properties),
                methods: Row::Open(meta_methods),
            },
        )?;

        Ok(())
    }
}
