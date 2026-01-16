use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::types::infer_row::RowParamId;
use crate::types::infer_ty::TypeParamId;
use crate::types::row::Row;
use crate::types::scheme::{ForAll, Scheme};
use crate::types::ty::Ty;
use crate::types::types::TypeEntry;

#[derive(Clone, Copy, Default)]
pub struct SymbolNames<'a> {
    primary: Option<&'a FxHashMap<Symbol, String>>,
    fallback: Option<&'a FxHashMap<Symbol, String>>,
}

impl<'a> SymbolNames<'a> {
    pub fn new(
        primary: Option<&'a FxHashMap<Symbol, String>>,
        fallback: Option<&'a FxHashMap<Symbol, String>>,
    ) -> Self {
        Self { primary, fallback }
    }

    pub fn single(primary: &'a FxHashMap<Symbol, String>) -> Self {
        Self {
            primary: Some(primary),
            fallback: None,
        }
    }

    fn resolve(&self, symbol: &Symbol) -> Option<&'a str> {
        if let Some(primary) = self.primary
            && let Some(name) = primary.get(symbol)
        {
            return Some(name.as_str());
        }

        if let Some(fallback) = self.fallback
            && let Some(name) = fallback.get(symbol)
        {
            return Some(name.as_str());
        }

        None
    }
}

#[derive(Clone, Copy)]
pub struct TypeFormatter<'a> {
    names: SymbolNames<'a>,
}

impl<'a> TypeFormatter<'a> {
    pub fn new(names: SymbolNames<'a>) -> Self {
        Self { names }
    }

    pub fn format_type_entry(&self, entry: &TypeEntry) -> String {
        match entry {
            TypeEntry::Mono(ty) => self.format_ty(ty),
            TypeEntry::Poly(scheme) => self.format_scheme(scheme),
        }
    }

    pub fn format_scheme(&self, scheme: &Scheme<Ty>) -> String {
        let ctx = TyFormatContext::from_scheme(scheme);
        let body = self.format_ty_in_context(&scheme.ty, &ctx);

        let foralls = ctx.forall_names();
        if foralls.is_empty() {
            body
        } else {
            format!("<{}>{body}", foralls.join(", "))
        }
    }

    pub fn format_ty(&self, ty: &Ty) -> String {
        let ctx = TyFormatContext::from_ty(ty);
        self.format_ty_in_context(ty, &ctx)
    }

    fn format_ty_in_context(&self, ty: &Ty, ctx: &TyFormatContext) -> String {
        match ty {
            Ty::Primitive(symbol) => match *symbol {
                Symbol::Int => "Int".to_string(),
                Symbol::Float => "Float".to_string(),
                Symbol::Bool => "Bool".to_string(),
                Symbol::Void => "Void".to_string(),
                Symbol::Never => "Never".to_string(),
                Symbol::RawPtr => "RawPtr".to_string(),
                Symbol::Byte => "Byte".to_string(),
                _ => symbol.to_string(),
            },
            Ty::Param(id, _) => ctx
                .type_param_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("{id:?}")),
            Ty::Constructor { name, params, ret } => {
                if params.is_empty() {
                    name.name_str()
                } else {
                    let params = params
                        .iter()
                        .map(|p| self.format_ty_in_context(p, ctx))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("({params}) -> {}", self.format_ty_in_context(ret, ctx))
                }
            }
            Ty::Func(param, ret, box effects) => {
                let params = param
                    .clone()
                    .uncurry_params()
                    .iter()
                    .map(|p| self.format_ty_in_context(p, ctx))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "({params}) {}-> {}",
                    if *effects != Row::Empty {
                        format!("{} ", self.format_row_in_context(effects, ctx))
                    } else {
                        "".to_string()
                    },
                    self.format_ty_in_context(ret, ctx)
                )
            }
            Ty::Tuple(items) => format!(
                "({})",
                items
                    .iter()
                    .map(|t| self.format_ty_in_context(t, ctx))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Ty::Record(.., row) => format!("{{ {} }}", self.format_row_in_context(row, ctx)),
            Ty::Nominal { symbol, type_args } => {
                let base = self.nominal_name(symbol);
                if type_args.is_empty() {
                    base
                } else {
                    let args = type_args
                        .iter()
                        .map(|t| self.format_ty_in_context(t, ctx))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{base}<{args}>")
                }
            }
        }
    }

    fn format_row_in_context(&self, row: &Row, ctx: &TyFormatContext) -> String {
        let mut fields = vec![];
        let mut cursor = row;
        loop {
            match cursor {
                Row::Empty | Row::Param(..) => break,
                Row::Extend { row, label, ty } => {
                    fields.push((label.clone(), ty.clone()));
                    cursor = row;
                }
            }
        }
        fields.reverse();

        let mut rendered = fields
            .into_iter()
            .map(|(label, ty)| format!("{label}: {}", self.format_ty_in_context(&ty, ctx)))
            .collect::<Vec<_>>();

        if let Row::Param(param) = cursor {
            let name = ctx
                .row_param_names
                .get(param)
                .cloned()
                .unwrap_or_else(|| format!("{param:?}"));
            rendered.push(format!("..{name}"));
        }

        rendered.join(", ")
    }

    fn nominal_name(&self, symbol: &Symbol) -> String {
        if let Some(name) = self.names.resolve(symbol) {
            return name.to_string();
        }

        if *symbol == Symbol::String {
            return "String".to_string();
        }

        if *symbol == Symbol::Array {
            return "Array".to_string();
        }

        symbol.to_string()
    }
}

#[derive(Default)]
struct TyFormatContext {
    type_param_order: Vec<TypeParamId>,
    row_param_order: Vec<RowParamId>,
    type_param_names: FxHashMap<TypeParamId, String>,
    row_param_names: FxHashMap<RowParamId, String>,
}

impl TyFormatContext {
    fn from_scheme(scheme: &Scheme<Ty>) -> Self {
        let mut type_params: Vec<TypeParamId> = vec![];
        let mut row_params: Vec<RowParamId> = vec![];
        for forall in &scheme.foralls {
            match forall {
                ForAll::Ty(id) => type_params.push(*id),
                ForAll::Row(id) => row_params.push(*id),
            }
        }

        type_params.sort();
        row_params.sort();

        let mut ctx = Self {
            type_param_order: type_params.clone(),
            row_param_order: row_params.clone(),
            type_param_names: FxHashMap::default(),
            row_param_names: FxHashMap::default(),
        };

        for (idx, id) in type_params.into_iter().enumerate() {
            ctx.type_param_names
                .insert(id, type_param_display_name(idx));
        }
        for (idx, id) in row_params.into_iter().enumerate() {
            ctx.row_param_names.insert(id, row_param_display_name(idx));
        }

        ctx
    }

    fn from_ty(ty: &Ty) -> Self {
        let foralls = ty.collect_foralls();
        let mut type_param_order: Vec<_> = foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Ty(id) => Some(*id),
                ForAll::Row(..) => None,
            })
            .collect();
        type_param_order.sort();
        let mut row_param_order: Vec<_> = foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Row(id) => Some(*id),
                ForAll::Ty(..) => None,
            })
            .collect();
        row_param_order.sort();

        let mut ctx = Self {
            type_param_order: type_param_order.clone(),
            row_param_order: row_param_order.clone(),
            type_param_names: FxHashMap::default(),
            row_param_names: FxHashMap::default(),
        };

        for (idx, id) in type_param_order.into_iter().enumerate() {
            ctx.type_param_names
                .insert(id, type_param_display_name(idx));
        }
        for (idx, id) in row_param_order.into_iter().enumerate() {
            ctx.row_param_names.insert(id, row_param_display_name(idx));
        }

        ctx
    }

    fn forall_names(&self) -> Vec<String> {
        let mut names: Vec<String> = vec![];
        names.extend(
            self.type_param_order
                .iter()
                .filter_map(|id| self.type_param_names.get(id).cloned()),
        );
        names.extend(
            self.row_param_order
                .iter()
                .filter_map(|id| self.row_param_names.get(id).cloned()),
        );

        names
    }
}

fn type_param_display_name(idx: usize) -> String {
    const NAMES: &[&str] = &["T", "U", "V", "W", "X", "Y", "Z"];
    if let Some(name) = NAMES.get(idx) {
        (*name).to_string()
    } else {
        format!("T{idx}")
    }
}

fn row_param_display_name(idx: usize) -> String {
    if idx == 0 {
        "R".to_string()
    } else {
        format!("R{idx}")
    }
}
