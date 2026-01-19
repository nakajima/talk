use rustc_hash::FxHashMap;

use crate::name_resolution::symbol::Symbol;
use crate::label::Label;
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

    /// Format a type entry as an instance method (omitting self, uncurrying)
    pub fn format_method_type_entry(&self, entry: &TypeEntry) -> String {
        match entry {
            TypeEntry::Mono(ty) => self.format_method_ty(ty),
            TypeEntry::Poly(scheme) => self.format_method_scheme(scheme),
        }
    }

    /// Format a mono type as an instance method (omitting self, uncurrying)
    pub fn format_method_ty(&self, ty: &Ty) -> String {
        // For methods, use a context that only includes type params, not row params
        // This way, internal effect row params are omitted from the display
        let ctx = TyFormatContext::from_ty_without_row_params(ty);
        self.format_method_ty_in_context(ty, &ctx)
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

    /// Format a method type, omitting the implicit self parameter and uncurrying
    pub fn format_method_scheme(&self, scheme: &Scheme<Ty>) -> String {
        let ctx = TyFormatContext::from_scheme(scheme);
        let body = self.format_method_ty_in_context(&scheme.ty, &ctx);

        let foralls = ctx.forall_names();
        if foralls.is_empty() {
            body
        } else {
            format!("<{}>{body}", foralls.join(", "))
        }
    }

    /// Format a type entry as a top-level function (uncurrying parameters)
    pub fn format_func_type_entry(&self, entry: &TypeEntry) -> String {
        match entry {
            TypeEntry::Mono(ty) => self.format_func_ty(ty),
            TypeEntry::Poly(scheme) => self.format_func_scheme(scheme),
        }
    }

    /// Format a mono type as a top-level function (uncurrying parameters)
    pub fn format_func_ty(&self, ty: &Ty) -> String {
        let ctx = TyFormatContext::from_ty_without_row_params(ty);
        self.format_func_ty_in_context(ty, &ctx)
    }

    /// Format a function scheme (uncurrying parameters, omitting row params)
    pub fn format_func_scheme(&self, scheme: &Scheme<Ty>) -> String {
        let ctx = TyFormatContext::from_scheme_without_row_params(scheme);
        let body = self.format_func_ty_in_context(&scheme.ty, &ctx);

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

    /// Format a method type, omitting the implicit self parameter and uncurrying
    fn format_method_ty_in_context(&self, ty: &Ty, ctx: &TyFormatContext) -> String {
        // For a method type like: (Self) effects -> (param1) effects -> ... -> ret
        // We want to show: (param1, ...) effects -> ret
        let Ty::Func(_self_param, box inner, _self_effects) = ty else {
            // Not a function type, fall back to normal formatting
            return self.format_ty_in_context(ty, ctx);
        };

        // Collect all params and find the final return type and effects
        let mut params = vec![];
        let mut current = inner;
        let mut final_effects = &Row::Empty;

        loop {
            match current {
                Ty::Func(box param, box ret, box effects) => {
                    params.push(self.format_ty_in_context(param, ctx));
                    final_effects = effects;
                    current = ret;
                }
                _ => break,
            }
        }

        let ret_str = self.format_ty_in_context(current, ctx);
        let effects_str = self.format_row_in_context(final_effects, ctx);
        let effects_part = if effects_str.is_empty() {
            String::new()
        } else {
            format!("{effects_str} ")
        };

        format!("({}) {effects_part}-> {ret_str}", params.join(", "))
    }

    /// Format a function type, uncurrying all parameters
    fn format_func_ty_in_context(&self, ty: &Ty, ctx: &TyFormatContext) -> String {
        // For a function type like: (param1) effects -> (param2) effects -> ... -> ret
        // We want to show: (param1, param2, ...) effects -> ret
        let Ty::Func(..) = ty else {
            // Not a function type, fall back to normal formatting
            return self.format_ty_in_context(ty, ctx);
        };

        // Collect all params and find the final return type and effects
        let mut params = vec![];
        let mut current = ty;
        let mut final_effects = &Row::Empty;

        loop {
            match current {
                Ty::Func(box param, box ret, box effects) => {
                    params.push(self.format_ty_in_context(param, ctx));
                    final_effects = effects;
                    current = ret;
                }
                _ => break,
            }
        }

        let ret_str = self.format_ty_in_context(current, ctx);
        let effects_str = self.format_row_in_context(final_effects, ctx);
        let effects_part = if effects_str.is_empty() {
            String::new()
        } else {
            format!("{effects_str} ")
        };

        format!("({}) {effects_part}-> {ret_str}", params.join(", "))
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
                let effects_str = self.format_row_in_context(effects, ctx);
                let effects_part = if effects_str.is_empty() {
                    String::new()
                } else {
                    format!("{effects_str} ")
                };
                format!(
                    "({params}) {effects_part}-> {}",
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
        // Handle bare row params (no fields) - for effects, this means "open, no specific effects"
        // Only omit if it's an unquantified row param (not in the scheme's foralls)
        if let Row::Param(param) = row {
            if let Some(name) = ctx.row_param_names.get(param) {
                // Quantified row param - show it
                return format!("..{name}");
            } else {
                // Unquantified row param - omit it
                return String::new();
            }
        }

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

        let is_open = matches!(cursor, Row::Param(..));
        let is_effect_row = fields
            .first()
            .map(|(label, _)| matches!(label, Label::_Symbol(Symbol::Effect(_))))
            .unwrap_or(false);

        if is_effect_row {
            // Format as effect row
            let effect_names: Vec<String> = fields
                .iter()
                .filter_map(|(label, _)| {
                    if let Label::_Symbol(symbol @ Symbol::Effect(_)) = label {
                        Some(
                            self.names
                                .resolve(symbol)
                                .map(|n| n.to_string())
                                .unwrap_or_else(|| format!("{label}")),
                        )
                    } else {
                        None
                    }
                })
                .collect();

            match (effect_names.len(), is_open) {
                (0, true) => String::new(), // No effects, open row: omit
                (0, false) => "'[]".to_string(), // No effects, closed row
                (1, false) => format!("'{}", effect_names[0]), // One effect, closed
                (1, true) => format!("'[{}, ..]", effect_names[0]), // One effect, open
                (_, false) => format!("'[{}]", effect_names.join(", ")), // Multiple, closed
                (_, true) => format!("'[{}, ..]", effect_names.join(", ")), // Multiple, open
            }
        } else {
            // Format as record row (original behavior)
            let mut rendered: Vec<String> = fields
                .into_iter()
                .map(|(label, ty)| format!("{label}: {}", self.format_ty_in_context(&ty, ctx)))
                .collect();

            if let Row::Param(param) = cursor {
                if let Some(name) = ctx.row_param_names.get(param) {
                    rendered.push(format!("..{name}"));
                } else {
                    rendered.push("..".to_string());
                }
            }

            rendered.join(", ")
        }
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

    /// Like from_ty but doesn't include row params (used for method display)
    fn from_ty_without_row_params(ty: &Ty) -> Self {
        let foralls = ty.collect_foralls();
        let mut type_param_order: Vec<_> = foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Ty(id) => Some(*id),
                ForAll::Row(..) => None,
            })
            .collect();
        type_param_order.sort();

        let mut ctx = Self {
            type_param_order: type_param_order.clone(),
            row_param_order: vec![],
            type_param_names: FxHashMap::default(),
            row_param_names: FxHashMap::default(),
        };

        for (idx, id) in type_param_order.into_iter().enumerate() {
            ctx.type_param_names
                .insert(id, type_param_display_name(idx));
        }

        ctx
    }

    /// Like from_scheme but doesn't include row params (used for function display)
    fn from_scheme_without_row_params(scheme: &Scheme<Ty>) -> Self {
        let mut type_params: Vec<TypeParamId> = vec![];
        for forall in &scheme.foralls {
            if let ForAll::Ty(id) = forall {
                type_params.push(*id);
            }
        }

        type_params.sort();

        let mut ctx = Self {
            type_param_order: type_params.clone(),
            row_param_order: vec![],
            type_param_names: FxHashMap::default(),
            row_param_names: FxHashMap::default(),
        };

        for (idx, id) in type_params.into_iter().enumerate() {
            ctx.type_param_names
                .insert(id, type_param_display_name(idx));
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
