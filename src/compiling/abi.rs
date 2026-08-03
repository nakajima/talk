//! The frontend ABI descriptor (ADR 0043 §5): a machine-readable schema
//! of the parse-result types, emitted from the frontend's own Talk
//! declarations at bootstrap time and checked in beside the artifact.
//! Rust-side result validation is driven by this descriptor, so there
//! is no handwritten Rust mirror of the Talk schema to drift; the
//! symbol ids it records are the record/variant identities the compiled
//! artifact's runtime values carry.

use crate::compiling::typed_program::TypedProgram;
use crate::name_resolution::symbol::Symbol;
use crate::types::ty::Ty;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt::Write as _;

pub const ABI_VERSION: u32 = 1;

/// The parsed descriptor: the schema the result validator walks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiSchema {
    pub root: String,
    /// The artifact's own core Optional enum identity: the bridge
    /// validates Optional-shaped values against the identity the
    /// artifact was compiled with, never against the host's core
    /// (which may be mid-compilation through this very bridge).
    pub optional: AbiSymbol,
    pub types: BTreeMap<String, AbiType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiType {
    pub name: String,
    pub symbol: AbiSymbol,
    pub kind: AbiTypeKind,
}

/// The record/variant identity a runtime value of this type carries
/// (the structural mapping `backend::lower::runtime_symbol` applies).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbiSymbol {
    pub is_enum: bool,
    pub module: u32,
    pub local: u32,
}

impl AbiSymbol {
    pub fn runtime(&self) -> Result<talk_vm::symbol::Symbol, String> {
        use talk_vm::symbol::{ModuleId, ModuleSymbolId, Symbol};
        let module = u16::try_from(self.module)
            .map_err(|_| format!("ABI symbol module {} out of range", self.module))?;
        let id = ModuleSymbolId::new(ModuleId(module), self.local);
        Ok(if self.is_enum {
            Symbol::Enum(id)
        } else {
            Symbol::Struct(id)
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiTypeKind {
    /// Fields in declaration (= runtime record) order.
    Struct(Vec<(String, AbiTy)>),
    /// Variants in declaration (= runtime tag) order, with payload types.
    Enum(Vec<(String, Vec<AbiTy>)>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiTy {
    Named(String),
    Array(Box<AbiTy>),
    Optional(Box<AbiTy>),
    Tuple(Vec<AbiTy>),
}

/// Parse a descriptor back into the schema model. The parser accepts
/// exactly what `describe` emits; anything else fails closed.
pub fn parse_schema(text: &str) -> Result<AbiSchema, String> {
    let mut lines = text.lines().peekable();
    let version_line = lines.next().ok_or("empty ABI descriptor")?;
    let version = version_line
        .strip_prefix("abi_version: ")
        .ok_or_else(|| format!("malformed ABI descriptor header: `{version_line}`"))?;
    if version.trim() != ABI_VERSION.to_string() {
        return Err(format!(
            "ABI descriptor version {version} is not the supported {ABI_VERSION}"
        ));
    }
    let root_line = lines.next().ok_or("ABI descriptor missing its root")?;
    let root = root_line
        .strip_prefix("root: ")
        .ok_or_else(|| format!("malformed ABI descriptor root: `{root_line}`"))?
        .trim()
        .to_string();
    let optional_line = lines
        .next()
        .ok_or("ABI descriptor missing its Optional identity")?;
    let optional = parse_symbol(
        optional_line
            .strip_prefix("optional: ")
            .ok_or_else(|| format!("malformed ABI descriptor optional: `{optional_line}`"))?
            .trim(),
        true,
    )?;

    let mut types = BTreeMap::new();
    while let Some(line) = lines.next() {
        if line.trim().is_empty() {
            continue;
        }
        let (is_enum, rest) = if let Some(rest) = line.strip_prefix("struct ") {
            (false, rest)
        } else if let Some(rest) = line.strip_prefix("enum ") {
            (true, rest)
        } else {
            return Err(format!("malformed ABI descriptor line: `{line}`"));
        };
        let (name, symbol_text) = rest
            .split_once(" @ ")
            .ok_or_else(|| format!("malformed ABI descriptor head: `{line}`"))?;
        let symbol = parse_symbol(symbol_text.trim(), is_enum)?;
        let mut members = Vec::new();
        while let Some(member) = lines.peek() {
            let Some(member) = member.strip_prefix('\t') else {
                break;
            };
            let member = member.to_string();
            lines.next();
            members.push(member);
        }
        let kind = if is_enum {
            AbiTypeKind::Enum(
                members
                    .iter()
                    .map(|member| parse_variant(member))
                    .collect::<Result<_, _>>()?,
            )
        } else {
            AbiTypeKind::Struct(
                members
                    .iter()
                    .map(|member| {
                        let (field, ty) = member
                            .split_once(": ")
                            .ok_or_else(|| format!("malformed ABI field: `{member}`"))?;
                        Ok::<_, String>((field.to_string(), parse_ty(ty.trim())?))
                    })
                    .collect::<Result<_, _>>()?,
            )
        };
        let name = name.trim().to_string();
        if types
            .insert(name.clone(), AbiType { name, symbol, kind })
            .is_some()
        {
            return Err("duplicate type in ABI descriptor".into());
        }
    }
    if !types.contains_key(&root) {
        return Err(format!("ABI descriptor root `{root}` has no schema entry"));
    }
    Ok(AbiSchema {
        root,
        optional,
        types,
    })
}

fn parse_symbol(text: &str, is_enum: bool) -> Result<AbiSymbol, String> {
    let expected_prefix = if is_enum { "enum:" } else { "struct:" };
    let ids = text
        .strip_prefix(expected_prefix)
        .ok_or_else(|| format!("malformed ABI symbol: `{text}`"))?;
    let (module, local) = ids
        .split_once('.')
        .ok_or_else(|| format!("malformed ABI symbol: `{text}`"))?;
    Ok(AbiSymbol {
        is_enum,
        module: module
            .parse()
            .map_err(|_| format!("malformed ABI symbol module: `{text}`"))?,
        local: local
            .parse()
            .map_err(|_| format!("malformed ABI symbol id: `{text}`"))?,
    })
}

fn parse_variant(member: &str) -> Result<(String, Vec<AbiTy>), String> {
    match member.split_once('(') {
        None => Ok((member.trim().to_string(), vec![])),
        Some((name, payloads)) => {
            let payloads = payloads
                .strip_suffix(')')
                .ok_or_else(|| format!("malformed ABI variant: `{member}`"))?;
            Ok((
                name.trim().to_string(),
                split_top_level(payloads)?
                    .iter()
                    .map(|payload| parse_ty(payload.trim()))
                    .collect::<Result<_, _>>()?,
            ))
        }
    }
}

/// Split a comma-separated type list without cutting inside `[]`, `()`,
/// or `<>` nesting.
fn split_top_level(text: &str) -> Result<Vec<String>, String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();
    for ch in text.chars() {
        match ch {
            '[' | '(' | '<' => {
                depth += 1;
                current.push(ch);
            }
            ']' | ')' | '>' => {
                depth -= 1;
                current.push(ch);
            }
            ',' if depth == 0 => {
                parts.push(std::mem::take(&mut current));
            }
            other => current.push(other),
        }
    }
    if depth != 0 {
        return Err(format!("unbalanced ABI type list: `{text}`"));
    }
    if !current.trim().is_empty() {
        parts.push(current);
    }
    Ok(parts)
}

fn parse_ty(text: &str) -> Result<AbiTy, String> {
    let text = text.trim();
    if let Some(inner) = text.strip_suffix('?') {
        return Ok(AbiTy::Optional(Box::new(parse_ty(inner)?)));
    }
    if let Some(inner) = text.strip_prefix('[') {
        let inner = inner
            .strip_suffix(']')
            .ok_or_else(|| format!("malformed ABI array type: `{text}`"))?;
        return Ok(AbiTy::Array(Box::new(parse_ty(inner)?)));
    }
    if let Some(inner) = text.strip_prefix('(') {
        let inner = inner
            .strip_suffix(')')
            .ok_or_else(|| format!("malformed ABI tuple type: `{text}`"))?;
        return Ok(AbiTy::Tuple(
            split_top_level(inner)?
                .iter()
                .map(|item| parse_ty(item))
                .collect::<Result<_, _>>()?,
        ));
    }
    if text.contains('<') {
        return Err(format!("generic ABI types are not supported: `{text}`"));
    }
    if text.is_empty() || !text.chars().all(|ch| ch.is_alphanumeric() || ch == '_') {
        return Err(format!("malformed ABI type: `{text}`"));
    }
    Ok(AbiTy::Named(text.to_string()))
}

/// Render the descriptor for every type reachable from `root` in the
/// program's catalog. Types outside the program (core nominals like
/// `String`) render as leaf names; `[T]` and `T?` render as their sugar.
/// Anything the schema cannot carry across the ABI — functions, borrows,
/// open rows — fails closed.
pub fn describe(program: &TypedProgram, root: &str) -> Result<String, String> {
    let catalog = &program.types().catalog;
    let core = crate::compiling::core::typed_program();

    let mut names: HashMap<Symbol, String> = HashMap::new();
    for (symbol, name) in &core.resolved_names().symbol_names {
        names.insert(*symbol, name.clone());
    }
    for (symbol, name) in &program.resolved_names().symbol_names {
        names.insert(*symbol, name.clone());
    }
    names.insert(Symbol::Int, "Int".into());
    names.insert(Symbol::Float, "Float".into());
    names.insert(Symbol::Bool, "Bool".into());
    names.insert(Symbol::Byte, "Byte".into());
    names.insert(Symbol::Void, "Void".into());
    names.insert(Symbol::RawPtr, "RawPtr".into());
    names.insert(Symbol::String, "String".into());
    names.insert(Symbol::Array, "Array".into());

    let root_symbol = catalog
        .structs
        .keys()
        .chain(catalog.enums.keys())
        .find(|symbol| names.get(symbol).is_some_and(|name| name == root))
        .copied()
        .ok_or_else(|| format!("ABI schema root `{root}` is not a type in the program"))?;

    let mut queue: VecDeque<Symbol> = VecDeque::from([root_symbol]);
    let mut visited: Vec<Symbol> = vec![root_symbol];
    // name -> rendered block; BTreeMap for a deterministic, diff-stable
    // descriptor order.
    let mut blocks: BTreeMap<String, String> = BTreeMap::new();

    while let Some(symbol) = queue.pop_front() {
        let name = names
            .get(&symbol)
            .cloned()
            .ok_or_else(|| format!("unnamed type symbol in ABI schema: {symbol:?}"))?;
        let mut block = String::new();
        let mut referenced: Vec<Symbol> = Vec::new();
        if let Some(info) = catalog.structs.get(&symbol) {
            if !info.params.is_empty() {
                return Err(format!("ABI schema type `{name}` must not be generic"));
            }
            let _ = writeln!(block, "struct {name} @ {}", symbol_id(symbol)?);
            for (field, (_, ty)) in &info.fields {
                let rendered = render_ty(ty, &names, &mut referenced)?;
                let _ = writeln!(block, "\t{field}: {rendered}");
            }
        } else if let Some(info) = catalog.enums.get(&symbol) {
            if !info.params.is_empty() {
                return Err(format!("ABI schema type `{name}` must not be generic"));
            }
            let _ = writeln!(block, "enum {name} @ {}", symbol_id(symbol)?);
            for (variant, def) in &info.variants {
                let payloads = payload_types(&def.constructor_scheme.ty)
                    .ok_or_else(|| format!("variant `{name}.{variant}` has no constructor type"))?;
                if payloads.is_empty() {
                    let _ = writeln!(block, "\t{variant}");
                } else {
                    let rendered = payloads
                        .iter()
                        .map(|ty| render_ty(ty, &names, &mut referenced))
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ");
                    let _ = writeln!(block, "\t{variant}({rendered})");
                }
            }
        } else {
            unreachable!("only catalog types are enqueued");
        }
        if blocks.insert(name.clone(), block).is_some() {
            return Err(format!("two ABI schema types share the name `{name}`"));
        }
        for reference in referenced {
            // Expand only the program's own declarations: imported core
            // types sit in the catalog too, but they cross the ABI as
            // leaf names (`String`), not as schema entries.
            if (catalog.structs.contains_key(&reference) || catalog.enums.contains_key(&reference))
                && program
                    .resolved_names()
                    .symbol_names
                    .contains_key(&reference)
                && !visited.contains(&reference)
            {
                visited.push(reference);
                queue.push_back(reference);
            }
        }
    }

    let optional = core
        .types()
        .catalog
        .enums
        .keys()
        .find(|symbol| {
            core.resolved_names()
                .symbol_names
                .get(symbol)
                .is_some_and(|name| name == "Optional")
        })
        .copied()
        .ok_or("core has no Optional enum")?;
    let mut out = format!(
        "abi_version: {ABI_VERSION}\nroot: {root}\noptional: {}\n",
        symbol_id(optional)?
    );
    for block in blocks.values() {
        out.push('\n');
        out.push_str(block);
    }
    Ok(out)
}

/// A variant constructor's payload types: the parameter list of its
/// (possibly nullary) function type.
fn payload_types(ty: &Ty) -> Option<&[Ty]> {
    match ty {
        Ty::Func(params, _, _) => Some(params),
        _ => None,
    }
}

/// The stable identity the decoder matches against runtime values:
/// mirrors `backend::lower::runtime_symbol`'s structural mapping.
fn symbol_id(symbol: Symbol) -> Result<String, String> {
    match symbol {
        Symbol::Struct(id) => Ok(format!("struct:{}.{}", id.module_id.0, id.local_id)),
        Symbol::Enum(id) => Ok(format!("enum:{}.{}", id.module_id.0, id.local_id)),
        other => Err(format!("unsupported ABI schema symbol: {other:?}")),
    }
}

fn render_ty(
    ty: &Ty,
    names: &HashMap<Symbol, String>,
    referenced: &mut Vec<Symbol>,
) -> Result<String, String> {
    match ty {
        Ty::Nominal(symbol, args) => {
            let name = names
                .get(symbol)
                .cloned()
                .ok_or_else(|| format!("unnamed nominal in ABI schema: {symbol:?}"))?;
            if *symbol == Symbol::Array && args.len() == 1 {
                return Ok(format!("[{}]", render_ty(&args[0], names, referenced)?));
            }
            if name == "Optional" && args.len() == 1 {
                return Ok(format!("{}?", render_ty(&args[0], names, referenced)?));
            }
            referenced.push(*symbol);
            if args.is_empty() {
                return Ok(name);
            }
            let rendered = args
                .iter()
                .map(|arg| render_ty(arg, names, referenced))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            Ok(format!("{name}<{rendered}>"))
        }
        Ty::Tuple(items) => {
            let rendered = items
                .iter()
                .map(|item| render_ty(item, names, referenced))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            Ok(format!("({rendered})"))
        }
        other => Err(format!(
            "type unsupported in the ABI schema (only nominals and tuples cross): {other:?}"
        )),
    }
}
