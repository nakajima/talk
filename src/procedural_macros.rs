use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use derive_visitor::{Drive, Visitor};

use crate::ast::{AST, Parsed};
use crate::compiling::abi::AbiSchema;
use crate::compiling::driver::{Driver, DriverConfig, Source};
use crate::compiling::module::{ModuleEnvironment, ModuleId};
use crate::node::Node;
use crate::node_id::FileID;
use crate::node_kinds::decl::{DeclKind, ImportPath, ImportedSymbols, Visibility};
use crate::node_kinds::expr::{Expr, ExprKind};

const MACRO_SUFFIX: &str = ".macro.tlk";
const MAX_MACRO_INSTRUCTIONS: u64 = 10_000_000;
const MAX_MACRO_FRAMES: usize = 4_096;
const MAX_MACRO_MEMORY: usize = 64 * 1024 * 1024;

/// Serializable compile-time portion of a package module. Dependency modules
/// carry this beside their runtime interface, so macro implementations never
/// need to be rebuilt in the importing package.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct ProceduralMacroArtifact {
    image: Vec<u8>,
    schema: String,
    wrappers: BTreeMap<String, String>,
}

impl std::fmt::Debug for ProceduralMacroArtifact {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProceduralMacroArtifact")
            .field("macros", &self.wrappers.keys().collect::<Vec<_>>())
            .field("image_bytes", &self.image.len())
            .finish()
    }
}

impl ProceduralMacroArtifact {
    pub fn exported_names(&self) -> impl Iterator<Item = &str> {
        self.wrappers.keys().map(String::as_str)
    }

    fn load(&self) -> Result<ProceduralMacroService, String> {
        let module = talk_vm::Module::decode_bytecode(&self.image)
            .map_err(|error| format!("invalid procedural macro artifact: {error:?}"))?;
        Ok(ProceduralMacroService {
            executable: talk_bytecode::Executable::from_vm_module(
                module,
                crate::compiling::mir::string_shape(),
            ),
            schema: crate::compiling::abi::parse_schema(&self.schema)?,
            artifact: self.clone(),
        })
    }
}

/// One package's compile-time Talk program. Every public function declared in
/// a `*.macro.tlk` unit is an expression macro with the standard syntax API
/// signature; generated wrappers keep opaque syntax values inside Talk.
pub struct ProceduralMacroService {
    executable: talk_bytecode::Executable,
    schema: AbiSchema,
    artifact: ProceduralMacroArtifact,
}

impl std::fmt::Debug for ProceduralMacroService {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProceduralMacroService")
            .field("macros", &self.artifact.wrappers.keys().collect::<Vec<_>>())
            .finish_non_exhaustive()
    }
}

impl ProceduralMacroService {
    pub fn discover(root: &Path) -> Result<Option<Self>, String> {
        if root.as_os_str().is_empty() || !root.is_dir() {
            return Ok(None);
        }
        let mut paths = Vec::new();
        Self::collect_paths(root, &mut paths)?;
        paths.sort();
        if paths.is_empty() {
            return Ok(None);
        }
        Self::compile(paths).map(Some)
    }

    fn collect_paths(directory: &Path, paths: &mut Vec<PathBuf>) -> Result<(), String> {
        let entries = std::fs::read_dir(directory).map_err(|error| {
            format!(
                "failed to scan {} for macro units: {error}",
                directory.display()
            )
        })?;
        for entry in entries {
            let entry = entry.map_err(|error| {
                format!(
                    "failed to inspect a macro unit under {}: {error}",
                    directory.display()
                )
            })?;
            let file_type = entry.file_type().map_err(|error| {
                format!(
                    "failed to inspect a macro unit under {}: {error}",
                    directory.display()
                )
            })?;
            let path = entry.path();
            if file_type.is_dir() {
                Self::collect_paths(&path, paths)?;
            } else if file_type.is_file()
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.ends_with(MACRO_SUFFIX))
            {
                paths.push(path);
            }
        }
        Ok(())
    }

    fn compile(paths: Vec<PathBuf>) -> Result<Self, String> {
        let mut macro_sources = Vec::new();
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        for (index, path) in paths.iter().enumerate() {
            let text = std::fs::read_to_string(path)
                .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
            let (ast, diagnostics) = crate::compiling::frontend::parse_ast(
                &text,
                FileID(u32::try_from(index).map_err(|_| "too many macro files")?),
                path.to_string_lossy().as_ref(),
            )
            .map_err(|error| format!("failed to parse {}: {error}", path.display()))?;
            if !diagnostics.is_empty() {
                return Err(format!(
                    "{} contains macro parse errors:\n{}",
                    path.display(),
                    diagnostics
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("\n")
                ));
            }
            let mut forbidden = ForbiddenSyntax::default();
            let mut unit_names = Vec::new();
            for root in &ast.roots {
                root.drive(&mut forbidden);
                if let Node::Decl(decl) = root
                    && decl.visibility == Visibility::Public
                    && let DeclKind::Func(function) = &decl.kind
                {
                    let name = function.name.name_str();
                    if !seen.insert(name.clone()) {
                        return Err(format!("duplicate procedural macro `@{name}`"));
                    }
                    names.push(name.clone());
                    unit_names.push(name);
                }
            }
            if forbidden.inline_ir || forbidden.unsafe_block {
                let mut rejected = Vec::new();
                if forbidden.inline_ir {
                    rejected.push("inline IR");
                }
                if forbidden.unsafe_block {
                    rejected.push("#unsafe");
                }
                return Err(format!(
                    "{} uses {}, which is forbidden in macro units",
                    path.display(),
                    rejected.join(" and ")
                ));
            }
            macro_sources.push((path.clone(), text, unit_names));
        }
        if names.is_empty() {
            return Err("macro units declare no public macro functions".into());
        }
        names.sort();

        let mut sources = crate::compiling::stdlib::source_documents("syntax")
            .ok_or_else(|| "the syntax standard library is unavailable".to_string())?
            .into_iter()
            .map(|(path, text)| {
                let name = path.file_name().unwrap_or_default().into();
                Source::in_memory(name, text)
            })
            .collect::<Vec<_>>();

        let mut wrappers = BTreeMap::new();
        for (index, name) in names.iter().enumerate() {
            wrappers.insert(name.clone(), format!("__talk_expand_{index}"));
        }
        for (index, (_, text, mut unit_names)) in macro_sources.into_iter().enumerate() {
            unit_names.sort();
            let mut unit = String::from(
                "use package::Lexer::{ capture_macro_input }\n\
                 use package::Syntax::{ ExprMacroOutput, empty_syntax_context, lexical_scope, \
                 module_scope, syntax_context_with_scope, expansion_scope, quote_context, \
                 expr_macro_failure, materialize_expr_macro_result, splice, quote_expr_encoded }\n\n",
            );
            unit.push_str(&format!(
                "let __talk_macro_definition_source_id = {}\n\n",
                0x8000_0000u64 + index as u64
            ));
            unit.push_str(&text);
            unit.push_str("\n\n");
            for name in unit_names {
                let wrapper = &wrappers[&name];
                unit.push_str(&format!(
                    "pub func {wrapper}(source_id: Int, source: String, input_start: Int, input_end: Int, token_data: String, definition_module_id: Int, expansion_namespace: Int, expansion_ordinal: Int) -> ExprMacroOutput {{\n\
                     \t#handle 'panic {{ message in\n\
                     \t\texpr_macro_failure(code: \"macro.panic\", message: message, span: input_start..<input_end)\n\
                     \t}}\n\
                     \tlet captured = capture_macro_input(source_id: source_id, source: source, encoded: token_data)\n\
                     \tif let .some(input) = captured {{\n\
                     \t\tlet use_site = empty_syntax_context()\n\
                     \t\tlet definition_site = empty_syntax_context()\n\
                     \t\tif definition_module_id < 0 {{\n\
                     \t\t\tdefinition_site = syntax_context_with_scope(\n\
                     \t\t\t\tcontext: definition_site,\n\
                     \t\t\t\tscope: lexical_scope(file_id: source_id, node_id: 0)\n\
                     \t\t\t)\n\
                     \t\t}} else {{\n\
                     \t\t\tdefinition_site = syntax_context_with_scope(\n\
                     \t\t\t\tcontext: definition_site,\n\
                     \t\t\t\tscope: module_scope(module_id: definition_module_id)\n\
                     \t\t\t)\n\
                     \t\t}}\n\
                     \t\tlet context = quote_context(\n\
                     \t\t\tdefinition_site: definition_site,\n\
                     \t\t\texpansion_scope: expansion_scope(namespace: expansion_namespace, ordinal: expansion_ordinal)\n\
                     \t\t)\n\
                     \t\treturn materialize_expr_macro_result(result: {name}(input: input, use_site: use_site, context: context))\n\
                     \t}}\n\
                     \texpr_macro_failure(code: \"macro.invalid-input\", message: \"Macro invocation is not one balanced token tree\", span: input_start..<input_end)\n\
                     }}\n\n"
                ));
            }
            sources.push(Source::in_memory(
                format!("MacroUnit{index}.tlk").into(),
                unit,
            ));
        }

        let mut modules = ModuleEnvironment::default();
        modules.import_core(crate::compiling::core::compile());
        let mut config = DriverConfig::new("PackageMacros");
        config.modules = Rc::new(modules);
        // Macro services include the complete syntax source set and need only
        // core. Keeping this compilation bare also permits a bundled stdlib
        // module to own macros without recursively initializing the stdlib.
        let parsed = Driver::new_bare(sources, config)
            .parse()
            .map_err(|error| format!("macro service parse failed: {error:?}"))?;
        let resolved = parsed
            .resolve_names()
            .map_err(|error| format!("macro service name resolution failed: {error:?}"))?;
        let typed = resolved.type_check();
        if typed.has_errors() {
            return Err(format!(
                "macro service type check failed:\n{}",
                typed
                    .diagnostics()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }
        let schema_text = crate::compiling::abi::describe(&typed.phase.program, "ExprMacroOutput")?;
        let schema = crate::compiling::abi::parse_schema(&schema_text)?;
        let exports = names
            .iter()
            .map(|name| wrappers[name].clone())
            .collect::<Vec<_>>();
        let executable = typed.compile_service(&exports, &["alloc".into(), "diagnostic".into()])?;
        let image = executable
            .encode_bytecode()
            .map_err(|error| format!("failed to encode procedural macro artifact: {error:?}"))?;
        Ok(Self {
            executable,
            schema,
            artifact: ProceduralMacroArtifact {
                image,
                schema: schema_text,
                wrappers,
            },
        })
    }

    pub fn artifact(&self) -> &ProceduralMacroArtifact {
        &self.artifact
    }

    pub fn contains(&self, name: &str) -> bool {
        self.artifact.wrappers.contains_key(name)
    }

    pub fn exported_names(&self) -> impl Iterator<Item = &str> {
        self.artifact.exported_names()
    }

    pub fn expand(
        &self,
        name: &str,
        source_id: FileID,
        source: &str,
        input_start: u32,
        input_end: u32,
        input_tokens: &[crate::node_kinds::expr::MacroToken],
        definition_module: Option<ModuleId>,
        expansion_namespace: u64,
        expansion_ordinal: u64,
    ) -> Result<crate::compiling::bridge::BridgedExprMacro, String> {
        let wrapper = self
            .artifact
            .wrappers
            .get(name)
            .ok_or_else(|| format!("undefined procedural macro `@{name}`"))?;
        let integer = |value: u64, what: &str| {
            i64::try_from(value).map_err(|_| format!("{what} exceeds Talk's Int range"))
        };
        let args = [
            talk_vm::interp::HostValue::Int(i64::from(source_id.0)),
            talk_vm::interp::HostValue::String(source.as_bytes().to_vec()),
            talk_vm::interp::HostValue::Int(i64::from(input_start)),
            talk_vm::interp::HostValue::Int(i64::from(input_end)),
            talk_vm::interp::HostValue::String(
                crate::node_kinds::expr::MacroToken::encode_all(input_tokens).into_bytes(),
            ),
            talk_vm::interp::HostValue::Int(
                definition_module.map_or(-1, |module| i64::from(module.0)),
            ),
            talk_vm::interp::HostValue::Int(integer(
                expansion_namespace,
                "macro expansion namespace",
            )?),
            talk_vm::interp::HostValue::Int(integer(expansion_ordinal, "macro expansion ordinal")?),
        ];
        let mut io = talk_vm::io::CaptureIO::default();
        let run = self.executable.run_export(
            wrapper,
            &args,
            talk_vm::interp::Budgets {
                instructions: MAX_MACRO_INSTRUCTIONS,
                frames: MAX_MACRO_FRAMES,
                memory_bytes: MAX_MACRO_MEMORY,
            },
            &mut io,
        )?;
        crate::compiling::bridge::adapt_expr_macro(
            crate::compiling::bridge::FrontendRun::Vm(&run),
            &self.schema,
            source_id,
        )
    }
}

#[derive(Debug)]
struct ImportedProceduralMacros {
    module_id: ModuleId,
    service: Arc<ProceduralMacroService>,
}

/// Compile-time macro namespace available to one driver invocation. Local
/// macros are package-wide; dependency macros become visible only through the
/// importing source file's ordinary package `use` declarations.
#[derive(Debug, Default)]
pub struct ProceduralMacroEnvironment {
    local: Option<Arc<ProceduralMacroService>>,
    imported: HashMap<String, ImportedProceduralMacros>,
}

impl ProceduralMacroEnvironment {
    pub fn load(
        local: Option<ProceduralMacroService>,
        modules: &ModuleEnvironment,
    ) -> Result<Self, String> {
        let mut imported = HashMap::new();
        for module in modules.all_modules() {
            let Some(artifact) = &module.procedural_macros else {
                continue;
            };
            let module_id = modules
                .get_module_id_by_name(&module.name)
                .ok_or_else(|| format!("macro module {} has no session id", module.name))?;
            imported.insert(
                module.name.clone(),
                ImportedProceduralMacros {
                    module_id,
                    service: Arc::new(artifact.load()?),
                },
            );
        }
        Ok(Self {
            local: local.map(Arc::new),
            imported,
        })
    }

    pub fn local_artifact(&self) -> Option<ProceduralMacroArtifact> {
        self.local
            .as_ref()
            .map(|service| service.artifact().clone())
    }

    pub(crate) fn bindings_for(&self, ast: &AST<Parsed>) -> ProceduralMacroBindings {
        let mut bindings = ProceduralMacroBindings::default();
        if let Some(service) = &self.local {
            for name in service.exported_names() {
                bindings.insert(
                    name,
                    ProceduralMacroBinding {
                        service: service.clone(),
                        exported_name: name.to_string(),
                        definition_module: None,
                        origin: "the current package".into(),
                    },
                );
            }
        }

        for root in &ast.roots {
            let Node::Decl(decl) = root else { continue };
            let DeclKind::Import(import) = &decl.kind else {
                continue;
            };
            let ImportPath::Package(module_name) = &import.path else {
                continue;
            };
            let Some(imported) = self.imported.get(module_name) else {
                continue;
            };
            match &import.symbols {
                ImportedSymbols::All | ImportedSymbols::Glob => {
                    for name in imported.service.exported_names() {
                        bindings.insert(
                            name,
                            ProceduralMacroBinding {
                                service: imported.service.clone(),
                                exported_name: name.to_string(),
                                definition_module: Some(imported.module_id),
                                origin: module_name.clone(),
                            },
                        );
                    }
                }
                ImportedSymbols::Named(symbols) => {
                    for symbol in symbols {
                        if !imported.service.contains(&symbol.name) {
                            continue;
                        }
                        bindings.insert(
                            symbol.alias.as_deref().unwrap_or(&symbol.name),
                            ProceduralMacroBinding {
                                service: imported.service.clone(),
                                exported_name: symbol.name.clone(),
                                definition_module: Some(imported.module_id),
                                origin: module_name.clone(),
                            },
                        );
                    }
                }
            }
        }
        bindings
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ProceduralMacroBinding {
    pub(crate) service: Arc<ProceduralMacroService>,
    pub(crate) exported_name: String,
    pub(crate) definition_module: Option<ModuleId>,
    origin: String,
}

#[derive(Debug, Default)]
pub(crate) struct ProceduralMacroBindings {
    by_name: HashMap<String, Vec<ProceduralMacroBinding>>,
}

pub(crate) enum ProceduralMacroResolution<'a> {
    Missing,
    Found(&'a ProceduralMacroBinding),
    Ambiguous(Vec<String>),
}

impl ProceduralMacroBindings {
    fn insert(&mut self, visible_name: &str, binding: ProceduralMacroBinding) {
        let set = self.by_name.entry(visible_name.to_string()).or_default();
        if set.iter().any(|existing| {
            existing.definition_module == binding.definition_module
                && existing.exported_name == binding.exported_name
        }) {
            return;
        }
        set.push(binding);
    }

    pub(crate) fn resolve(&self, name: &str) -> ProceduralMacroResolution<'_> {
        let Some(bindings) = self.by_name.get(name) else {
            return ProceduralMacroResolution::Missing;
        };
        if let [binding] = bindings.as_slice() {
            return ProceduralMacroResolution::Found(binding);
        }
        let mut origins = bindings
            .iter()
            .map(|binding| binding.origin.clone())
            .collect::<Vec<_>>();
        origins.sort();
        origins.dedup();
        ProceduralMacroResolution::Ambiguous(origins)
    }
}

#[derive(Default, Visitor)]
#[visitor(Expr(enter))]
struct ForbiddenSyntax {
    inline_ir: bool,
    unsafe_block: bool,
}

impl ForbiddenSyntax {
    fn enter_expr(&mut self, expression: &Expr) {
        match &expression.kind {
            ExprKind::InlineIR(_) => self.inline_ir = true,
            ExprKind::Unsafe(_) => self.unsafe_block = true,
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_unsafe_syntax_before_compiling_macro_service() {
        let root = std::env::temp_dir().join(format!(
            "talk-unsafe-macro-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).expect("create macro fixture");
        std::fs::write(
            root.join("bad.macro.tlk"),
            "pub func bad() -> Int { #unsafe { 1 } }\n",
        )
        .expect("write macro unit");
        let error =
            ProceduralMacroService::discover(&root).expect_err("unsafe macro must be rejected");
        assert!(error.contains("#unsafe"), "{error}");
        std::fs::remove_dir_all(root).expect("remove macro fixture");
    }
}
