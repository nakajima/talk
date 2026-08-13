//! Structural verification of a finalized MIR module (ADR 0057
//! slice 4): the invariant class the ownership balance verifier does not
//! cover — block-parameter arity against `Goto` arguments, terminator
//! presence, and id bounds (locals, functions, blocks, layouts,
//! globals). Runs at the publication point in debug builds, so a
//! lowering refactor that emits malformed MIR fails here, at the seam,
//! instead of as a wrong answer in some backend.

use talk_mir::{FuncId, Function, Inst, LayoutId, LocalId, Module, Operand, Term};

/// Every structural violation in the module, rendered for the panic
/// message. Empty means the module upholds the trust contract the
/// adapters compile against.
pub(crate) fn verify_structure(module: &Module) -> Vec<String> {
    let mut findings = Vec::new();
    if module.entry >= module.functions.len() {
        findings.push(format!(
            "entry function f{} out of bounds ({} functions)",
            module.entry,
            module.functions.len()
        ));
    }
    for (name, func) in &module.exports {
        if *func >= module.functions.len() {
            findings.push(format!("export `{name}` names out-of-bounds function f{func}"));
        }
    }
    for (id, function) in module.functions.iter().enumerate() {
        verify_function(module, id, function, &mut findings);
    }
    findings
}

fn verify_function(module: &Module, id: usize, function: &Function, findings: &mut Vec<String>) {
    let name = &function.name;
    let n_blocks = function.blocks.len();
    let n_locals = function.locals.len();
    let mut fail = |message: String| findings.push(format!("{name} (f{id}): {message}"));

    if usize::from(function.arity) > n_locals {
        fail(format!(
            "arity {} exceeds {} locals",
            function.arity, n_locals
        ));
    }

    let local_ok = |local: LocalId| usize::from(local) < n_locals;
    let operand_ok = |operand: &Operand| match operand {
        Operand::Local(local) => local_ok(*local),
        Operand::Const(_) => true,
    };
    let layout_ok = |layout: LayoutId| (layout as usize) < module.layout_table.len();
    let func_ok = |func: FuncId| func < module.functions.len();

    for (block_id, block) in function.blocks.iter().enumerate() {
        let mut fail = |message: String| {
            findings.push(format!("{name} (f{id}) block b{block_id}: {message}"))
        };
        for param in &block.params {
            if !local_ok(*param) {
                fail(format!("block parameter L{param} out of bounds"));
            }
        }

        for (index, inst) in block.insts.iter().enumerate() {
            let mut dests: Vec<LocalId> = Vec::new();
            let mut operands: Vec<Operand> = Vec::new();
            let mut layouts: Vec<LayoutId> = Vec::new();
            let mut funcs: Vec<FuncId> = Vec::new();
            let mut unwind: Option<talk_mir::BlockId> = None;
            let mut global: Option<u32> = None;
            match inst {
                Inst::Copy { dest, src } => {
                    dests.push(*dest);
                    operands.push(*src);
                }
                Inst::Scalar { dest, a, b, .. } => {
                    dests.push(*dest);
                    operands.push(*a);
                    operands.extend(*b);
                }
                Inst::Call {
                    dest,
                    func,
                    args,
                    unwind: u,
                } => {
                    dests.push(*dest);
                    funcs.push(*func);
                    operands.extend(args.iter().copied());
                    unwind = *u;
                }
                Inst::Aggregate {
                    dest, layout, args, ..
                } => {
                    dests.push(*dest);
                    layouts.push(*layout);
                    operands.extend(args.iter().copied());
                }
                Inst::GetTag { dest, src }
                | Inst::IsUnique { dest, src }
                | Inst::ExistentialPayload { dest, src } => {
                    dests.push(*dest);
                    operands.push(*src);
                }
                Inst::Blank { dest, layout } => {
                    dests.push(*dest);
                    layouts.push(*layout);
                }
                Inst::Field {
                    dest,
                    src,
                    container,
                    member,
                    ..
                } => {
                    dests.push(*dest);
                    operands.push(*src);
                    layouts.push(*container);
                    layouts.extend(*member);
                }
                Inst::FieldIndex { dest, src, .. }
                | Inst::ObjectGet { dest, src, .. }
                | Inst::ExistentialWitness { dest, src, .. } => {
                    dests.push(*dest);
                    operands.push(*src);
                }
                Inst::GetElement {
                    dest,
                    src,
                    element,
                    index,
                } => {
                    dests.push(*dest);
                    operands.push(*src);
                    operands.push(*index);
                    layouts.push(*element);
                }
                Inst::SetField {
                    rec,
                    src,
                    container,
                    member,
                    ..
                } => {
                    dests.push(*rec);
                    operands.push(*src);
                    layouts.push(*container);
                    layouts.extend(*member);
                }
                Inst::SetFieldIndex { rec, src, .. } => {
                    dests.push(*rec);
                    operands.push(*src);
                }
                Inst::StringLit {
                    dest,
                    layout,
                    storage_layout,
                    ..
                } => {
                    dests.push(*dest);
                    layouts.push(*layout);
                    layouts.push(*storage_layout);
                }
                Inst::BytesLit { dest, .. }
                | Inst::MakeCont { dest }
                | Inst::GetFloor { dest }
                | Inst::EnvGet { dest, .. } => dests.push(*dest),
                Inst::Alloc { dest, bytes } => {
                    dests.push(*dest);
                    operands.push(*bytes);
                }
                Inst::Free { src }
                | Inst::RetainPtr { src }
                | Inst::RegionAcquire { src }
                | Inst::RegionRelease { src }
                | Inst::SetFloor { src } => operands.push(*src),
                Inst::Load { dest, ptr, .. } => {
                    dests.push(*dest);
                    operands.push(*ptr);
                }
                Inst::Store { ptr, src, .. } => {
                    operands.push(*ptr);
                    operands.push(*src);
                }
                Inst::MemCopy { from, to, len } => {
                    operands.extend([*from, *to, *len]);
                }
                Inst::PtrAdd {
                    dest, ptr, offset, ..
                } => {
                    dests.push(*dest);
                    operands.push(*ptr);
                    operands.push(*offset);
                }
                Inst::Io { dest, a, b, c, .. } => {
                    dests.push(*dest);
                    operands.extend([*a, *b, *c]);
                }
                Inst::ObjectNew { dest, args } => {
                    dests.push(*dest);
                    operands.extend(args.iter().copied());
                }
                Inst::ObjectSet { obj, src, .. } => {
                    operands.push(*obj);
                    operands.push(*src);
                }
                Inst::MakeClosure { dest, func, env } => {
                    dests.push(*dest);
                    funcs.push(*func);
                    operands.extend(env.iter().copied());
                }
                Inst::SetFinalizer { obj, closure } => {
                    operands.push(*obj);
                    operands.push(*closure);
                }
                Inst::CellNew { dest, init } => {
                    dests.push(*dest);
                    operands.push(*init);
                }
                Inst::CellGet { dest, cell } => {
                    dests.push(*dest);
                    operands.push(*cell);
                }
                Inst::CellSet { cell, src } => {
                    operands.push(*cell);
                    operands.push(*src);
                }
                Inst::CallIndirect {
                    dest,
                    callee,
                    args,
                    unwind: u,
                } => {
                    dests.push(*dest);
                    operands.push(*callee);
                    operands.extend(args.iter().copied());
                    unwind = *u;
                }
                Inst::PushHandler { clause, cont, .. } => {
                    operands.push(*clause);
                    operands.push(*cont);
                }
                Inst::FindHandler {
                    clause,
                    cont,
                    index,
                    ..
                } => {
                    dests.extend([*clause, *cont, *index]);
                }
                Inst::GlobalLoad { dest, global: g } => {
                    dests.push(*dest);
                    global = Some(*g);
                }
                Inst::GlobalStore { global: g, src } => {
                    operands.push(*src);
                    global = Some(*g);
                }
                Inst::ExistentialPack {
                    dest,
                    payload,
                    witnesses,
                    ..
                } => {
                    dests.push(*dest);
                    operands.push(*payload);
                    operands.extend(witnesses.iter().copied());
                }
                Inst::AbortTo { cont, value } => {
                    operands.push(*cont);
                    operands.push(*value);
                }
            }
            for dest in dests {
                if !local_ok(dest) {
                    fail(format!("inst {index}: destination L{dest} out of bounds"));
                }
            }
            for operand in &operands {
                if !operand_ok(operand) {
                    fail(format!("inst {index}: operand {operand:?} out of bounds"));
                }
            }
            for layout in layouts {
                if !layout_ok(layout) {
                    fail(format!("inst {index}: layout {layout} out of bounds"));
                }
            }
            for func in funcs {
                if !func_ok(func) {
                    fail(format!("inst {index}: callee f{func} out of bounds"));
                }
            }
            if let Some(unwind) = unwind
                && unwind >= n_blocks
            {
                fail(format!("inst {index}: unwind target b{unwind} out of bounds"));
            }
            if let Some(global) = global
                && global >= module.global_slots
            {
                fail(format!("inst {index}: global g{global} out of bounds"));
            }
        }

        let mut edge_findings: Vec<String> = Vec::new();
        let mut check_edge = |target: usize, args: Option<&[Operand]>, what: &str| {
            let Some(target_block) = function.blocks.get(target) else {
                edge_findings.push(format!("{what} target b{target} out of bounds"));
                return;
            };
            match args {
                Some(args) => {
                    if args.len() != target_block.params.len() {
                        edge_findings.push(format!(
                            "{what} passes {} arguments to b{target}, which declares {} parameters",
                            args.len(),
                            target_block.params.len()
                        ));
                    }
                }
                // The builder keeps `Branch`/`Switch` argument-free by
                // routing merged values through dedicated arm blocks.
                None => {
                    if !target_block.params.is_empty() {
                        edge_findings.push(format!(
                            "{what} enters b{target}, which declares {} parameters no edge can pass",
                            target_block.params.len()
                        ));
                    }
                }
            }
        };
        match &block.term {
            None => fail("missing terminator".to_string()),
            Some(Term::Goto(target, args)) => {
                check_edge(*target, Some(args), "goto");
                for arg in args {
                    if !operand_ok(arg) {
                        fail(format!("goto argument {arg:?} out of bounds"));
                    }
                }
            }
            Some(Term::Branch {
                cond,
                then_block,
                else_block,
            }) => {
                if !operand_ok(cond) {
                    fail(format!("branch condition {cond:?} out of bounds"));
                }
                check_edge(*then_block, None, "branch/then");
                check_edge(*else_block, None, "branch/else");
            }
            Some(Term::Switch {
                tag,
                targets,
                default,
            }) => {
                if !operand_ok(tag) {
                    fail(format!("switch tag {tag:?} out of bounds"));
                }
                for target in targets {
                    check_edge(*target, None, "switch");
                }
                check_edge(*default, None, "switch/default");
            }
            Some(Term::Return(value)) => {
                if !operand_ok(value) {
                    fail(format!("return value {value:?} out of bounds"));
                }
            }
            Some(Term::Trap(_)) | Some(Term::UnwindRet) => {}
        }
        drop(check_edge);
        for message in edge_findings {
            fail(message);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use talk_mir::{BlockData, LocalInfo, MirSymbol, MirSymbolKind};

    fn symbol() -> MirSymbol {
        MirSymbol {
            kind: MirSymbolKind::Struct,
            module: 0,
            local: 0,
        }
    }

    fn module_with(functions: Vec<Function>) -> Module {
        Module {
            functions,
            entry: 0,
            global_slots: 0,
            exports: vec![],
            layout_table: vec![],
            display: Default::default(),
            string_symbol: symbol(),
            storage_symbol: symbol(),
            debug_files: vec![],
            debug_sources: vec![],
        }
    }

    fn function(blocks: Vec<BlockData>, locals: usize) -> Function {
        Function {
            name: "test".into(),
            arity: 0,
            locals: vec![LocalInfo::default(); locals],
            blocks,
            param_reprs: vec![],
            return_repr: None,
            frame_sites: Default::default(),
            debug_names: None,
        }
    }

    #[test]
    fn well_formed_module_has_no_findings() {
        let block = BlockData {
            params: vec![],
            insts: vec![Inst::Copy {
                dest: 0,
                src: Operand::Const(talk_mir::Constant::Int(1)),
            }],
            term: Some(Term::Return(Operand::Local(0))),
            debug: None,
        };
        let module = module_with(vec![function(vec![block], 1)]);
        assert_eq!(verify_structure(&module), Vec::<String>::new());
    }

    #[test]
    fn missing_terminator_is_reported() {
        let block = BlockData::default();
        let module = module_with(vec![function(vec![block], 0)]);
        let findings = verify_structure(&module);
        assert!(
            findings.iter().any(|f| f.contains("missing terminator")),
            "{findings:?}"
        );
    }

    #[test]
    fn goto_arity_mismatch_is_reported() {
        let target = BlockData {
            params: vec![0, 1],
            insts: vec![],
            term: Some(Term::Return(Operand::Local(0))),
            debug: None,
        };
        let source = BlockData {
            params: vec![],
            insts: vec![],
            term: Some(Term::Goto(1, vec![Operand::Local(0)])),
            debug: None,
        };
        let module = module_with(vec![function(vec![source, target], 2)]);
        let findings = verify_structure(&module);
        assert!(
            findings
                .iter()
                .any(|f| f.contains("passes 1 arguments to b1, which declares 2 parameters")),
            "{findings:?}"
        );
    }

    #[test]
    fn out_of_bounds_ids_are_reported() {
        let block = BlockData {
            params: vec![],
            insts: vec![
                Inst::Copy {
                    dest: 9,
                    src: Operand::Local(8),
                },
                Inst::Call {
                    dest: 0,
                    func: 7,
                    args: vec![],
                    unwind: Some(5),
                },
                Inst::Blank { dest: 0, layout: 3 },
            ],
            term: Some(Term::Branch {
                cond: Operand::Local(0),
                then_block: 0,
                else_block: 4,
            }),
            debug: None,
        };
        let module = module_with(vec![function(vec![block], 1)]);
        let findings = verify_structure(&module);
        for needle in [
            "destination L9",
            "operand Local(8)",
            "callee f7",
            "unwind target b5",
            "layout 3",
            "branch/else target b4",
        ] {
            assert!(
                findings.iter().any(|f| f.contains(needle)),
                "missing {needle:?} in {findings:?}"
            );
        }
    }
}
