//! MIR to textual LLVM IR lowering.
//!
//! Language functions and scalar operations are emitted as LLVM IR. A small
//! pointer ABI reaches the existing native runtime for allocation, effects,
//! host IO, regions, and result rendering. The pointer ABI is intentional: it
//! keeps platform-specific C aggregate calling conventions out of the IR.
//!
//! Every MIR instruction and terminator is matched exhaustively. Adding a MIR
//! operation therefore breaks this backend at compile time instead of silently
//! changing the accepted language.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use talk_mir::{
    CmpKind, Constant, DisplayNames, FieldRepr, Function, Inst, Layout, LayoutId, MirSymbol,
    Module, Operand, ScalarOp, Shape, SlotKind, Term, TypeKind,
};

use crate::{Artifact, Error};

const RUNTIME_ABI: &str = include_str!("llvm_runtime.c");

pub(crate) fn emit(program: &Module) -> Result<Artifact, Error> {
    let entry = program
        .functions
        .get(program.entry)
        .ok_or_else(|| internal("entry function is missing"))?;
    if entry.arity != 0 {
        return Err(Error::new(
            "an entry function with parameters is not supported by the LLVM backend",
        ));
    }

    let mut emitter = Emitter::new(
        program.string_symbol,
        program.storage_symbol,
        program.layout_table.clone(),
    );
    let mut bodies = String::new();
    for (id, function) in program.functions.iter().enumerate() {
        emitter.function(&mut bodies, id, function)?;
    }
    emitter.dispatch(&mut bodies, program);
    emitter.entry(&mut bodies, program.entry);

    let mut ir = String::from(IR_HEADER);
    ir.push_str(&bodies);
    let runtime_c = emitter.runtime_source(program.global_slots, &program.display);
    Ok(Artifact { ir, runtime_c })
}

const IR_HEADER: &str = r#"; Talk LLVM backend
source_filename = "talk-mir"

%TalkValue = type { i8, [7 x i8], i64 }

declare void @talk_llvm_frame_enter()
declare i32 @talk_llvm_enter(ptr)
declare void @talk_llvm_leave()
declare i32 @talk_llvm_unwinding()
declare i32 @talk_llvm_unwind_targets(i64, i32)
declare void @talk_llvm_unwind_take(ptr)
declare i32 @talk_llvm_cont_is(ptr, i64, i32)
declare void @talk_llvm_cont(ptr, i64, i32)
declare void @talk_llvm_push_handler(i32, ptr, ptr, i64, i32)
declare void @talk_llvm_find_handler(i32, ptr, ptr, ptr)
declare void @talk_llvm_get_floor(ptr)
declare void @talk_llvm_set_floor(ptr)
declare void @talk_llvm_abort_to(ptr, ptr)
declare void @talk_llvm_checked_scalar(ptr, i32, ptr, ptr)
declare void @talk_llvm_agg(ptr, i32, i32, i32)
declare void @talk_llvm_agg_arg(ptr, i32, i32, i32, ptr)
declare void @talk_llvm_dyn_agg(ptr, i32, i32)
declare void @talk_llvm_agg_set(ptr, i32, ptr)
declare void @talk_llvm_field(ptr, ptr, i32, i32, i32, i32)
declare void @talk_llvm_field_index(ptr, ptr, i32)
declare i64 @talk_llvm_agg_tag(ptr)
declare void @talk_llvm_set_field(ptr, ptr, i32, i32, i32)
declare void @talk_llvm_set_field_index(ptr, ptr, i32)
declare void @talk_llvm_string(ptr, i32, i32, i32, i32, i32, i32)
declare void @talk_llvm_bytes(ptr, i32)
declare void @talk_llvm_closure(ptr, i32, i32)
declare i32 @talk_llvm_closure_function(ptr)
declare ptr @talk_llvm_closure_env(ptr)
declare void @talk_llvm_cell_new(ptr, ptr)
declare void @talk_llvm_cell_get(ptr, ptr)
declare void @talk_llvm_cell_set(ptr, ptr)
declare void @talk_llvm_existential_payload(ptr, ptr)
declare void @talk_llvm_existential_witness(ptr, ptr, i32)
declare void @talk_llvm_get_element(ptr, ptr, ptr, i32, i32)
declare void @talk_llvm_alloc(ptr, ptr)
declare void @talk_llvm_free(ptr)
declare void @talk_llvm_retain(ptr)
declare void @talk_llvm_is_unique(ptr, ptr)
declare void @talk_llvm_ptr_add(ptr, ptr, ptr, i32)
declare void @talk_llvm_mem_copy(ptr, ptr, ptr)
declare void @talk_llvm_load(ptr, ptr, i32)
declare void @talk_llvm_store(ptr, ptr, i32)
declare void @talk_llvm_global_load(ptr, i32)
declare void @talk_llvm_global_store(i32, ptr)
declare void @talk_llvm_object_new(ptr, i32)
declare void @talk_llvm_object_get(ptr, ptr, i32)
declare void @talk_llvm_object_set(ptr, i32, ptr)
declare void @talk_llvm_region_acquire(ptr)
declare void @talk_llvm_region_release(ptr)
declare void @talk_llvm_set_finalizer(ptr, ptr)
declare void @talk_llvm_io(ptr, i8, ptr, ptr, ptr)
declare void @talk_llvm_trap(ptr)

"#;

struct Emitter {
    effects: HashMap<MirSymbol, u32>,
    statics: Vec<u8>,
    static_offsets: HashMap<Vec<u8>, u32>,
    display_ids: HashMap<MirSymbol, u32>,
    existential_ids: HashSet<u32>,
    next_value: u64,
    constant_slot: usize,
    call_width: usize,
    operand_width: usize,
    string_symbol: MirSymbol,
    storage_symbol: MirSymbol,
    layouts: Vec<Layout>,
}

impl Emitter {
    fn new(string_symbol: MirSymbol, storage_symbol: MirSymbol, layouts: Vec<Layout>) -> Self {
        let mut emitter = Self {
            effects: HashMap::new(),
            statics: Vec::new(),
            static_offsets: HashMap::new(),
            display_ids: HashMap::new(),
            existential_ids: HashSet::new(),
            next_value: 0,
            constant_slot: 0,
            call_width: 1,
            operand_width: 1,
            string_symbol,
            storage_symbol,
            layouts,
        };
        let symbols: Vec<_> = emitter
            .layouts
            .iter()
            .filter_map(|layout| match layout {
                Layout::Inline(symbol, _) | Layout::Boxed(symbol, _) => *symbol,
                Layout::Slot | Layout::Opaque => None,
            })
            .collect();
        for symbol in symbols {
            emitter.display_id(symbol);
        }
        emitter
    }

    fn fresh(&mut self, prefix: &str) -> String {
        let id = self.next_value;
        self.next_value += 1;
        format!("%{prefix}{id}")
    }

    fn effect(&mut self, symbol: MirSymbol) -> u32 {
        let next = u32::try_from(self.effects.len()).unwrap_or_default();
        *self.effects.entry(symbol).or_insert(next)
    }

    fn display_id(&mut self, symbol: MirSymbol) -> u32 {
        let next = u32::try_from(self.display_ids.len() + 1).unwrap_or(1);
        *self.display_ids.entry(symbol).or_insert(next)
    }

    fn layout_display(&mut self, layout: LayoutId) -> Result<u32, Error> {
        let index = usize::try_from(layout)
            .map_err(|_| internal("an instruction references an unaddressable layout"))?;
        let symbol = match self.layouts.get(index) {
            Some(Layout::Inline(symbol, _) | Layout::Boxed(symbol, _)) => *symbol,
            Some(Layout::Slot | Layout::Opaque) => None,
            None => return Err(internal("an instruction references a missing layout")),
        };
        Ok(symbol.map(|symbol| self.display_id(symbol)).unwrap_or(0))
    }

    fn published_display(&self, layout: LayoutId) -> u32 {
        usize::try_from(layout)
            .ok()
            .and_then(|index| self.layouts.get(index))
            .and_then(|layout| match layout {
                Layout::Inline(symbol, _) | Layout::Boxed(symbol, _) => *symbol,
                Layout::Slot | Layout::Opaque => None,
            })
            .and_then(|symbol| self.display_ids.get(&symbol).copied())
            .unwrap_or(0)
    }

    fn layout_width(&self, layout: LayoutId) -> u32 {
        usize::try_from(layout)
            .ok()
            .and_then(|index| self.layouts.get(index))
            .map(|layout| match layout {
                Layout::Inline(_, Shape::Product { width, .. })
                | Layout::Inline(_, Shape::Sum { width, .. })
                | Layout::Boxed(_, Shape::Product { width, .. })
                | Layout::Boxed(_, Shape::Sum { width, .. }) => *width,
                Layout::Slot | Layout::Opaque => 1,
            })
            .unwrap_or(1)
    }

    fn intern_static(&mut self, bytes: &[u8]) -> u32 {
        if let Some(offset) = self.static_offsets.get(bytes) {
            return *offset;
        }
        let offset = u32::try_from(self.statics.len()).unwrap_or_default();
        self.statics.extend_from_slice(bytes);
        self.static_offsets.insert(bytes.to_vec(), offset);
        offset
    }

    fn function(&mut self, out: &mut String, id: usize, function: &Function) -> Result<(), Error> {
        self.next_value = 0;
        self.constant_slot = 0;
        self.call_width = function
            .blocks
            .iter()
            .flat_map(|block| &block.insts)
            .filter_map(|inst| match inst {
                Inst::Call { args, .. } | Inst::CallIndirect { args, .. } => Some(args.len()),
                _ => None,
            })
            .max()
            .unwrap_or(0)
            .max(1);
        self.operand_width = function
            .blocks
            .iter()
            .flat_map(|block| &block.insts)
            .filter_map(|inst| match inst {
                Inst::Aggregate { args, .. } | Inst::ObjectNew { args, .. } => Some(args.len()),
                Inst::MakeClosure { env, .. } => Some(env.len()),
                Inst::ExistentialPack { witnesses, .. } => Some(witnesses.len() + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0)
            .max(1);
        let identified = needs_identity(function);
        let _ = writeln!(out, "\n; {}", llvm_comment(&function.name));
        let _ = writeln!(
            out,
            "define void @talk_fn{id}(ptr %out, ptr %env, ptr %args) {{"
        );
        let _ = writeln!(out, "entry:");
        let count = function.n_locals().max(1);
        let _ = writeln!(out, "  %locals = alloca [{count} x %TalkValue], align 8");
        let _ = writeln!(out, "  %constants = alloca [8 x %TalkValue], align 8");
        let call_width = self.call_width;
        let _ = writeln!(
            out,
            "  %callargs = alloca [{call_width} x %TalkValue], align 8"
        );
        let operand_width = self.operand_width;
        let _ = writeln!(
            out,
            "  %operands = alloca [{operand_width} x %TalkValue], align 8"
        );
        for local in 0..count {
            let _ = writeln!(
                out,
                "  %l{local} = getelementptr inbounds [{count} x %TalkValue], ptr %locals, i32 0, i32 {local}"
            );
            let _ = writeln!(
                out,
                "  store %TalkValue zeroinitializer, ptr %l{local}, align 8"
            );
        }
        let _ = writeln!(out, "  call void @talk_llvm_frame_enter()");
        if identified {
            let _ = writeln!(out, "  %frame_depth_slot = alloca i64, align 8");
            let _ = writeln!(
                out,
                "  %frame_id = call i32 @talk_llvm_enter(ptr %frame_depth_slot)"
            );
            let _ = writeln!(
                out,
                "  %frame_depth = load i64, ptr %frame_depth_slot, align 8"
            );
        }
        for parameter in 0..function.arity {
            let pointer = self.fresh("arg");
            let value = self.fresh("argv");
            let _ = writeln!(
                out,
                "  {pointer} = getelementptr inbounds %TalkValue, ptr %args, i32 {parameter}"
            );
            let _ = writeln!(out, "  {value} = load %TalkValue, ptr {pointer}, align 8");
            let _ = writeln!(
                out,
                "  store %TalkValue {value}, ptr %l{parameter}, align 8"
            );
        }
        let _ = writeln!(out, "  br label %b0");

        for (block_id, block) in function.blocks.iter().enumerate() {
            let _ = writeln!(out, "b{block_id}:");
            for inst in &block.insts {
                self.inst(out, inst, identified)?;
            }
            let term = block
                .term
                .as_ref()
                .ok_or_else(|| internal("basic block has no terminator"))?;
            self.term(out, term, function, identified)?;
        }
        let _ = writeln!(out, "}}");
        Ok(())
    }

    fn operand(&mut self, out: &mut String, operand: Operand) -> String {
        match operand {
            Operand::Local(local) => format!("%l{local}"),
            Operand::Const(constant) => {
                let pointer = self.fresh("const");
                let slot = self.constant_slot % 8;
                self.constant_slot += 1;
                let _ = writeln!(
                    out,
                    "  {pointer} = getelementptr inbounds [8 x %TalkValue], ptr %constants, i32 0, i32 {slot}"
                );
                let (tag, payload) = match constant {
                    Constant::Unit => (0, 0),
                    Constant::Bool(value) => (1, i64::from(value)),
                    Constant::Int(value) => (2, value),
                    Constant::Float(value) => {
                        (8, i64::from_ne_bytes(value.to_bits().to_ne_bytes()))
                    }
                };
                let _ = writeln!(
                    out,
                    "  store %TalkValue {{ i8 {tag}, [7 x i8] zeroinitializer, i64 {payload} }}, ptr {pointer}, align 8"
                );
                pointer
            }
        }
    }

    fn copy_value(&mut self, out: &mut String, dest: &str, src: &str) {
        let value = self.fresh("copy");
        let _ = writeln!(out, "  {value} = load %TalkValue, ptr {src}, align 8");
        let _ = writeln!(out, "  store %TalkValue {value}, ptr {dest}, align 8");
    }

    fn args(&mut self, out: &mut String, args: &[Operand]) -> String {
        let width = self.call_width;
        for (index, arg) in args.iter().enumerate() {
            let source = self.operand(out, *arg);
            let target = self.fresh("callarg");
            let _ = writeln!(
                out,
                "  {target} = getelementptr inbounds [{width} x %TalkValue], ptr %callargs, i32 0, i32 {index}"
            );
            self.copy_value(out, &target, &source);
        }
        "%callargs".into()
    }

    fn snapshot_operands(&mut self, out: &mut String, operands: &[Operand]) -> Vec<String> {
        let width = self.operand_width;
        operands
            .iter()
            .enumerate()
            .map(|(index, operand)| {
                let source = self.operand(out, *operand);
                let target = self.fresh("operand");
                let _ = writeln!(
                    out,
                    "  {target} = getelementptr inbounds [{width} x %TalkValue], ptr %operands, i32 0, i32 {index}"
                );
                self.copy_value(out, &target, &source);
                target
            })
            .collect()
    }

    fn inst(&mut self, out: &mut String, inst: &Inst, identified: bool) -> Result<(), Error> {
        match inst {
            Inst::Copy { dest, src } => {
                let src = self.operand(out, *src);
                self.copy_value(out, &format!("%l{dest}"), &src);
            }
            Inst::Scalar { dest, op, a, b } => self.scalar(out, *dest, *op, *a, *b)?,
            Inst::Call {
                dest,
                func,
                args,
                unwind,
            } => {
                let args = self.args(out, args);
                let _ = writeln!(
                    out,
                    "  call void @talk_fn{func}(ptr %l{dest}, ptr null, ptr {args})"
                );
                self.unwind_check(out, *unwind, identified);
            }
            Inst::CallIndirect {
                dest,
                callee,
                args,
                unwind,
            } => {
                let callee = self.operand(out, *callee);
                let args = self.args(out, args);
                let function = self.fresh("closure_fn");
                let env = self.fresh("closure_env");
                let _ = writeln!(
                    out,
                    "  {function} = call i32 @talk_llvm_closure_function(ptr {callee})"
                );
                let _ = writeln!(
                    out,
                    "  {env} = call ptr @talk_llvm_closure_env(ptr {callee})"
                );
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_dispatch(ptr %l{dest}, i32 {function}, ptr {env}, ptr {args})"
                );
                self.unwind_check(out, *unwind, identified);
            }
            Inst::Aggregate {
                dest,
                tag,
                layout,
                args,
            } => self.aggregate(out, *dest, *layout, *tag, args)?,
            Inst::GetTag { dest, src } => {
                let src = self.operand(out, *src);
                let tag = self.fresh("tag");
                let _ = writeln!(out, "  {tag} = call i64 @talk_llvm_agg_tag(ptr {src})");
                let value = self.tagged_value(out, 2, &format!("i64 {tag}"));
                let _ = writeln!(out, "  store %TalkValue {value}, ptr %l{dest}, align 8");
            }
            Inst::Blank { dest, layout } => self.aggregate(out, *dest, *layout, 0, &[])?,
            Inst::Field {
                dest,
                src,
                container,
                offset,
                member,
            } => {
                let src = self.operand(out, *src);
                let symbol = match member {
                    Some(member) => self.layout_display(*member)?,
                    None => 0,
                };
                let member = member.unwrap_or(u32::MAX);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_field(ptr %l{dest}, ptr {src}, i32 {container}, i32 {offset}, i32 {member}, i32 {symbol})"
                );
            }
            Inst::FieldIndex { dest, src, index } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_field_index(ptr %l{dest}, ptr {src}, i32 {index})"
                );
            }
            Inst::SetField {
                rec,
                src,
                container,
                offset,
                member,
            } => {
                let src = self.operand(out, *src);
                let member = member.unwrap_or(u32::MAX);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_set_field(ptr %l{rec}, ptr {src}, i32 {container}, i32 {offset}, i32 {member})"
                );
            }
            Inst::SetFieldIndex { rec, src, index } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_set_field_index(ptr %l{rec}, ptr {src}, i32 {index})"
                );
            }
            Inst::StringLit {
                dest,
                bytes,
                layout,
                storage_layout,
            } => {
                let offset = self.intern_static(bytes);
                let string = self.display_id(self.string_symbol);
                let storage = self.display_id(self.storage_symbol);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_string(ptr %l{dest}, i32 {offset}, i32 {}, i32 {layout}, i32 {storage_layout}, i32 {string}, i32 {storage})",
                    bytes.len()
                );
            }
            Inst::BytesLit { dest, bytes } => {
                let offset = self.intern_static(bytes);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_bytes(ptr %l{dest}, i32 {offset})"
                );
            }
            Inst::Alloc { dest, bytes } => {
                let bytes = self.operand(out, *bytes);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_alloc(ptr %l{dest}, ptr {bytes})"
                );
            }
            Inst::Free { src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(out, "  call void @talk_llvm_free(ptr {src})");
            }
            Inst::RetainPtr { src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(out, "  call void @talk_llvm_retain(ptr {src})");
            }
            Inst::IsUnique { dest, src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_is_unique(ptr %l{dest}, ptr {src})"
                );
            }
            Inst::Load { dest, ptr, kind } => {
                let ptr = self.operand(out, *ptr);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_load(ptr %l{dest}, ptr {ptr}, i32 {})",
                    mem_kind(*kind)
                );
            }
            Inst::Store { ptr, src, kind } => {
                let ptr = self.operand(out, *ptr);
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_store(ptr {ptr}, ptr {src}, i32 {})",
                    mem_kind(*kind)
                );
            }
            Inst::MemCopy { from, to, len } => {
                let from = self.operand(out, *from);
                let to = self.operand(out, *to);
                let len = self.operand(out, *len);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_mem_copy(ptr {from}, ptr {to}, ptr {len})"
                );
            }
            Inst::PtrAdd {
                dest,
                ptr,
                offset,
                size,
            } => {
                let ptr = self.operand(out, *ptr);
                let offset = self.operand(out, *offset);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_ptr_add(ptr %l{dest}, ptr {ptr}, ptr {offset}, i32 {size})"
                );
            }
            Inst::Io { dest, op, a, b, c } => {
                let a = self.operand(out, *a);
                let b = self.operand(out, *b);
                let c = self.operand(out, *c);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_io(ptr %l{dest}, i8 {op}, ptr {a}, ptr {b}, ptr {c})"
                );
            }
            Inst::ObjectNew { dest, args } => {
                let args = self.snapshot_operands(out, args);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_object_new(ptr %l{dest}, i32 {})",
                    args.len()
                );
                for (index, arg) in args.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "  call void @talk_llvm_object_set(ptr %l{dest}, i32 {index}, ptr {arg})"
                    );
                }
            }
            Inst::ObjectGet { dest, src, index } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_object_get(ptr %l{dest}, ptr {src}, i32 {index})"
                );
            }
            Inst::ObjectSet { obj, src, index } => {
                let obj = self.operand(out, *obj);
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_object_set(ptr {obj}, i32 {index}, ptr {src})"
                );
            }
            Inst::RegionAcquire { src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(out, "  call void @talk_llvm_region_acquire(ptr {src})");
            }
            Inst::RegionRelease { src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(out, "  call void @talk_llvm_region_release(ptr {src})");
            }
            Inst::MakeClosure { dest, func, env } => {
                let env = self.snapshot_operands(out, env);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_closure(ptr %l{dest}, i32 {func}, i32 {})",
                    env.len()
                );
                for (index, captured) in env.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "  call void @talk_llvm_agg_set(ptr %l{dest}, i32 {index}, ptr {captured})"
                    );
                }
            }
            Inst::SetFinalizer { obj, closure } => {
                let obj = self.operand(out, *obj);
                let closure = self.operand(out, *closure);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_set_finalizer(ptr {obj}, ptr {closure})"
                );
            }
            Inst::CellNew { dest, init } => {
                let init = self.operand(out, *init);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_cell_new(ptr %l{dest}, ptr {init})"
                );
            }
            Inst::CellGet { dest, cell } => {
                let cell = self.operand(out, *cell);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_cell_get(ptr %l{dest}, ptr {cell})"
                );
            }
            Inst::CellSet { cell, src } => {
                let cell = self.operand(out, *cell);
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_cell_set(ptr {cell}, ptr {src})"
                );
            }
            Inst::EnvGet { dest, index } => {
                let pointer = self.fresh("env");
                let _ = writeln!(
                    out,
                    "  {pointer} = getelementptr inbounds %TalkValue, ptr %env, i32 {index}"
                );
                self.copy_value(out, &format!("%l{dest}"), &pointer);
            }
            Inst::MakeCont { dest } => {
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_cont(ptr %l{dest}, i64 %frame_depth, i32 %frame_id)"
                );
            }
            Inst::PushHandler {
                effect,
                clause,
                cont,
            } => {
                let effect = self.effect(*effect);
                let clause = self.operand(out, *clause);
                let cont = self.operand(out, *cont);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_push_handler(i32 {effect}, ptr {clause}, ptr {cont}, i64 %frame_depth, i32 %frame_id)"
                );
            }
            Inst::FindHandler {
                clause,
                cont,
                index,
                effect,
            } => {
                let effect = self.effect(*effect);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_find_handler(i32 {effect}, ptr %l{clause}, ptr %l{cont}, ptr %l{index})"
                );
            }
            Inst::GetFloor { dest } => {
                let _ = writeln!(out, "  call void @talk_llvm_get_floor(ptr %l{dest})");
            }
            Inst::SetFloor { src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(out, "  call void @talk_llvm_set_floor(ptr {src})");
            }
            Inst::GlobalLoad { dest, global } => {
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_global_load(ptr %l{dest}, i32 {global})"
                );
            }
            Inst::GlobalStore { global, src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_global_store(i32 {global}, ptr {src})"
                );
            }
            Inst::ExistentialPack {
                dest,
                protocol,
                payload,
                witnesses,
            } => {
                let symbol = self.display_id(*protocol);
                self.existential_ids.insert(symbol);
                let values: Vec<_> = std::iter::once(*payload)
                    .chain(witnesses.iter().copied())
                    .collect();
                let values = self.snapshot_operands(out, &values);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_dyn_agg(ptr %l{dest}, i32 {symbol}, i32 {})",
                    values.len()
                );
                for (index, value) in values.iter().enumerate() {
                    let _ = writeln!(
                        out,
                        "  call void @talk_llvm_agg_set(ptr %l{dest}, i32 {index}, ptr {value})"
                    );
                }
            }
            Inst::ExistentialWitness { dest, src, index } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_existential_witness(ptr %l{dest}, ptr {src}, i32 {index})"
                );
            }
            Inst::ExistentialPayload { dest, src } => {
                let src = self.operand(out, *src);
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_existential_payload(ptr %l{dest}, ptr {src})"
                );
            }
            Inst::AbortTo { cont, value } => {
                let cont = self.operand(out, *cont);
                let value = self.operand(out, *value);
                if identified {
                    let same = self.fresh("same_cont");
                    let direct = self
                        .fresh("abort_direct")
                        .trim_start_matches('%')
                        .to_string();
                    let routed = self
                        .fresh("abort_routed")
                        .trim_start_matches('%')
                        .to_string();
                    let _ = writeln!(
                        out,
                        "  {same} = call i32 @talk_llvm_cont_is(ptr {cont}, i64 %frame_depth, i32 %frame_id)"
                    );
                    let _ = writeln!(
                        out,
                        "  %same_bool{} = trunc i32 {same} to i1",
                        self.next_value
                    );
                    let bool_name = format!("%same_bool{}", self.next_value);
                    self.next_value += 1;
                    let _ = writeln!(out, "  br i1 {bool_name}, label %{direct}, label %{routed}");
                    let _ = writeln!(out, "{direct}:");
                    self.copy_value(out, "%out", &value);
                    let _ = writeln!(out, "  call void @talk_llvm_leave()");
                    let _ = writeln!(out, "  ret void");
                    let _ = writeln!(out, "{routed}:");
                }
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_abort_to(ptr {cont}, ptr {value})"
                );
                self.return_unit(out, identified);
            }
            Inst::GetElement {
                dest,
                src,
                element,
                index,
            } => {
                let src = self.operand(out, *src);
                let index = self.operand(out, *index);
                let symbol = self.layout_display(*element)?;
                let _ = writeln!(
                    out,
                    "  call void @talk_llvm_get_element(ptr %l{dest}, ptr {src}, ptr {index}, i32 {element}, i32 {symbol})"
                );
            }
        }
        Ok(())
    }

    fn scalar(
        &mut self,
        out: &mut String,
        dest: u16,
        op: ScalarOp,
        a: Operand,
        b: Option<Operand>,
    ) -> Result<(), Error> {
        let a = self.operand(out, a);
        let ap = self.fresh("ap");
        let av = self.fresh("a");
        let _ = writeln!(
            out,
            "  {ap} = getelementptr inbounds %TalkValue, ptr {a}, i32 0, i32 2"
        );
        let _ = writeln!(out, "  {av} = load i64, ptr {ap}, align 8");
        let b_pair = b.map(|b| {
            let b = self.operand(out, b);
            let bp = self.fresh("bp");
            let bv = self.fresh("rhs");
            let _ = writeln!(
                out,
                "  {bp} = getelementptr inbounds %TalkValue, ptr {b}, i32 0, i32 2"
            );
            let _ = writeln!(out, "  {bv} = load i64, ptr {bp}, align 8");
            (b, bv)
        });

        if matches!(
            op,
            ScalarOp::IntDiv | ScalarOp::FloatToIntTrunc | ScalarOp::IntToByte
        ) {
            let code = match op {
                ScalarOp::IntDiv => 0,
                ScalarOp::FloatToIntTrunc => 1,
                ScalarOp::IntToByte => 2,
                _ => unreachable!(),
            };
            let b = b_pair
                .as_ref()
                .map(|(pointer, _)| pointer.as_str())
                .unwrap_or("ptr null");
            let b_arg = if b == "ptr null" {
                "ptr null".to_string()
            } else {
                format!("ptr {b}")
            };
            let _ = writeln!(
                out,
                "  call void @talk_llvm_checked_scalar(ptr %l{dest}, i32 {code}, ptr {a}, {b_arg})"
            );
            return Ok(());
        }

        let bv = b_pair
            .as_ref()
            .map(|(_, value)| value.as_str())
            .unwrap_or_default();
        let unary = matches!(
            op,
            ScalarOp::IntNot | ScalarOp::ByteNot | ScalarOp::IntToFloat | ScalarOp::ByteToInt
        );
        if !unary && bv.is_empty() {
            return Err(internal("a binary scalar operation has no right operand"));
        }
        let result = self.fresh("scalar");
        let (tag, payload) = match op {
            ScalarOp::IntAdd => {
                let _ = writeln!(out, "  {result} = add i64 {av}, {}", bv);
                (2, result.clone())
            }
            ScalarOp::IntSub => {
                let _ = writeln!(out, "  {result} = sub i64 {av}, {}", bv);
                (2, result.clone())
            }
            ScalarOp::IntMul => {
                let _ = writeln!(out, "  {result} = mul i64 {av}, {}", bv);
                (2, result.clone())
            }
            ScalarOp::IntAnd | ScalarOp::ByteAnd => {
                let _ = writeln!(out, "  {result} = and i64 {av}, {}", bv);
                (
                    if matches!(op, ScalarOp::ByteAnd) {
                        7
                    } else {
                        2
                    },
                    result.clone(),
                )
            }
            ScalarOp::IntOr | ScalarOp::ByteOr => {
                let _ = writeln!(out, "  {result} = or i64 {av}, {}", bv);
                (
                    if matches!(op, ScalarOp::ByteOr) { 7 } else { 2 },
                    result.clone(),
                )
            }
            ScalarOp::IntXor | ScalarOp::ByteXor => {
                let _ = writeln!(out, "  {result} = xor i64 {av}, {}", bv);
                (
                    if matches!(op, ScalarOp::ByteXor) {
                        7
                    } else {
                        2
                    },
                    result.clone(),
                )
            }
            ScalarOp::IntNot | ScalarOp::ByteNot => {
                let _ = writeln!(out, "  {result} = xor i64 {av}, -1");
                (
                    if matches!(op, ScalarOp::ByteNot) {
                        7
                    } else {
                        2
                    },
                    result.clone(),
                )
            }
            ScalarOp::IntShl | ScalarOp::IntShr | ScalarOp::ByteShl | ScalarOp::ByteShr => {
                let mask = if matches!(op, ScalarOp::ByteShl | ScalarOp::ByteShr) {
                    7
                } else {
                    63
                };
                let amount = self.fresh("shift");
                let _ = writeln!(out, "  {amount} = and i64 {}, {mask}", bv);
                let opcode = match op {
                    ScalarOp::IntShl | ScalarOp::ByteShl => "shl",
                    ScalarOp::IntShr => "ashr",
                    ScalarOp::ByteShr => "lshr",
                    _ => unreachable!(),
                };
                let _ = writeln!(out, "  {result} = {opcode} i64 {av}, {amount}");
                (
                    if matches!(op, ScalarOp::ByteShl | ScalarOp::ByteShr) {
                        7
                    } else {
                        2
                    },
                    result.clone(),
                )
            }
            ScalarOp::IntCmp(kind) | ScalarOp::ByteCmp(kind) | ScalarOp::BoolCmp(kind) => {
                let bit = self.fresh("cmp");
                let _ = writeln!(
                    out,
                    "  {bit} = icmp {} i64 {av}, {}",
                    int_predicate(kind),
                    bv
                );
                let _ = writeln!(out, "  {result} = zext i1 {bit} to i64");
                (1, result.clone())
            }
            ScalarOp::FloatAdd | ScalarOp::FloatSub | ScalarOp::FloatMul | ScalarOp::FloatDiv => {
                let af = self.fresh("af");
                let bf = self.fresh("bf");
                let rf = self.fresh("rf");
                let _ = writeln!(out, "  {af} = bitcast i64 {av} to double");
                let _ = writeln!(out, "  {bf} = bitcast i64 {} to double", bv);
                let opcode = match op {
                    ScalarOp::FloatAdd => "fadd",
                    ScalarOp::FloatSub => "fsub",
                    ScalarOp::FloatMul => "fmul",
                    ScalarOp::FloatDiv => "fdiv",
                    _ => unreachable!(),
                };
                let _ = writeln!(out, "  {rf} = {opcode} double {af}, {bf}");
                let _ = writeln!(out, "  {result} = bitcast double {rf} to i64");
                (8, result.clone())
            }
            ScalarOp::FloatCmp(kind) => {
                let af = self.fresh("af");
                let bf = self.fresh("bf");
                let bit = self.fresh("fcmp");
                let _ = writeln!(out, "  {af} = bitcast i64 {av} to double");
                let _ = writeln!(out, "  {bf} = bitcast i64 {} to double", bv);
                let _ = writeln!(
                    out,
                    "  {bit} = fcmp {} double {af}, {bf}",
                    float_predicate(kind)
                );
                let _ = writeln!(out, "  {result} = zext i1 {bit} to i64");
                (1, result.clone())
            }
            ScalarOp::IntToFloat => {
                let float = self.fresh("itof");
                let _ = writeln!(out, "  {float} = sitofp i64 {av} to double");
                let _ = writeln!(out, "  {result} = bitcast double {float} to i64");
                (8, result.clone())
            }
            ScalarOp::ByteToInt => {
                let _ = writeln!(out, "  {result} = and i64 {av}, 255");
                (2, result.clone())
            }
            ScalarOp::IntDiv | ScalarOp::FloatToIntTrunc | ScalarOp::IntToByte => unreachable!(),
        };
        let normalized = if tag == 7 {
            let masked = self.fresh("byte");
            let _ = writeln!(out, "  {masked} = and i64 {payload}, 255");
            masked
        } else {
            payload
        };
        let value = self.tagged_value(out, tag, &format!("i64 {normalized}"));
        let _ = writeln!(out, "  store %TalkValue {value}, ptr %l{dest}, align 8");
        Ok(())
    }

    fn tagged_value(&mut self, out: &mut String, tag: u8, payload: &str) -> String {
        let tagged = self.fresh("tagged");
        let value = self.fresh("value");
        let _ = writeln!(
            out,
            "  {tagged} = insertvalue %TalkValue zeroinitializer, i8 {tag}, 0"
        );
        let _ = writeln!(
            out,
            "  {value} = insertvalue %TalkValue {tagged}, {payload}, 2"
        );
        value
    }

    fn aggregate(
        &mut self,
        out: &mut String,
        dest: u16,
        layout: LayoutId,
        tag: u16,
        args: &[Operand],
    ) -> Result<(), Error> {
        let symbol = self.layout_display(layout)?;
        let args = self.snapshot_operands(out, args);
        let _ = writeln!(
            out,
            "  call void @talk_llvm_agg(ptr %l{dest}, i32 {layout}, i32 {symbol}, i32 {tag})"
        );
        for (index, arg) in args.iter().enumerate() {
            let _ = writeln!(
                out,
                "  call void @talk_llvm_agg_arg(ptr %l{dest}, i32 {layout}, i32 {tag}, i32 {index}, ptr {arg})"
            );
        }
        Ok(())
    }

    fn unwind_check(&mut self, out: &mut String, unwind: Option<usize>, identified: bool) {
        let flag = self.fresh("unwinding");
        let is_unwinding = self.fresh("is_unwinding");
        let check = self
            .fresh("unwind_check")
            .trim_start_matches('%')
            .to_string();
        let after = self.fresh("after_call").trim_start_matches('%').to_string();
        let _ = writeln!(out, "  {flag} = call i32 @talk_llvm_unwinding()");
        let _ = writeln!(out, "  {is_unwinding} = trunc i32 {flag} to i1");
        let _ = writeln!(
            out,
            "  br i1 {is_unwinding}, label %{check}, label %{after}"
        );
        let _ = writeln!(out, "{check}:");
        if identified {
            let targets = self.fresh("targets");
            let target_bool = self.fresh("targets_bool");
            let take = self
                .fresh("unwind_take")
                .trim_start_matches('%')
                .to_string();
            let onward = self
                .fresh("unwind_onward")
                .trim_start_matches('%')
                .to_string();
            let _ = writeln!(
                out,
                "  {targets} = call i32 @talk_llvm_unwind_targets(i64 %frame_depth, i32 %frame_id)"
            );
            let _ = writeln!(out, "  {target_bool} = trunc i32 {targets} to i1");
            let _ = writeln!(out, "  br i1 {target_bool}, label %{take}, label %{onward}");
            let _ = writeln!(out, "{take}:");
            let _ = writeln!(out, "  call void @talk_llvm_unwind_take(ptr %out)");
            let _ = writeln!(out, "  call void @talk_llvm_leave()");
            let _ = writeln!(out, "  ret void");
            let _ = writeln!(out, "{onward}:");
        }
        match unwind {
            Some(block) => {
                let _ = writeln!(out, "  br label %b{block}");
            }
            None => self.return_unit(out, identified),
        }
        let _ = writeln!(out, "{after}:");
    }

    fn return_unit(&mut self, out: &mut String, identified: bool) {
        let _ = writeln!(out, "  store %TalkValue zeroinitializer, ptr %out, align 8");
        if identified {
            let _ = writeln!(out, "  call void @talk_llvm_leave()");
        }
        let _ = writeln!(out, "  ret void");
    }

    fn term(
        &mut self,
        out: &mut String,
        term: &Term,
        function: &Function,
        identified: bool,
    ) -> Result<(), Error> {
        match term {
            Term::Goto(target, args) => {
                let params = &function
                    .blocks
                    .get(*target)
                    .ok_or_else(|| internal("branch to a block that does not exist"))?
                    .params;
                if params.len() != args.len() {
                    return Err(internal(
                        "block argument count does not match its parameters",
                    ));
                }
                let mut values = Vec::new();
                for arg in args {
                    let arg = self.operand(out, *arg);
                    let value = self.fresh("edge");
                    let _ = writeln!(out, "  {value} = load %TalkValue, ptr {arg}, align 8");
                    values.push(value);
                }
                for (param, value) in params.iter().zip(values) {
                    let _ = writeln!(out, "  store %TalkValue {value}, ptr %l{param}, align 8");
                }
                let _ = writeln!(out, "  br label %b{target}");
            }
            Term::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond = self.operand(out, *cond);
                let payload = self.fresh("condp");
                let value = self.fresh("cond");
                let bit = self.fresh("condbit");
                let _ = writeln!(
                    out,
                    "  {payload} = getelementptr inbounds %TalkValue, ptr {cond}, i32 0, i32 2"
                );
                let _ = writeln!(out, "  {value} = load i64, ptr {payload}, align 8");
                let _ = writeln!(out, "  {bit} = icmp ne i64 {value}, 0");
                let _ = writeln!(
                    out,
                    "  br i1 {bit}, label %b{then_block}, label %b{else_block}"
                );
            }
            Term::Switch {
                tag,
                targets,
                default,
            } => {
                let tag = self.operand(out, *tag);
                let payload = self.fresh("switchp");
                let value = self.fresh("switch");
                let _ = writeln!(
                    out,
                    "  {payload} = getelementptr inbounds %TalkValue, ptr {tag}, i32 0, i32 2"
                );
                let _ = writeln!(out, "  {value} = load i64, ptr {payload}, align 8");
                let _ = writeln!(out, "  switch i64 {value}, label %b{default} [");
                for (case, target) in targets.iter().enumerate() {
                    let _ = writeln!(out, "    i64 {case}, label %b{target}");
                }
                let _ = writeln!(out, "  ]");
            }
            Term::Return(value) => {
                let value = self.operand(out, *value);
                self.copy_value(out, "%out", &value);
                if identified {
                    let _ = writeln!(out, "  call void @talk_llvm_leave()");
                }
                let _ = writeln!(out, "  ret void");
            }
            Term::Trap(message) => {
                let name = self.trap_string(out, message);
                let _ = writeln!(out, "  call void @talk_llvm_trap(ptr {name})");
                let _ = writeln!(out, "  unreachable");
            }
            Term::UnwindRet => self.return_unit(out, identified),
        }
        Ok(())
    }

    fn trap_string(&mut self, out: &mut String, message: &str) -> String {
        // MIR trap messages are fixed ASCII strings. Allocate one local byte
        // array so the module stays valid without a separate globals pass.
        let bytes = message.as_bytes();
        let buffer = self.fresh("trap");
        let _ = writeln!(
            out,
            "  {buffer} = alloca [{} x i8], align 1",
            bytes.len() + 1
        );
        for (index, byte) in bytes.iter().chain(std::iter::once(&0)).enumerate() {
            let pointer = self.fresh("trap_byte");
            let _ = writeln!(
                out,
                "  {pointer} = getelementptr inbounds [{} x i8], ptr {buffer}, i32 0, i32 {index}",
                bytes.len() + 1
            );
            let _ = writeln!(out, "  store i8 {byte}, ptr {pointer}, align 1");
        }
        buffer
    }

    fn dispatch(&mut self, out: &mut String, program: &Module) {
        let _ = writeln!(
            out,
            "\ndefine void @talk_llvm_dispatch(ptr %out, i32 %function, ptr %env, ptr %args) {{"
        );
        let _ = writeln!(out, "entry:");
        let _ = writeln!(out, "  switch i32 %function, label %unknown [");
        for id in 0..program.functions.len() {
            let _ = writeln!(out, "    i32 {id}, label %fn{id}");
        }
        let _ = writeln!(out, "  ]");
        for id in 0..program.functions.len() {
            let _ = writeln!(
                out,
                "fn{id}:\n  call void @talk_fn{id}(ptr %out, ptr %env, ptr %args)\n  ret void"
            );
        }
        let _ = writeln!(
            out,
            "unknown:\n  call void @talk_llvm_trap(ptr @unknown_function)\n  unreachable\n}}"
        );
        let _ = writeln!(
            out,
            "\n@unknown_function = private constant [28 x i8] c\"call to an unknown function\\00\""
        );
    }

    fn entry(&mut self, out: &mut String, entry: usize) {
        let _ = writeln!(
            out,
            "\ndefine void @talk_llvm_entry(ptr %out) {{\nentry:\n  call void @talk_fn{entry}(ptr %out, ptr null, ptr null)\n  ret void\n}}"
        );
    }

    fn runtime_source(&self, global_slots: u32, names: &DisplayNames) -> String {
        let mut out = String::from("#include <stddef.h>\n");
        out.push_str(talk_native_runtime::source());
        out.push('\n');
        emit_statics(&mut out, &self.statics);
        emit_layout_table(&mut out, self);
        emit_type_table(&mut out, self, names);
        let _ = writeln!(
            out,
            "static unsigned char talk_globals[{}];",
            (u64::from(global_slots) * 8).max(1)
        );
        out.push_str(RUNTIME_ABI);
        out.push_str("\nextern void talk_llvm_entry(TalkValue *out);\n");
        out.push_str("int main(int argc, char **argv) {\n");
        out.push_str("    talk_argc = argc; talk_argv = argv;\n");
        out.push_str("    { char anchor; talk_stack_init((uintptr_t)&anchor); }\n");
        out.push_str(
            "    talk_statics_base = talk_statics; talk_statics_len = sizeof talk_statics;\n",
        );
        out.push_str("    talk_types = talk_type_table; talk_type_count = sizeof talk_type_table / sizeof *talk_type_table;\n");
        let _ = writeln!(
            out,
            "    talk_layouts = talk_layout_table; talk_layout_count = {};",
            self.layouts.len()
        );
        out.push_str("    TalkValue result = talk_unit(); talk_llvm_entry(&result);\n");
        out.push_str("    int status = talk_print(result); talk_arena_release(); talk_effects_release(); return status;\n}\n");
        out
    }
}

fn emit_statics(out: &mut String, bytes: &[u8]) {
    let _ = write!(out, "static unsigned char talk_statics[] = {{");
    for byte in bytes {
        let _ = write!(out, "{byte},");
    }
    if bytes.is_empty() {
        let _ = write!(out, "0");
    }
    let _ = writeln!(out, "}};");
}

fn emit_layout_table(out: &mut String, emitter: &Emitter) {
    for (id, layout) in emitter.layouts.iter().enumerate() {
        let shape = match layout {
            Layout::Inline(_, shape) | Layout::Boxed(_, shape) => shape,
            Layout::Slot | Layout::Opaque => continue,
        };
        let (offsets, reprs): (Vec<_>, Vec<_>) = match shape {
            Shape::Product { offsets, reprs, .. } => (offsets.clone(), reprs.clone()),
            Shape::Sum {
                payloads, reprs, ..
            } => (
                payloads.iter().flatten().copied().collect(),
                reprs.iter().flatten().copied().collect(),
            ),
        };
        if !reprs.is_empty() {
            let _ = writeln!(out, "static const TalkField talk_layout_fields_{id}[] = {{");
            for (offset, repr) in offsets.iter().zip(&reprs) {
                match repr {
                    FieldRepr::Slot(_) => {
                        let _ = writeln!(out, "    {{ {offset}, 1, UINT32_MAX, 0 }},");
                    }
                    FieldRepr::Spliced(child) => {
                        let width = emitter.layout_width(*child);
                        let symbol = emitter.published_display(*child);
                        let _ = writeln!(out, "    {{ {offset}, {width}, {child}, {symbol} }},");
                    }
                }
            }
            let _ = writeln!(out, "}};");
        }
        if let Shape::Sum { reprs, .. } = shape {
            let mut start = 0usize;
            let _ = write!(
                out,
                "static const uint32_t talk_layout_starts_{id}[] = {{ 0"
            );
            for variant in reprs {
                start += variant.len();
                let _ = write!(out, ", {start}");
            }
            let _ = writeln!(out, " }};");
        }
    }

    let _ = writeln!(out, "static const TalkLayoutInfo talk_layout_table[] = {{");
    if emitter.layouts.is_empty() {
        let _ = writeln!(out, "    {{ 0, 0, NULL, 0, NULL, 0 }},");
    }
    for (id, layout) in emitter.layouts.iter().enumerate() {
        match layout {
            Layout::Slot | Layout::Opaque => {
                let _ = writeln!(out, "    {{ 1, 0, NULL, 0, NULL, 0 }},");
            }
            Layout::Inline(_, Shape::Product { width, reprs, .. })
            | Layout::Boxed(_, Shape::Product { width, reprs, .. }) => {
                let fields = if reprs.is_empty() {
                    "NULL".to_string()
                } else {
                    format!("talk_layout_fields_{id}")
                };
                let _ = writeln!(
                    out,
                    "    {{ {width}, 0, {fields}, {}, NULL, 0 }},",
                    reprs.len()
                );
            }
            Layout::Inline(_, Shape::Sum { width, reprs, .. })
            | Layout::Boxed(_, Shape::Sum { width, reprs, .. }) => {
                let field_count: usize = reprs.iter().map(Vec::len).sum();
                let fields = if field_count == 0 {
                    "NULL".to_string()
                } else {
                    format!("talk_layout_fields_{id}")
                };
                let _ = writeln!(
                    out,
                    "    {{ {width}, 1, {fields}, {field_count}, talk_layout_starts_{id}, {} }},",
                    reprs.len()
                );
            }
        }
    }
    let _ = writeln!(out, "}};");
}

fn emit_type_table(out: &mut String, emitter: &Emitter, display: &DisplayNames) {
    let mut ordered: Vec<_> = emitter.display_ids.iter().collect();
    ordered.sort_by_key(|(_, id)| **id);
    for (symbol, id) in &ordered {
        let members = display
            .entries
            .get(symbol)
            .map(|entry| entry.members.as_slice())
            .unwrap_or_default();
        if members.is_empty() {
            continue;
        }
        let rendered: Vec<_> = members
            .iter()
            .map(|member| format!("\"{}\"", c_escape(member)))
            .collect();
        let _ = writeln!(
            out,
            "static const char *const talk_members_{id}[] = {{ {} }};",
            rendered.join(", ")
        );
    }
    let _ = writeln!(out, "static const TalkTypeInfo talk_type_table[] = {{");
    let _ = writeln!(out, "    {{ \"\", TALK_TYPE_TUPLE, 0, NULL }},");
    for (symbol, id) in ordered {
        if emitter.existential_ids.contains(id) {
            let _ = writeln!(out, "    {{ \"\", TALK_TYPE_EXISTENTIAL, 0, NULL }},");
            continue;
        }
        let Some(entry) = display.entries.get(symbol) else {
            let _ = writeln!(out, "    {{ \"\", TALK_TYPE_TUPLE, 0, NULL }},");
            continue;
        };
        let kind = match entry.kind {
            TypeKind::Record => "TALK_TYPE_RECORD",
            TypeKind::Enum => "TALK_TYPE_ENUM",
            TypeKind::String => "TALK_TYPE_STRING",
        };
        let members = &entry.members;
        let name = &entry.name;
        let member_ref = if members.is_empty() {
            "NULL".into()
        } else {
            format!("talk_members_{id}")
        };
        let _ = writeln!(
            out,
            "    {{ \"{}\", {kind}, {}, {member_ref} }},",
            c_escape(name),
            members.len()
        );
    }
    let _ = writeln!(out, "}};");
}

fn mem_kind(kind: SlotKind) -> u32 {
    match kind {
        SlotKind::Byte => 0,
        SlotKind::Int => 1,
        SlotKind::F64 => 2,
        SlotKind::Bool => 3,
        SlotKind::Ptr => 4,
        SlotKind::Value => 5,
    }
}

fn int_predicate(kind: CmpKind) -> &'static str {
    match kind {
        CmpKind::Eq => "eq",
        CmpKind::Ne => "ne",
        CmpKind::Lt => "slt",
        CmpKind::Le => "sle",
        CmpKind::Gt => "sgt",
        CmpKind::Ge => "sge",
    }
}

fn float_predicate(kind: CmpKind) -> &'static str {
    match kind {
        CmpKind::Eq => "oeq",
        CmpKind::Ne => "une",
        CmpKind::Lt => "olt",
        CmpKind::Le => "ole",
        CmpKind::Gt => "ogt",
        CmpKind::Ge => "oge",
    }
}

fn needs_identity(function: &Function) -> bool {
    function.blocks.iter().any(|block| {
        block.insts.iter().any(|inst| {
            matches!(
                inst,
                Inst::MakeCont { .. } | Inst::PushHandler { .. } | Inst::AbortTo { .. }
            )
        })
    })
}

fn llvm_comment(text: &str) -> String {
    text.replace(['\n', '\r'], " ")
}
fn c_escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"")
}
fn internal(message: &str) -> Error {
    Error::new(format!("LLVM backend: {message}"))
}
