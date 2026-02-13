use std::fmt::Display;

use crate::compiling::driver::{CompilationMode, DriverConfig, Typed};
use crate::compiling::module::ModuleId;
use crate::ir::basic_block::{Phi, PhiSource};
use crate::ir::function::Function;
use crate::ir::instruction::CmpOperator;
use crate::ir::ir_ty::IrTy;
use crate::ir::monomorphizer::uncurry_function;
use crate::ir::value::{Addr, RecordId};
use crate::label::Label;
use crate::node_kinds::inline_ir_instruction::{InlineIRInstructionKind, TypedInlineIRInstruction};
use crate::node_kinds::type_annotation::TypeAnnotation;
use crate::types::infer_row::Row;
use crate::types::typed_ast::{
    TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc, TypedMatchArm,
    TypedNode, TypedParameter, TypedPattern, TypedPatternKind, TypedRecordField, TypedStmt,
    TypedStmtKind,
};
use crate::types::type_catalog::Nominal;
use crate::types::types::TypeEntry;
use crate::{
    ir::{
        basic_block::{BasicBlock, BasicBlockId},
        instruction::{Instruction, InstructionMeta},
        ir_error::IRError,
        monomorphizer::Monomorphizer,
        program::Program,
        register::Register,
        terminator::Terminator,
        value::Value,
    },
    name::Name,
    name_resolution::symbol::{Symbol, SynthesizedId},
    node_id::{FileID, NodeID},
    types::{
        infer_ty::Ty,
        matcher::{
            Constructor, MatchPlan, PlanNode, PlanNodeId, Projection, ValueId, ValueRef,
            plan_for_pattern,
        },
    },
};
use indexmap::IndexMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use tracing::instrument;

#[derive(Debug)]
enum LValue {
    Field {
        base: Box<LValue>,
        field: Label,
        ty: Ty,
    },
    Variable(Symbol),
}

impl Display for LValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug)]
pub(super) struct CurrentFunction {
    current_block_idx: Vec<usize>,
    blocks: Vec<BasicBlock<Ty>>,
    pub registers: RegisterAllocator,
    bindings: IndexMap<Symbol, Binding<Ty>>,
    symbol: Symbol,
}

impl CurrentFunction {
    fn new(symbol: Symbol) -> Self {
        CurrentFunction {
            symbol,
            current_block_idx: vec![0],
            blocks: vec![BasicBlock::<Ty> {
                phis: Default::default(),
                id: BasicBlockId(0),
                instructions: Default::default(),
                terminator: Terminator::Unreachable,
            }],
            registers: Default::default(),
            bindings: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct StaticMemory {
    pub data: Vec<u8>,
}

impl StaticMemory {
    pub fn write(&mut self, value: Value) -> usize {
        let addr = self.data.len();
        self.data.extend(value.as_bytes());
        addr
    }

    #[allow(clippy::unwrap_used)]
    #[warn(clippy::todo)]
    pub fn load(&self, at: usize, len: usize, ty: IrTy) -> Value {
        let bytes = &self.data[at..len];
        match ty {
            IrTy::Int => Value::Int(i64::from_le_bytes(bytes.try_into().unwrap())),
            IrTy::Float => Value::Float(f64::from_le_bytes(bytes.try_into().unwrap())),
            IrTy::Bool => Value::Bool(bytes[0] == 1),
            IrTy::Func(..) => Value::Func(Symbol::from_bytes(bytes.try_into().unwrap())),
            IrTy::Record(..) => unreachable!("can only load primitives"),
            IrTy::RawPtr => {
                Value::RawPtr(Addr(u64::from_le_bytes(bytes.try_into().unwrap()) as usize))
            }
            IrTy::Byte => Value::RawBuffer(bytes.to_vec()),
            IrTy::Void => unreachable!("cannot load the void"),
            IrTy::Buffer(..) => Value::RawBuffer(bytes.to_vec()),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Bind {
    Assigned(Register),
    Indirect(Register, Symbol),
    Fresh,
    Discard,
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub(super) struct RegisterAllocator {
    next: u32,
}

impl RegisterAllocator {
    fn next(&mut self) -> Register {
        let i = self.next;
        self.next += 1;
        Register(i)
    }
}

#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct PolyFunction {
    pub name: Symbol,
    pub params: Vec<Value>,
    pub blocks: Vec<BasicBlock<Ty>>,
    pub ty: Ty,
    pub register_count: usize,
    /// For methods, the register containing the final self value (after mutations).
    pub self_out: Option<Register>,
}

pub enum FlowContext {
    Loop {
        top_block_id: BasicBlockId,
        join_block_id: BasicBlockId,
    },
}

#[derive(Debug, Clone)]
pub enum Binding<T> {
    Register(u32),
    Pointer(Value),
    Capture { index: usize, ty: T },
    Continued { index: usize, ty: T },
}

impl<T> From<Register> for Binding<T> {
    fn from(value: Register) -> Self {
        Binding::Register(value.0)
    }
}

impl<T> From<Value> for Binding<T> {
    fn from(value: Value) -> Self {
        Binding::Pointer(value)
    }
}

#[derive(Debug)]
pub enum FuncTermination {
    Return,
    Continuation(Symbol),
}

/// Context for state machine compilation mode
#[derive(Debug)]
pub struct StateMachineContext {
    /// The analysis results for this effectful function
    pub analysis: super::effect_analysis::EffectAnalysis,
    /// Current state index being generated
    pub current_state: usize,
    /// Register holding the state index parameter
    pub state_var: Register,
    /// Register holding the state data parameter
    pub state_data: Register,
    /// Register holding the resumed value parameter
    pub resumed_var: Register,
    /// The original function name being compiled
    pub func_name: Symbol,
    /// Entry block IDs for each state (state 0 = initial, state N = continuation after yield N-1)
    pub state_entries: Vec<BasicBlockId>,
}

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer<'a> {
    pub(super) typed: &'a mut Typed,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,
    pub(super) config: &'a DriverConfig,
    static_memory: StaticMemory,
    record_labels: FxHashMap<RecordId, Vec<String>>,
    next_record_id: u32,
    flow_context_stack: Vec<FlowContext>,
    pending_continuations: Vec<(CurrentFunction, Symbol, Register)>,
    current_continuation_idx: Option<usize>,
    /// When set, we're compiling in state machine mode for effectful functions
    state_machine_context: Option<StateMachineContext>,
}

#[allow(clippy::panic)]
#[allow(clippy::expect_used)]
impl<'a> Lowerer<'a> {
    pub fn new(typed: &'a mut Typed, config: &'a DriverConfig) -> Self {
        Self {
            functions: Default::default(),
            current_function_stack: Default::default(),
            typed,
            static_memory: Default::default(),
            config,
            next_record_id: 0,
            record_labels: Default::default(),
            flow_context_stack: Default::default(),
            pending_continuations: Default::default(),
            current_continuation_idx: None,
            state_machine_context: None,
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.typed.ast.roots().is_empty() {
            let mut program = Program::default();
            program.functions.insert(
                Symbol::Main,
                Function {
                    name: Symbol::Main,
                    params: Default::default(),
                    blocks: Default::default(),
                    ty: IrTy::Void,
                    register_count: 0,
                    self_out: None,
                },
            );
            return Ok(program);
        }

        if self.config.mode == CompilationMode::Executable {
            self.lower_main();
            self.current_function_stack
                .push(CurrentFunction::new(Symbol::Main));
        } else {
            self.current_function_stack
                .push(CurrentFunction::new(Symbol::Library));
        }

        for root in self.typed.ast.roots() {
            self.lower_node(&root)?;
        }

        let mut static_memory = std::mem::take(&mut self.static_memory);
        let record_labels = std::mem::take(&mut self.record_labels);
        let functions = std::mem::take(&mut self.functions);
        let mut monomorphizer = Monomorphizer::new(
            &self.typed.types,
            functions,
            self.config,
            &self.typed.specializations,
            &self.typed.specialized_callees,
            &self.typed.call_resolutions,
            &mut static_memory,
            &self.typed.resolved_names.symbol_names,
        );

        let mono_functions = monomorphizer.monomorphize();
        let extern_synth_origins = std::mem::take(&mut monomorphizer.extern_synth_origins);

        Ok(Program {
            functions: mono_functions,
            polyfunctions: monomorphizer.functions,
            static_memory,
            record_labels,
            extern_synth_origins,
        })
    }

    fn lower_main(&mut self) {
        // Do we have a main func?
        let has_main_func = self
            .typed
            .ast
            .decls
            .iter()
            .any(|d| is_main_func(d, &self.typed.resolved_names.symbol_names));
        if !has_main_func {
            let main_symbol = Symbol::Main;
            let mut ret_ty = Ty::Void;

            let func = TypedFunc {
                name: main_symbol,
                foralls: Default::default(),
                params: Default::default(),
                effects: Default::default(),
                effects_row: Row::Empty,
                body: TypedBlock {
                    body: {
                        let nodes: Vec<TypedNode> = self.typed.ast.roots();

                        if let Some(last) = nodes.last() {
                            ret_ty = last.ty();
                        }

                        nodes
                    },
                    id: NodeID(FileID(0), 0),
                    ret: Ty::Void,
                },
                ret: Ty::Void,
            };

            #[allow(clippy::unwrap_used)]
            self.typed.ast.decls.push(TypedDecl {
                id: NodeID(FileID(0), 0),
                ty: Ty::Func(Ty::Void.into(), Ty::Void.into(), Row::Empty.into()),
                kind: TypedDeclKind::Let {
                    pattern: TypedPattern {
                        id: NodeID(FileID(0), 0),
                        ty: Ty::Func(Ty::Void.into(), Ty::Void.into(), Row::Empty.into()),
                        kind: TypedPatternKind::Bind(Symbol::Main),
                    },
                    ty: Ty::Func(Ty::Void.into(), Ty::Void.into(), Row::Empty.into()),
                    initializer: Some(TypedExpr {
                        id: NodeID(FileID(0), 0),
                        ty: Ty::Func(Ty::Void.into(), Ty::Void.into(), Row::Empty.into()),
                        kind: TypedExprKind::Func(func),
                    }),
                },
            });

            self.typed.types.define(
                main_symbol,
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into(), Row::Empty.into())),
            );

            self.typed
                .resolved_names
                .symbol_names
                .insert(main_symbol, "main(synthesized)".to_string());
        }
    }

    fn lower_node(&mut self, node: &TypedNode) -> Result<(Value, Ty), IRError> {
        self.lower_node_with_bind(node, Bind::Fresh)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, node), fields(node.id = %node.node_id()))]
    fn lower_node_with_bind(
        &mut self,
        node: &TypedNode,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        tracing::info!("{node:?}");
        match node {
            TypedNode::Decl(decl) => self.lower_decl(decl),
            TypedNode::Stmt(stmt) => self.lower_stmt(stmt, bind),
            TypedNode::Expr(expr) => self.lower_expr(expr, bind),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl), fields(decl.id = %decl.id))]
    fn lower_decl(&mut self, decl: &TypedDecl) -> Result<(Value, Ty), IRError> {
        match &decl.kind {
            TypedDeclKind::Let {
                pattern,
                initializer,
                ..
            } => {
                // Store global constants for cross-module access
                if let TypedPatternKind::Bind(sym @ Symbol::Global(_)) = &pattern.kind
                    && let Some(init) = initializer
                {
                    let constant = match &init.kind {
                        TypedExprKind::LiteralInt(val) => val
                            .parse::<i64>()
                            .ok()
                            .map(crate::types::type_catalog::GlobalConstant::Int),
                        TypedExprKind::LiteralFloat(val) => val
                            .parse::<f64>()
                            .ok()
                            .map(crate::types::type_catalog::GlobalConstant::Float),
                        TypedExprKind::LiteralTrue => {
                            Some(crate::types::type_catalog::GlobalConstant::Bool(true))
                        }
                        TypedExprKind::LiteralFalse => {
                            Some(crate::types::type_catalog::GlobalConstant::Bool(false))
                        }
                        _ => None,
                    };
                    if let Some(c) = constant {
                        self.typed.types.catalog.global_constants.insert(*sym, c);
                    }
                }

                if matches!(
                    pattern.kind,
                    TypedPatternKind::Bind(_) | TypedPatternKind::Wildcard
                ) {
                    let bind = self.lower_pattern(pattern)?;
                    if let Some(initializer) = initializer {
                        match bind {
                            Bind::Assigned(reg) => {
                                self.lower_expr(initializer, Bind::Assigned(reg))?;
                            }
                            Bind::Fresh => {
                                self.lower_expr(initializer, Bind::Fresh)?;
                            }
                            Bind::Discard => {
                                self.lower_expr(initializer, Bind::Discard)?;
                            }
                            Bind::Indirect(reg, ..) => {
                                let (val, ty) = self.lower_expr(initializer, Bind::Fresh)?;
                                self.push_instr(Instruction::Store {
                                    value: val,
                                    ty,
                                    addr: reg.into(),
                                });
                            }
                        }
                    }
                } else if let Some(initializer) = initializer {
                    self.lower_let_pattern(pattern, initializer)?;
                }
            }
            TypedDeclKind::StructDef {
                symbol,
                initializers,
                instance_methods,
                properties,
                ..
            } => {
                for initializer in initializers.values() {
                    self.lower_init(decl, symbol, initializer)?;
                }

                for method in instance_methods.values() {
                    self.lower_method(method)?;
                }

                self.record_labels.insert(
                    RecordId::Nominal(*symbol),
                    properties.keys().map(|key| key.to_string()).collect(),
                );
            }
            TypedDeclKind::Extend {
                instance_methods, ..
            } => {
                for method in instance_methods.values() {
                    self.lower_method(method)?;
                }
            }
            TypedDeclKind::EnumDef {
                symbol,
                instance_methods,
                variants,
                ..
            } => {
                for method in instance_methods.values() {
                    self.lower_method(method)?;
                }

                self.record_labels.insert(
                    RecordId::Nominal(*symbol),
                    variants.keys().map(|key| key.to_string()).collect(),
                );
            }
            TypedDeclKind::ProtocolDef {
                instance_methods, ..
            } => {
                for method in instance_methods.values() {
                    self.lower_method(method)?;
                }
            }
            // Import declarations are handled at name resolution time, nothing to lower
            TypedDeclKind::Import => {}
        }

        Ok((Value::Void, Ty::Void))
    }

    fn lower_method(&mut self, func: &TypedFunc) -> Result<(Value, Ty), IRError> {
        self.lower_func(func, Bind::Discard, FuncTermination::Return)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, initializer))]
    fn lower_init(
        &mut self,
        decl: &TypedDecl,
        name: &Symbol,
        initializer: &TypedFunc,
    ) -> Result<(Value, Ty), IRError> {
        let param_tys = initializer.params.iter().map(|p| &p.ty).collect_vec();
        let func_ty = curry_ty(param_tys.iter().cloned(), decl.ty.clone());

        let Ty::Func(..) = func_ty else {
            unreachable!();
        };

        // Build param_ty from all params (for now, just use the first one for compatibility)
        let param_ty = if !param_tys.is_empty() {
            param_tys[0].clone()
        } else {
            unreachable!(
                "init has no params - param_tys: {param_tys:?} name: {name:?}, sym: {:?}, ty: {:?}, {:?}",
                #[allow(clippy::unwrap_used)]
                self.typed.types.get_symbol(name).unwrap(),
                func_ty,
                decl
            );
        };

        self.current_function_stack
            .push(CurrentFunction::new(*name));

        let mut param_values = vec![];
        for param in initializer.params.iter() {
            let register = self.next_register();
            param_values.push(Value::Reg(register.0));
            self.lower_param_binding(param, register);
        }

        let ret_ty = initializer.ret.clone();
        for node in initializer.body.body.iter() {
            self.lower_node(node)?;
        }

        // Return the first parameter (the struct being initialized).
        // We must look up its current binding, as field assignments update the binding
        // to point to new registers containing the modified struct (SSA-style).
        let self_param = &initializer.params[0];
        let self_out_reg = self.get_binding(&self_param.name);
        let struct_val: Value = self_out_reg.into();
        self.push_terminator(Terminator::Ret {
            val: struct_val.clone(),
            ty: ret_ty.clone(),
        });

        #[allow(clippy::expect_used)]
        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");

        self.functions.insert(
            initializer.name,
            PolyFunction {
                name: initializer.name,
                params: param_values.clone(),
                blocks: current_function.blocks,
                ty: Ty::Func(
                    Box::new(param_ty.clone()),
                    Box::new(ret_ty.clone()),
                    Row::Empty.into(),
                ),
                register_count: (current_function.registers.next) as usize,
                self_out: Some(self_out_reg),
            },
        );

        Ok((struct_val, ret_ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt), fields(stmt.id = %stmt.id))]
    fn lower_stmt(&mut self, stmt: &TypedStmt, bind: Bind) -> Result<(Value, Ty), IRError> {
        match &stmt.kind {
            TypedStmtKind::Expr(typed_expr) => self.lower_expr(typed_expr, bind),
            TypedStmtKind::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs),
            TypedStmtKind::Return(typed_expr) => self.lower_return(typed_expr, bind),
            TypedStmtKind::Continue(Some(expr)) => self.lower_resume(stmt.id, expr, bind),
            TypedStmtKind::Continue(None) => self.lower_continue(),
            TypedStmtKind::Loop(cond, typed_block) => {
                self.lower_loop(&Some(cond.clone()), typed_block)
            }
            TypedStmtKind::Break => self.lower_break(),
            TypedStmtKind::Handler { func, .. } => self.lower_effect_handler(stmt.id, func, bind),
        }
    }

    fn lower_resume(
        &mut self,
        _id: NodeID,
        expr: &TypedExpr,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let (val, val_ty) = self.lower_expr(expr, Bind::Fresh)?;

        // Call continuation (register 0) with resumed value
        let dest = self.ret(bind);
        self.push_instr(Instruction::Call {
            dest,
            ty: val_ty.clone(),
            callee: Value::Reg(0),
            args: vec![val].into(),
            self_dest: None,
            meta: vec![].into(),
        });

        // Return result of continuation call
        self.push_terminator(Terminator::Ret {
            val: dest.into(),
            ty: val_ty,
        });

        Ok((Value::Void, Ty::Void))
    }

    fn lower_continue(&mut self) -> Result<(Value, Ty), IRError> {
        let top_block_id = match self.flow_context_stack.last() {
            Some(FlowContext::Loop { top_block_id, .. }) => *top_block_id,
            None => return Err(IRError::NoFlowContext),
        };

        self.push_terminator(Terminator::Jump { to: top_block_id });
        Ok((Value::Void, Ty::Void))
    }

    fn lower_break(&mut self) -> Result<(Value, Ty), IRError> {
        let join_block_id = match self.flow_context_stack.last() {
            Some(FlowContext::Loop { join_block_id, .. }) => *join_block_id,
            None => return Err(IRError::NoFlowContext),
        };

        self.push_terminator(Terminator::Jump { to: join_block_id });
        Ok((Value::Void, Ty::Void))
    }

    fn lower_loop(
        &mut self,
        cond: &Option<TypedExpr>,
        block: &TypedBlock,
    ) -> Result<(Value, Ty), IRError> {
        let top_block_id = self.new_basic_block();
        let body_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();
        self.push_terminator(Terminator::Jump { to: top_block_id });
        self.flow_context_stack.push(FlowContext::Loop {
            top_block_id,
            join_block_id,
        });

        self.in_basic_block(top_block_id, |lowerer| {
            if let Some(cond) = cond {
                let (val, _) = lowerer.lower_expr(cond, Bind::Fresh)?;
                lowerer.push_terminator(Terminator::Branch {
                    cond: val,
                    conseq: body_block_id,
                    alt: join_block_id,
                });
            } else {
                lowerer.push_terminator(Terminator::Jump { to: body_block_id });
            }

            Ok(())
        })?;

        self.in_basic_block(body_block_id, |lowerer| {
            lowerer.lower_block(block, Bind::Discard)?;
            lowerer.push_terminator(Terminator::Jump { to: top_block_id });

            Ok(())
        })?;

        self.set_current_block(join_block_id);

        self.flow_context_stack.pop();

        Ok((Value::Void, Ty::Void))
    }

    fn lower_return(
        &mut self,
        expr: &Option<TypedExpr>,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let (val, ty) = if let Some(expr) = expr {
            self.lower_expr(expr, bind)?
        } else {
            (Value::Void, Ty::Void)
        };

        self.push_terminator(Terminator::Ret {
            val: val.clone(),
            ty: ty.clone(),
        });

        Ok((val, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn lower_if_expr(
        &mut self,
        cond: &TypedExpr,
        conseq: &TypedBlock,
        alt: &TypedBlock,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let cond_ir = self.lower_expr(cond, Bind::Fresh)?;

        let conseq_block_id = self.new_basic_block();
        let alt_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();

        let conseq_val = self.in_basic_block(conseq_block_id, |lowerer| {
            let (val, _) = lowerer.lower_block(conseq, Bind::Fresh)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(val)
        })?;

        let alt_val = self.in_basic_block(alt_block_id, |lowerer| {
            let (val, _) = lowerer.lower_block(alt, Bind::Fresh)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(val)
        })?;

        self.push_terminator(Terminator::Branch {
            cond: cond_ir.0,
            conseq: conseq_block_id,
            alt: alt_block_id,
        });

        let ret = self.ret(bind);

        self.set_current_block(join_block_id);
        self.push_phi(Phi {
            dest: ret,
            ty: conseq.ret.clone(),
            sources: vec![
                PhiSource {
                    from_id: conseq_block_id,
                    value: conseq_val,
                },
                PhiSource {
                    from_id: alt_block_id,
                    value: alt_val,
                },
            ]
            .into(),
        });

        Ok((ret.into(), conseq.ret.clone()))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, block), fields(block.id = %block.id))]
    fn lower_block(&mut self, block: &TypedBlock, bind: Bind) -> Result<(Value, Ty), IRError> {
        for (i, node) in block.body.iter().enumerate() {
            // We want to skip the last one in the loop so we can handle it outside the loop and use our Bind
            if i < block.body.len() - 1 {
                self.lower_node(node)?;
            }
        }

        let (val, ty) = if let Some(node) = block.body.last() {
            self.lower_node_with_bind(node, bind)?
        } else {
            (Value::Void, Ty::Void)
        };

        Ok((val, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs), fields(lhs.id = %lhs.id, rhs.id = %rhs.id))]
    fn lower_assignment(
        &mut self,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
    ) -> Result<(Value, Ty), IRError> {
        let lvalue = self.lower_lvalue(lhs)?;
        let (value, ty) = self.lower_expr(rhs, Bind::Fresh)?;

        self.emit_lvalue_store(lvalue, value)?;

        Ok((Value::Void, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, receiver_ty))]
    fn emit_load_lvalue(&mut self, receiver_ty: &Ty, lvalue: &LValue) -> Result<Register, IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                // Variable is already in a register
                Ok(self.get_binding(sym))
            }
            LValue::Field { base, field, ty } => {
                // Recursively load base, then extract field
                let base_val = self.emit_load_lvalue(receiver_ty, base)?;
                let dest = self.next_register();

                self.push_instr(Instruction::GetField {
                    dest,
                    record: base_val,
                    field: self.field_index(receiver_ty, field),
                    ty: ty.clone(),
                    meta: vec![].into(),
                });

                Ok(dest)
            }
        }
    }

    fn emit_lvalue_store(&mut self, lvalue: LValue, value: Value) -> Result<(), IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                self.set_binding(&sym, value.as_register()?);
                Ok(())
            }
            LValue::Field {
                box base,
                field,
                ty: receiver_ty,
            } => {
                let base_val = self.emit_load_lvalue(&receiver_ty, &base)?;
                let dest = self.next_register();
                self.push_instr(Instruction::SetField {
                    dest,
                    record: base_val,
                    field: self.field_index(&receiver_ty, &field),
                    val: value,
                    ty: receiver_ty,
                    meta: vec![].into(),
                });

                self.emit_lvalue_store(base, dest.into())?;

                Ok(())
            }
        }
    }

    fn lower_lvalue(&mut self, expr: &TypedExpr) -> Result<LValue, IRError> {
        match &expr.kind {
            TypedExprKind::Variable(name) => Ok(LValue::Variable(*name)),
            TypedExprKind::Member {
                receiver: box receiver,
                label,
                ..
            } => {
                let receiver_ty = receiver.ty.clone();
                let receiver_lvalue = self.lower_lvalue(receiver)?;

                Ok(LValue::Field {
                    base: receiver_lvalue.into(),
                    ty: receiver_ty.clone(),
                    field: label.clone(),
                })
            }
            _ => Err(IRError::InvalidAssignmentTarget(format!("{expr:?}"))),
        }
    }

    fn lower_param_binding(&mut self, param: &TypedParameter, register: Register) {
        if self.typed.resolved_names.captured.contains(&param.name)
            || self
                .typed
                .resolved_names
                .mutated_symbols
                .contains(&param.name)
        {
            let ty = self
                .ty_from_symbol(&param.name)
                .expect("did not get ty for param");
            let addr = self.next_register();
            self.push_instr(Instruction::Alloc {
                dest: addr,
                ty: ty.clone(),
                count: 1.into(),
            });
            self.push_instr(Instruction::Store {
                value: register.into(),
                ty,
                addr: addr.into(),
            });
            self.insert_binding(param.name, Binding::Pointer(addr.into()));
        } else {
            self.insert_binding(param.name, register.into());
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, pattern), fields(pattern.id = %pattern.id))]
    fn lower_pattern(&mut self, pattern: &TypedPattern) -> Result<Bind, IRError> {
        match &pattern.kind {
            TypedPatternKind::Or(..) => unimplemented!(),
            TypedPatternKind::Bind(symbol) => {
                let value = if self.typed.resolved_names.captured.contains(symbol)
                    || self.typed.resolved_names.mutated_symbols.contains(symbol)
                {
                    let ty = self.ty_from_symbol(symbol).expect("did not get ty for sym");
                    let heap_addr = self.next_register();
                    self.push_instr(Instruction::Alloc {
                        dest: heap_addr,
                        ty,
                        count: 1.into(),
                    });
                    self.insert_binding(*symbol, Binding::Pointer(heap_addr.into()));
                    Bind::Indirect(heap_addr, *symbol)
                } else {
                    let val = self.next_register();

                    self.insert_binding(*symbol, val.into());
                    Bind::Assigned(val)
                };

                Ok(value)
            }
            #[allow(clippy::todo)]
            TypedPatternKind::LiteralInt(_) => todo!(),
            #[allow(clippy::todo)]
            TypedPatternKind::LiteralFloat(_) => todo!(),
            #[allow(clippy::todo)]
            TypedPatternKind::LiteralTrue => todo!(),
            #[allow(clippy::todo)]
            TypedPatternKind::LiteralFalse => todo!(),
            #[allow(clippy::todo)]
            TypedPatternKind::Tuple(..) => todo!(),
            TypedPatternKind::Wildcard => Ok(Bind::Discard),
            #[allow(clippy::todo)]
            TypedPatternKind::Variant { .. } => todo!(),
            #[allow(clippy::todo)]
            TypedPatternKind::Record { .. } => todo!(),
            #[allow(clippy::todo)]
            TypedPatternKind::Struct { .. } => todo!(),
        }
    }

    fn lower_let_pattern(
        &mut self,
        pattern: &TypedPattern,
        initializer: &TypedExpr,
    ) -> Result<(), IRError> {
        let scrutinee_register = self.next_register();
        self.lower_expr(initializer, Bind::Assigned(scrutinee_register))?;

        let plan = plan_for_pattern(&self.typed.types, pattern.ty.clone(), pattern);
        let value_regs = self.plan_value_registers(&plan, scrutinee_register);

        let mut symbol_binds: FxHashMap<Symbol, (ValueId, Ty)> = FxHashMap::default();
        for node in &plan.nodes {
            if let PlanNode::Arm { binds, .. } = node {
                for (symbol, value_id) in binds {
                    symbol_binds.entry(*symbol).or_insert_with(|| {
                        (*value_id, self.plan_value_ty(&plan, *value_id).clone())
                    });
                }
            }
        }

        for (symbol, (value_id, ty)) in &symbol_binds {
            if self.typed.resolved_names.captured.contains(symbol) {
                let addr = self.next_register();
                self.insert_binding(*symbol, Binding::Pointer(addr.into()));
            } else if let Some(reg) = value_regs.get(value_id).copied() {
                self.insert_binding(*symbol, reg.into());
            } else {
                self.ensure_match_binding(*symbol, ty.clone());
            }
        }

        let join_block_id = self.new_basic_block();
        let arm_block_ids = vec![join_block_id];
        self.lower_match_plan(&plan, scrutinee_register, &arm_block_ids, &value_regs)?;
        self.set_current_block(join_block_id);

        Ok(())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr), fields(expr.id = %expr.id))]
    fn lower_expr(&mut self, expr: &TypedExpr, bind: Bind) -> Result<(Value, Ty), IRError> {
        let (value, ty) = match &expr.kind {
            TypedExprKind::Hole => Err(IRError::TypeNotFound("nope".into())),
            TypedExprKind::CallEffect { effect, args, .. } => {
                self.lower_effect_call(expr, effect, args, bind)
            }
            TypedExprKind::InlineIR(inline_irinstruction) => {
                self.lower_inline_ir(inline_irinstruction, bind)
            }
            TypedExprKind::LiteralArray(typed_exprs) => self.lower_array(expr, typed_exprs, bind),
            TypedExprKind::LiteralInt(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::Constant {
                    dest: ret,
                    val: Value::Int(str::parse(val).map_err(|_| {
                        IRError::CouldNotParse(format!("Could not get int value from {val}"))
                    })?),
                    ty: Ty::Int,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok((ret.into(), Ty::Int))
            }
            TypedExprKind::LiteralFloat(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::Constant {
                    dest: ret,
                    val: Value::Float(str::parse(val).map_err(|_| {
                        IRError::CouldNotParse(format!("Could not get float value from {val}"))
                    })?),
                    ty: Ty::Float,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok((ret.into(), Ty::Float))
            }
            TypedExprKind::LiteralTrue => {
                if let Bind::Assigned(reg) = bind {
                    self.push_instr(Instruction::Constant {
                        dest: reg,
                        ty: Ty::Bool,
                        val: Value::Bool(true),
                        meta: vec![InstructionMeta::Source(expr.id)].into(),
                    });
                    Ok((reg.into(), Ty::Bool))
                } else {
                    Ok((Value::Bool(true), Ty::Bool))
                }
            }
            TypedExprKind::LiteralFalse => {
                if let Bind::Assigned(reg) = bind {
                    self.push_instr(Instruction::Constant {
                        dest: reg,
                        ty: Ty::Bool,
                        val: Value::Bool(false),
                        meta: vec![InstructionMeta::Source(expr.id)].into(),
                    });
                    Ok((reg.into(), Ty::Bool))
                } else {
                    Ok((Value::Bool(false), Ty::Bool))
                }
            }
            TypedExprKind::LiteralString(val) => self.lower_string(expr, val, bind),
            TypedExprKind::Tuple(typed_exprs) => self.lower_tuple(expr.id, typed_exprs, bind),
            TypedExprKind::Block(typed_block) => self.lower_block(typed_block, bind),
            TypedExprKind::Call {
                callee,
                args,
                callee_sym,
                ..
            } => self.lower_call(expr, callee, args, callee_sym.as_ref(), bind),
            TypedExprKind::Member {
                receiver, label, ..
            } => self.lower_member(expr, &Some(receiver.clone()), label, None, bind),

            TypedExprKind::Func(typed_func) => {
                self.lower_func(typed_func, bind, FuncTermination::Return)
            }
            TypedExprKind::Variable(symbol) => {
                let (value, ty) = self.lower_variable(symbol, expr)?;
                if let Bind::Assigned(reg) = bind {
                    if !matches!(value, Value::Reg(src) if src == reg.0) {
                        self.push_instr(Instruction::Constant {
                            dest: reg,
                            val: value,
                            ty: ty.clone(),
                            meta: vec![InstructionMeta::Source(expr.id)].into(),
                        });
                    }
                    Ok((Value::Reg(reg.0), ty))
                } else {
                    Ok((value, ty))
                }
            }
            TypedExprKind::Constructor(symbol, _items) => {
                self.lower_constructor(symbol, expr, bind)
            }
            TypedExprKind::If(cond, conseq, alt) => self.lower_if_expr(cond, conseq, alt, bind),
            TypedExprKind::Match(scrutinee, arms) => self.lower_match(expr, scrutinee, arms, bind),
            TypedExprKind::RecordLiteral { fields } => {
                self.lower_record_literal(expr, fields, bind)
            }
            TypedExprKind::Choice { dimension, .. } => {
                // Choice nodes should be resolved before lowering.
                // If we reach here, resolution failed.
                Err(IRError::TypeNotFound(format!(
                    "Unresolved choice at dimension {:?}",
                    dimension
                )))
            }
        }?;

        // Quick check to make sure types are right
        #[cfg(feature = "verify_ir")]
        if let Ok(expected_ty) = self.ty_from_id(&expr.id) {
            assert_eq!(
                ty,
                expected_ty,
                "type mismatch {:?}",
                formatter::format_node(&expr.into(), &self.asts[expr.id.0.0 as usize].meta)
            );
        }

        Ok((value, ty))
    }

    fn lower_effect_handler(
        &mut self,
        _id: NodeID,
        func: &TypedFunc,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let (_val, _) = self.lower_func(func, bind, FuncTermination::Continuation(func.name))?;
        Ok((Value::Void, Ty::Void))
    }

    fn lower_effect_call(
        &mut self,
        expr: &TypedExpr,
        effect: &Symbol,
        args: &[TypedExpr],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        // Check if we're in state machine mode
        if self.state_machine_context.is_some() {
            return self.lower_effect_call_state_machine(expr, effect, args, bind);
        }

        // Original closure-based implementation
        self.lower_effect_call_closure(expr, effect, args, bind)
    }

    /// Lower an effect call using the closure-based continuation approach (original behavior)
    fn lower_effect_call_closure(
        &mut self,
        expr: &TypedExpr,
        _effect: &Symbol,
        args: &[TypedExpr],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let mut arg_vals = Vec::with_capacity(args.len());
        for arg in args {
            let (val, _ty) = self.lower_expr(arg, Bind::Fresh)?;
            arg_vals.push(val);
        }

        let dest = self.ret(bind);

        let Some(handler_sym) = self
            .typed
            .resolved_names
            .effect_handlers
            .get(&expr.id)
            .copied()
        else {
            return Err(IRError::TypeNotFound(format!(
                "No handler found for {:?}",
                expr
            )));
        };

        let mut env = vec![];
        let mut env_ty = vec![];
        let mut new_bindings = Vec::with_capacity(self.current_func().bindings.len());
        for binding in self.current_func().bindings.clone() {
            env.push(self.get_binding(&binding.0).into());

            let ty = self.ty_from_symbol(&binding.0)?;
            env_ty.push(ty.clone());
            // Rebind to capture going forward
            new_bindings.push((
                binding.0,
                Binding::Continued {
                    index: new_bindings.len(),
                    ty,
                },
            ));
        }

        let continuation_sym =
            Symbol::Synthesized(self.typed.symbols.next_synthesized(self.config.module_id));
        let closure = Value::Closure {
            func: continuation_sym,
            env: env.into(),
        };

        let closure_reg = self.next_register();
        self.push_instr(Instruction::Ref {
            dest: closure_reg,
            ty: Ty::Tuple(env_ty),
            val: closure,
        });

        // Pass the continutation closure. It doesn't show up in the type signature. It's probably fine.
        arg_vals.insert(0, closure_reg.into());

        self.push_instr(Instruction::Call {
            dest,
            ty: self.ty_from_symbol(&handler_sym)?,
            callee: Value::Func(handler_sym),
            args: arg_vals.into(),
            self_dest: None,
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        // Get the parent function name for tracking
        let parent_name = self.current_func().symbol;

        // Create continuation and add to pending list (NOT the stack)
        let mut continuation = CurrentFunction::new(continuation_sym);
        // Burn the first register - it will be the env parameter
        continuation.registers.next();
        // Burn the second register - it will be the resumed value parameter
        let resumed_value_reg = continuation.registers.next();
        continuation.bindings.extend(new_bindings);

        self.pending_continuations
            .push((continuation, parent_name, dest));
        self.current_continuation_idx = Some(self.pending_continuations.len() - 1);

        // Return the continuation's resumed value register, not the parent's dest
        Ok((Value::Reg(resumed_value_reg.0), expr.ty.clone()))
    }

    /// Lower an effect call in state machine mode.
    /// Instead of creating a closure continuation, we:
    /// 1. Build the state_data record with live variables
    /// 2. Return (next_state, state_data, Pending(effect, args))
    fn lower_effect_call_state_machine(
        &mut self,
        expr: &TypedExpr,
        _effect: &Symbol,
        args: &[TypedExpr],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        // Lower effect arguments
        let mut arg_vals = Vec::with_capacity(args.len());
        for arg in args {
            let (val, _ty) = self.lower_expr(arg, Bind::Fresh)?;
            arg_vals.push(val);
        }

        // Get the yield point info for this expression
        let yield_point_idx = self
            .state_machine_context
            .as_ref()
            .and_then(|ctx| ctx.analysis.yield_point_for_expr(expr.id))
            .ok_or_else(|| {
                IRError::TypeNotFound(format!(
                    "No yield point found for effect call {:?}",
                    expr.id
                ))
            })?;

        let (next_state, live_vars) = {
            let ctx = self
                .state_machine_context
                .as_ref()
                .expect("did not get state machine context");
            let yield_point = &ctx.analysis.yield_points[yield_point_idx];
            (yield_point.resume_state, yield_point.live_vars.clone())
        };

        // Build state_data as a RawPtr. When live_vars is empty, use a null pointer.
        // When non-empty, store the record to memory and return the pointer.
        let state_data_reg = if live_vars.is_empty() {
            let reg = self.next_register();
            self.push_instr(Instruction::Constant {
                dest: reg,
                val: Value::Int(0),
                ty: Ty::RawPtr,
                meta: Default::default(),
            });
            reg
        } else {
            let mut state_data_fields = Vec::with_capacity(live_vars.len());
            for (sym, _ty) in &live_vars {
                let reg = self.get_binding(sym);
                state_data_fields.push(reg.into());
            }

            let record_ty = Ty::Record(
                None,
                live_vars
                    .iter()
                    .enumerate()
                    .fold(Row::Empty, |row, (i, (_, ty))| Row::Extend {
                        row: row.into(),
                        label: Label::Positional(i),
                        ty: ty.clone(),
                    })
                    .into(),
            );

            let record_reg = self.next_register();
            self.push_instr(Instruction::Record {
                dest: record_reg,
                ty: record_ty.clone(),
                record: state_data_fields.into(),
                meta: Default::default(),
            });

            let addr_reg = self.next_register();
            self.push_instr(Instruction::Alloc {
                dest: addr_reg,
                ty: record_ty.clone(),
                count: Value::Int(1),
            });
            self.push_instr(Instruction::Store {
                value: record_reg.into(),
                ty: record_ty,
                addr: addr_reg.into(),
            });

            addr_reg
        };

        // Build the next state value
        let next_state_reg = self.next_register();
        self.push_instr(Instruction::Constant {
            dest: next_state_reg,
            val: Value::Int(next_state as i64),
            ty: Ty::Int,
            meta: Default::default(),
        });

        // Build the effect args tuple
        let effect_args_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: effect_args_reg,
            ty: Ty::Tuple(args.iter().map(|a| a.ty.clone()).collect()),
            record: arg_vals.into(),
            meta: Default::default(),
        });

        // Build the Pending result: (effect_symbol, args)
        // For now, we'll use a simple record to represent this
        // In a full implementation, this would be a proper Poll::Pending enum variant
        let pending_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: pending_reg,
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr]), // Simplified
            record: vec![
                Value::Int(0), // 0 = Pending tag
                effect_args_reg.into(),
            ]
            .into(),
            meta: Default::default(),
        });

        // Return tuple: (next_state, state_data, Pending)
        let return_tuple_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: return_tuple_reg,
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr, expr.ty.clone()]),
            record: vec![
                next_state_reg.into(),
                state_data_reg.into(),
                pending_reg.into(),
            ]
            .into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        // Emit return terminator with the pending result
        self.push_terminator(Terminator::Ret {
            val: return_tuple_reg.into(),
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr, expr.ty.clone()]),
        });

        // Update state machine context for next state
        if let Some(ref mut ctx) = self.state_machine_context {
            ctx.current_state = next_state;
        }

        // Create a new basic block for the continuation (code after the effect call)
        let continuation_block = self.new_basic_block();
        self.set_current_block(continuation_block);

        // Record this continuation block as the entry for the next state
        if let Some(ref mut ctx) = self.state_machine_context {
            ctx.state_entries.push(continuation_block);
        }

        // In the continuation, the resumed value comes from the resumed_var parameter
        // We need to restore live variables from state_data
        let context = self
            .state_machine_context
            .as_ref()
            .expect("didn't get state machine context");
        let resumed_var = context.resumed_var;
        let state_data = context.state_data;

        // Restore live variables from state_data (which is a RawPtr)
        if !live_vars.is_empty() {
            let record_ty = Ty::Record(
                None,
                live_vars
                    .iter()
                    .enumerate()
                    .fold(Row::Empty, |row, (i, (_, ty))| Row::Extend {
                        row: row.into(),
                        label: Label::Positional(i),
                        ty: ty.clone(),
                    })
                    .into(),
            );

            let loaded_reg = self.next_register();
            self.push_instr(Instruction::Load {
                dest: loaded_reg,
                ty: record_ty,
                addr: state_data.into(),
            });

            for (i, (sym, ty)) in live_vars.iter().enumerate() {
                let dest = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record: loaded_reg,
                    field: Label::Positional(i),
                    meta: Default::default(),
                });
                self.insert_binding(*sym, Binding::Register(dest.0));
            }
        }

        // The effect call result comes from the resumed value
        let dest = self.ret(bind);
        self.push_instr(Instruction::Constant {
            dest,
            val: Value::Reg(resumed_var.0),
            ty: expr.ty.clone(),
            meta: Default::default(),
        });

        Ok((dest.into(), expr.ty.clone()))
    }

    /// Lower a yield builtin call.
    /// In state machine mode, this saves state and returns Poll::pending.
    /// Outside state machine mode, this is an error (yield should only be used in functions
    /// that compile to state machines).
    fn lower_yield_call(
        &mut self,
        expr: &TypedExpr,
        args: &[TypedExpr],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        // yield should only be called inside a function that compiles to a state machine
        if self.state_machine_context.is_none() {
            return Err(IRError::TypeNotFound(
                "yield can only be called inside a function that compiles to a state machine"
                    .into(),
            ));
        }

        // Lower the yielded value (first argument)
        let yielded_value = if !args.is_empty() {
            let (val, _ty) = self.lower_expr(&args[0], Bind::Fresh)?;
            val
        } else {
            Value::Void
        };

        // Get the yield point info for this expression
        let yield_point_idx = self
            .state_machine_context
            .as_ref()
            .and_then(|ctx| ctx.analysis.yield_point_for_expr(expr.id))
            .ok_or_else(|| {
                IRError::TypeNotFound(format!("No yield point found for yield call {:?}", expr.id))
            })?;

        let (next_state, live_vars) = {
            let ctx = self
                .state_machine_context
                .as_ref()
                .expect("state machine context");
            let yield_point = &ctx.analysis.yield_points[yield_point_idx];
            (yield_point.resume_state, yield_point.live_vars.clone())
        };

        // Build state_data as a RawPtr. When live_vars is empty, use a null pointer.
        // When non-empty, store the record to memory and return the pointer.
        let state_data_reg = if live_vars.is_empty() {
            let reg = self.next_register();
            self.push_instr(Instruction::Constant {
                dest: reg,
                val: Value::Int(0),
                ty: Ty::RawPtr,
                meta: Default::default(),
            });
            reg
        } else {
            let mut state_data_fields = Vec::with_capacity(live_vars.len());
            for (sym, _ty) in &live_vars {
                let reg = self.get_binding(sym);
                state_data_fields.push(reg.into());
            }

            let record_ty = Ty::Record(
                None,
                live_vars
                    .iter()
                    .enumerate()
                    .fold(Row::Empty, |row, (i, (_, ty))| Row::Extend {
                        row: row.into(),
                        label: Label::Positional(i),
                        ty: ty.clone(),
                    })
                    .into(),
            );

            let record_reg = self.next_register();
            self.push_instr(Instruction::Record {
                dest: record_reg,
                ty: record_ty.clone(),
                record: state_data_fields.into(),
                meta: Default::default(),
            });

            let addr_reg = self.next_register();
            self.push_instr(Instruction::Alloc {
                dest: addr_reg,
                ty: record_ty.clone(),
                count: Value::Int(1),
            });
            self.push_instr(Instruction::Store {
                value: record_reg.into(),
                ty: record_ty,
                addr: addr_reg.into(),
            });

            addr_reg
        };

        // Build the next state value
        let next_state_reg = self.next_register();
        self.push_instr(Instruction::Constant {
            dest: next_state_reg,
            val: Value::Int(next_state as i64),
            ty: Ty::Int,
            meta: Default::default(),
        });

        // Build GeneratorState::yielded(value)
        // Using structural representation: (tag: Int, value: Y) where 0 = yielded, 1 = done
        // yielded = Record(0, yielded_value) where 0 = yielded tag
        let yielded_ty = args.first().map(|a| a.ty.clone()).unwrap_or(Ty::Void);
        let generator_state_ty = Ty::Tuple(vec![Ty::Int, yielded_ty.clone()]);
        let yielded_state_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: yielded_state_reg,
            ty: generator_state_ty.clone(),
            record: vec![
                Value::Int(0), // 0 = yielded tag
                yielded_value,
            ]
            .into(),
            meta: Default::default(),
        });

        // Return tuple: (next_state, state_data, GeneratorState::yielded(value))
        let return_tuple_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: return_tuple_reg,
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr, generator_state_ty.clone()]),
            record: vec![
                next_state_reg.into(),
                state_data_reg.into(),
                yielded_state_reg.into(),
            ]
            .into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        // Emit return terminator with the yielded result
        self.push_terminator(Terminator::Ret {
            val: return_tuple_reg.into(),
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr, generator_state_ty]),
        });

        // Update state machine context for next state
        if let Some(ref mut ctx) = self.state_machine_context {
            ctx.current_state = next_state;
        }

        // Create a new basic block for the continuation (code after the yield)
        let continuation_block = self.new_basic_block();
        self.set_current_block(continuation_block);

        // Record this continuation block as the entry for the next state
        if let Some(ref mut ctx) = self.state_machine_context {
            ctx.state_entries.push(continuation_block);
        }

        // In the continuation, the resumed value comes from the resumed_var parameter
        let resumed_var = self
            .state_machine_context
            .as_ref()
            .expect("state machine context")
            .resumed_var;
        let state_data = self
            .state_machine_context
            .as_ref()
            .expect("state machine context")
            .state_data;

        // Restore live variables from state_data (which is a RawPtr)
        if !live_vars.is_empty() {
            let record_ty = Ty::Record(
                None,
                live_vars
                    .iter()
                    .enumerate()
                    .fold(Row::Empty, |row, (i, (_, ty))| Row::Extend {
                        row: row.into(),
                        label: Label::Positional(i),
                        ty: ty.clone(),
                    })
                    .into(),
            );

            let loaded_reg = self.next_register();
            self.push_instr(Instruction::Load {
                dest: loaded_reg,
                ty: record_ty,
                addr: state_data.into(),
            });

            for (i, (sym, ty)) in live_vars.iter().enumerate() {
                let dest = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record: loaded_reg,
                    field: Label::Positional(i),
                    meta: Default::default(),
                });
                self.insert_binding(*sym, Binding::Register(dest.0));
            }
        }

        // The yield call result comes from the resumed value
        let dest = self.ret(bind);
        self.push_instr(Instruction::Constant {
            dest,
            val: Value::Reg(resumed_var.0),
            ty: expr.ty.clone(),
            meta: Default::default(),
        });

        Ok((dest.into(), expr.ty.clone()))
    }

    #[allow(clippy::todo)]
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_inline_ir(
        &mut self,
        instr: &TypedInlineIRInstruction,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let binds: Vec<_> = instr
            .binds
            .iter()
            .map(|b| self.lower_expr(b, Bind::Fresh).map(|b| b.0))
            .try_collect()?;
        match &instr.kind {
            InlineIRInstructionKind::Constant { dest, ty, val } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty);
                let val = self.parsed_value(val, &binds);
                self.push_instr(Instruction::Constant {
                    dest,
                    ty: ty.clone(),
                    val,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Cmp {
                dest,
                lhs,
                rhs,
                ty,
                op,
            } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty);
                let lhs = self.parsed_value(lhs, &binds);
                let rhs = self.parsed_value(rhs, &binds);
                self.push_instr(Instruction::Cmp {
                    dest,
                    ty: ty.clone(),
                    lhs,
                    rhs,
                    op: (*op).into(),
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Add { dest, ty, a, b }
            | InlineIRInstructionKind::Sub { dest, ty, a, b }
            | InlineIRInstructionKind::Mul { dest, ty, a, b }
            | InlineIRInstructionKind::Div { dest, ty, a, b } => {
                let ty = self.parsed_ty(ty);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let a = self.parsed_value(a, &binds);
                let b = self.parsed_value(b, &binds);

                match &instr.kind {
                    InlineIRInstructionKind::Add { .. } => self.push_instr(Instruction::Add {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    InlineIRInstructionKind::Sub { .. } => self.push_instr(Instruction::Sub {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    InlineIRInstructionKind::Mul { .. } => self.push_instr(Instruction::Mul {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    InlineIRInstructionKind::Div { .. } => self.push_instr(Instruction::Div {
                        dest,
                        ty: ty.clone(),
                        a,
                        b,
                        meta: vec![InstructionMeta::Source(instr.id)].into(),
                    }),
                    _ => unreachable!(),
                }

                Ok((dest.into(), ty))
            }

            InlineIRInstructionKind::Ref { dest, ty, val } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty);
                let val = self.parsed_value(val, &binds);
                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val,
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Call {
                dest,
                ty,
                callee,
                args,
            } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty);
                let callee = self.parsed_value(callee, &binds);
                let args = args
                    .iter()
                    .map(|a| self.parsed_value(a, &binds))
                    .collect_vec()
                    .into();
                self.push_instr(Instruction::Call {
                    dest,
                    ty: ty.clone(),
                    callee,
                    args,
                    self_dest: None,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Record { dest, ty, record } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty);
                let record = record
                    .iter()
                    .map(|a| self.parsed_value(a, &binds))
                    .collect_vec()
                    .into();

                self.push_instr(Instruction::Record {
                    dest,
                    ty: ty.clone(),
                    record,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::GetField {
                dest,
                ty,
                record,
                field,
            } => {
                let ty = self.parsed_ty(ty);
                let record = self.parsed_register(record, Register::DROP);
                let Value::Int(pos) = self.parsed_value(field, &binds) else {
                    unreachable!("field must be an int");
                };
                let field = Label::Positional(pos as usize);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record,
                    field,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::SetField {
                dest,
                val,
                ty,
                record,
                field,
            } => {
                let ty = self.parsed_ty(ty);
                let val = self.parsed_value(val, &binds);
                let record = self.parsed_register(record, Register::DROP);
                let Value::Int(pos) = self.parsed_value(field, &binds) else {
                    unreachable!("field must be an int");
                };
                let field = Label::Positional(pos as usize);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::SetField {
                    dest,
                    val,
                    ty: ty.clone(),
                    record,
                    field: field.clone(),
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::_Print { val } => {
                let val = self.parsed_value(val, &binds);
                self.push_instr(Instruction::_Print { val });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Alloc { dest, ty, count } => {
                let ty = self.parsed_ty(ty);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let count = self.parsed_value(count, &binds);
                self.push_instr(Instruction::Alloc {
                    dest,
                    ty: ty.clone(),
                    count,
                });
                Ok((dest.into(), Ty::RawPtr))
            }
            InlineIRInstructionKind::Free { addr } => {
                let addr = self.parsed_value(addr, &binds);
                self.push_instr(Instruction::Free { addr });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Load { dest, ty, addr } => {
                let ty = self.parsed_ty(ty);
                let addr = self.parsed_value(addr, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::Load {
                    dest,
                    ty: ty.clone(),
                    addr,
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Store { value, ty, addr } => {
                let ty = self.parsed_ty(ty);
                let value = self.parsed_value(value, &binds);
                let addr = self.parsed_value(addr, &binds);
                self.push_instr(Instruction::Store {
                    value,
                    ty: ty.clone(),
                    addr,
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Move { from, ty, to } => {
                let ty = self.parsed_ty(ty);
                let from = self.parsed_value(from, &binds);
                let to = self.parsed_value(to, &binds);
                self.push_instr(Instruction::Move {
                    ty: ty.clone(),
                    from,
                    to,
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Copy {
                ty,
                from,
                to,
                length,
            } => {
                let ty = self.parsed_ty(ty);
                let from = self.parsed_value(from, &binds);
                let to = self.parsed_value(to, &binds);
                let length = self.parsed_value(length, &binds);
                self.push_instr(Instruction::Copy {
                    ty: ty.clone(),
                    from,
                    to,
                    length,
                });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Gep {
                dest,
                ty,
                addr,
                offset_index,
            } => {
                let ty = self.parsed_ty(ty);
                let addr = self.parsed_value(addr, &binds);
                let offset_index = self.parsed_value(offset_index, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::Gep {
                    dest,
                    ty: ty.clone(),
                    addr,
                    offset_index,
                });
                Ok((dest.into(), Ty::RawPtr))
            }
            // I/O Instructions
            InlineIRInstructionKind::IoOpen {
                dest,
                path,
                flags,
                mode,
            } => {
                let path = self.parsed_value(path, &binds);
                let flags = self.parsed_value(flags, &binds);
                let mode = self.parsed_value(mode, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoOpen {
                    dest,
                    path,
                    flags,
                    mode,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoRead {
                dest,
                fd,
                buf,
                count,
            } => {
                let fd = self.parsed_value(fd, &binds);
                let buf = self.parsed_value(buf, &binds);
                let count = self.parsed_value(count, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoRead {
                    dest,
                    fd,
                    buf,
                    count,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoWrite {
                dest,
                fd,
                buf,
                count,
            } => {
                let fd = self.parsed_value(fd, &binds);
                let buf = self.parsed_value(buf, &binds);
                let count = self.parsed_value(count, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoWrite {
                    dest,
                    fd,
                    buf,
                    count,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoClose { dest, fd } => {
                let fd = self.parsed_value(fd, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoClose { dest, fd });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoCtl { dest, fd, op, arg } => {
                let fd = self.parsed_value(fd, &binds);
                let op = self.parsed_value(op, &binds);
                let arg = self.parsed_value(arg, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoCtl { dest, fd, op, arg });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoPoll {
                dest,
                fds,
                count,
                timeout,
            } => {
                let fds = self.parsed_value(fds, &binds);
                let count = self.parsed_value(count, &binds);
                let timeout = self.parsed_value(timeout, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoPoll {
                    dest,
                    fds,
                    count,
                    timeout,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoSocket {
                dest,
                domain,
                socktype,
                protocol,
            } => {
                let domain = self.parsed_value(domain, &binds);
                let socktype = self.parsed_value(socktype, &binds);
                let protocol = self.parsed_value(protocol, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoSocket {
                    dest,
                    domain,
                    socktype,
                    protocol,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoBind {
                dest,
                fd,
                addr,
                port,
            } => {
                let fd = self.parsed_value(fd, &binds);
                let addr = self.parsed_value(addr, &binds);
                let port = self.parsed_value(port, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoBind {
                    dest,
                    fd,
                    addr,
                    port,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoListen { dest, fd, backlog } => {
                let fd = self.parsed_value(fd, &binds);
                let backlog = self.parsed_value(backlog, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoListen { dest, fd, backlog });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoConnect {
                dest,
                fd,
                addr,
                port,
            } => {
                let fd = self.parsed_value(fd, &binds);
                let addr = self.parsed_value(addr, &binds);
                let port = self.parsed_value(port, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoConnect {
                    dest,
                    fd,
                    addr,
                    port,
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoAccept { dest, fd } => {
                let fd = self.parsed_value(fd, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoAccept { dest, fd });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IoSleep { dest, ms } => {
                let ms = self.parsed_value(ms, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IoSleep { dest, ms });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::Trunc { dest, val } => {
                let val = self.parsed_value(val, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::Trunc {
                    dest,
                    val,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), Ty::Int))
            }
            InlineIRInstructionKind::IntToFloat { dest, val } => {
                let val = self.parsed_value(val, &binds);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                self.push_instr(Instruction::IntToFloat {
                    dest,
                    val,
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), Ty::Float))
            }
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, items))]
    fn lower_array(
        &mut self,
        expr: &TypedExpr,
        items: &[TypedExpr],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let item_irs: Vec<(Value, Ty)> = items
            .iter()
            .map(|item| self.lower_expr(item, Bind::Fresh))
            .try_collect()?;

        let (item_irs, item_tys): (Vec<Value>, Vec<Ty>) = item_irs.into_iter().unzip();
        let item_ty = if let Some(item) = items.first() {
            item.ty.clone()
        } else {
            Ty::Void
        };

        let record_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: record_reg,
            ty: Ty::Tuple(item_tys.clone()), // This is sort of a hack, it's really a record but it's a pain to wrap a row and this still lowers to IrTy::Record
            record: item_irs.into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        let alloc_reg = self.next_register();
        self.push_instr(Instruction::Alloc {
            dest: alloc_reg,
            ty: Ty::Tuple(item_tys.clone()),
            count: Value::Int(1),
        });

        self.push_instr(Instruction::Store {
            value: record_reg.into(),
            ty: Ty::Tuple(item_tys),
            addr: alloc_reg.into(),
        });

        let dest = self.ret(bind);
        self.push_instr(Instruction::Nominal {
            dest,
            sym: Symbol::Array,
            ty: Ty::Array(item_ty.clone()),
            record: vec![
                alloc_reg.into(),
                Value::Int(items.len() as i64),
                Value::Int(items.len() as i64),
            ]
            .into(),
            meta: vec![
                InstructionMeta::Source(expr.id),
                InstructionMeta::RecordId(RecordId::Nominal(Symbol::Array)),
            ]
            .into(),
        });

        Ok((dest.into(), Ty::Array(item_ty)))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, items))]
    fn lower_tuple(
        &mut self,
        id: NodeID,
        items: &[TypedExpr],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let item_irs: Vec<(Value, Ty)> = items
            .iter()
            .map(|expr| self.lower_expr(expr, Bind::Fresh))
            .try_collect()?;

        let (item_irs, item_tys): (Vec<Value>, Vec<Ty>) = item_irs.into_iter().unzip();
        let ty = Ty::Tuple(item_tys);
        let dest = self.ret(bind);
        self.push_instr(Instruction::Record {
            dest,
            ty: ty.clone(),
            record: item_irs.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_string(
        &mut self,
        expr: &TypedExpr,
        string: &String,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let ret = self.ret(bind);
        let unescaped = crate::parsing::lexing::unescape(string);
        let bytes = unescaped.bytes().collect_vec();
        let bytes_len = bytes.len() as i64;
        let ptr = self.static_memory.write(Value::RawBuffer(bytes));

        self.push_instr(Instruction::Nominal {
            dest: ret,
            sym: Symbol::String,
            ty: Ty::String(),
            record: vec![
                Value::RawPtr(Addr(ptr)),
                Value::Int(bytes_len),
                Value::Int(bytes_len),
            ]
            .into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
        });

        Ok((ret.into(), Ty::String()))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_match(
        &mut self,
        expr: &TypedExpr,
        scrutinee: &TypedExpr,
        arms: &[TypedMatchArm],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let result_type = expr.ty.clone();
        let Some(plan) = self.typed.types.match_plans.get(&expr.id).cloned() else {
            self.lower_expr(scrutinee, Bind::Discard)?;
            return Ok((Value::Void, result_type));
        };
        let produce_value = !matches!(bind, Bind::Discard);
        let result_register = if produce_value {
            self.ret(bind)
        } else {
            Register::DROP
        };

        let scrutinee_register = self.next_register();
        self.lower_expr(scrutinee, Bind::Assigned(scrutinee_register))?;

        let (symbol_binds, value_regs) = {
            let value_regs = self.plan_value_registers(&plan, scrutinee_register);

            let mut symbol_binds: FxHashMap<Symbol, (ValueId, Ty)> = FxHashMap::default();
            for node in &plan.nodes {
                if let PlanNode::Arm { binds, .. } = node {
                    for (symbol, value_id) in binds {
                        symbol_binds.entry(*symbol).or_insert_with(|| {
                            (*value_id, self.plan_value_ty(&plan, *value_id).clone())
                        });
                    }
                }
            }

            (symbol_binds, value_regs)
        };

        for (symbol, (value_id, ty)) in &symbol_binds {
            if self.typed.resolved_names.captured.contains(symbol) {
                let addr = self.next_register();
                self.insert_binding(*symbol, Binding::Pointer(addr.into()));
            } else if let Some(reg) = value_regs.get(value_id).copied() {
                self.insert_binding(*symbol, reg.into());
            } else {
                self.ensure_match_binding(*symbol, ty.clone());
            }
        }

        let join_block_id = self.new_basic_block();

        let mut arm_block_ids = Vec::with_capacity(arms.len());
        let mut arm_result_values = Vec::with_capacity(arms.len());

        for arm in arms {
            let arm_block_id = self.new_basic_block();
            arm_block_ids.push(arm_block_id);

            self.in_basic_block(arm_block_id, |lowerer| {
                let arm_bind = if produce_value {
                    Bind::Fresh
                } else {
                    Bind::Discard
                };
                let (arm_value, _arm_type) = lowerer.lower_block(&arm.body, arm_bind)?;
                if produce_value {
                    arm_result_values.push(arm_value);
                }

                lowerer.push_terminator(Terminator::Jump { to: join_block_id });
                Ok(())
            })?;
        }

        self.lower_match_plan(&plan, scrutinee_register, &arm_block_ids, &value_regs)?;

        self.set_current_block(join_block_id);

        if produce_value {
            self.push_phi(Phi {
                dest: result_register,
                ty: result_type.clone(),
                sources: arm_block_ids
                    .into_iter()
                    .zip(arm_result_values.into_iter())
                    .map(|(from_id, value)| PhiSource { from_id, value })
                    .collect::<Vec<PhiSource>>()
                    .into(),
            });

            Ok((Value::Reg(result_register.0), result_type))
        } else {
            Ok((Value::Void, result_type))
        }
    }

    fn lower_match_plan(
        &mut self,
        plan: &MatchPlan,
        scrutinee_register: Register,
        arm_block_ids: &[BasicBlockId],
        value_regs: &FxHashMap<ValueId, Register>,
    ) -> Result<(), IRError> {
        let root_block_id = self.current_block_id();
        let mut node_blocks = Vec::with_capacity(plan.nodes.len());
        for idx in 0..plan.nodes.len() {
            if idx == plan.root.0 {
                node_blocks.push(root_block_id);
            } else {
                node_blocks.push(self.new_basic_block());
            }
        }

        for (idx, node) in plan.nodes.iter().enumerate() {
            let block_id = node_blocks[idx];
            self.in_basic_block(block_id, |lowerer| {
                lowerer.emit_match_plan_node(
                    plan,
                    scrutinee_register,
                    node,
                    &node_blocks,
                    arm_block_ids,
                    value_regs,
                )
            })?;
        }

        Ok(())
    }

    fn emit_match_plan_node(
        &mut self,
        plan: &MatchPlan,
        scrutinee_register: Register,
        node: &PlanNode,
        node_blocks: &[BasicBlockId],
        arm_block_ids: &[BasicBlockId],
        value_regs: &FxHashMap<ValueId, Register>,
    ) -> Result<(), IRError> {
        match node {
            PlanNode::Fail => {
                self.push_terminator(Terminator::Unreachable);
            }
            PlanNode::Arm { arm_index, binds } => {
                for (symbol, value_id) in binds {
                    let (value, ty) =
                        self.plan_value(plan, *value_id, scrutinee_register, value_regs)?;
                    self.store_match_binding(*symbol, value, &ty)?;
                }
                let target = arm_block_ids[*arm_index];
                self.push_terminator(Terminator::Jump { to: target });
            }
            PlanNode::Switch {
                value,
                cases,
                default,
            } => {
                self.emit_match_switch(
                    plan,
                    scrutinee_register,
                    *value,
                    cases,
                    *default,
                    node_blocks,
                    value_regs,
                )?;
            }
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_match_switch(
        &mut self,
        plan: &MatchPlan,
        scrutinee_register: Register,
        value_id: ValueId,
        cases: &[crate::types::matcher::PlanCase],
        default: Option<PlanNodeId>,
        node_blocks: &[BasicBlockId],
        value_regs: &FxHashMap<ValueId, Register>,
    ) -> Result<(), IRError> {
        if cases.is_empty() {
            if let Some(default_id) = default {
                self.push_terminator(Terminator::Jump {
                    to: node_blocks[default_id.0],
                });
            } else {
                self.push_terminator(Terminator::Unreachable);
            }
            return Ok(());
        }

        let mut current_block_id = self.current_block_id();
        for (idx, case) in cases.iter().enumerate() {
            let is_last = idx + 1 == cases.len();
            let next_block_id = if is_last {
                if let Some(default_id) = default {
                    node_blocks[default_id.0]
                } else {
                    self.new_basic_block()
                }
            } else {
                self.new_basic_block()
            };
            let target_block_id = node_blocks[case.target.0];
            let ctor = &case.ctor;

            self.in_basic_block(current_block_id, |lowerer| {
                if matches!(ctor, Constructor::Tuple | Constructor::Record) {
                    lowerer.push_terminator(Terminator::Jump {
                        to: target_block_id,
                    });
                    return Ok(());
                }

                let cond_reg = lowerer.emit_match_condition(
                    plan,
                    scrutinee_register,
                    value_id,
                    ctor,
                    value_regs,
                )?;
                lowerer.push_terminator(Terminator::Branch {
                    cond: Value::Reg(cond_reg.0),
                    conseq: target_block_id,
                    alt: next_block_id,
                });
                Ok(())
            })?;

            if matches!(ctor, Constructor::Tuple | Constructor::Record) {
                return Ok(());
            }

            if is_last {
                if default.is_none() {
                    self.in_basic_block(next_block_id, |lowerer| {
                        lowerer.push_terminator(Terminator::Unreachable);
                        Ok(())
                    })?;
                }
                break;
            }

            current_block_id = next_block_id;
        }

        Ok(())
    }

    fn emit_match_condition(
        &mut self,
        plan: &MatchPlan,
        scrutinee_register: Register,
        value_id: ValueId,
        ctor: &Constructor,
        value_regs: &FxHashMap<ValueId, Register>,
    ) -> Result<Register, IRError> {
        let (value, value_ty) = self.plan_value(plan, value_id, scrutinee_register, value_regs)?;
        match ctor {
            Constructor::LiteralTrue => self.emit_eq_cmp(value, Value::Bool(true), Ty::Bool),
            Constructor::LiteralFalse => self.emit_eq_cmp(value, Value::Bool(false), Ty::Bool),
            Constructor::LiteralInt(text) => {
                let parsed = text.parse::<i64>().map_err(|error| {
                    IRError::InvalidAssignmentTarget(format!(
                        "invalid integer literal in match pattern: {text} ({error})"
                    ))
                })?;
                self.emit_eq_cmp(value, Value::Int(parsed), value_ty)
            }
            Constructor::LiteralFloat(text) => {
                let parsed = text.parse::<f64>().map_err(|error| {
                    IRError::InvalidAssignmentTarget(format!(
                        "invalid float literal in match pattern: {text} ({error})"
                    ))
                })?;
                self.emit_eq_cmp(value, Value::Float(parsed), value_ty)
            }
            Constructor::Variant(name) => {
                let Ty::Nominal { symbol, .. } = value_ty else {
                    return Err(IRError::TypeNotFound(format!(
                        "expected nominal type for variant match, got {value_ty:?}"
                    )));
                };
                let label = self.label_from_name(name);
                let tag = self.get_variant_tag(&symbol, &label)?;

                let record = value.as_register()?;
                let tag_reg = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest: tag_reg,
                    ty: Ty::Int,
                    record,
                    field: Label::Positional(0),
                    meta: vec![InstructionMeta::Source(NodeID::SYNTHESIZED)].into(),
                });
                self.emit_eq_cmp(Value::Reg(tag_reg.0), Value::Int(tag), Ty::Int)
            }
            Constructor::Tuple | Constructor::Record => Err(IRError::InvalidAssignmentTarget(
                "no condition for tuple/record constructor".into(),
            )),
        }
    }

    fn emit_eq_cmp(&mut self, lhs: Value, rhs: Value, ty: Ty) -> Result<Register, IRError> {
        let dest = self.next_register();
        self.push_instr(Instruction::Cmp {
            dest,
            lhs,
            rhs,
            ty,
            op: CmpOperator::Equals,
            meta: vec![InstructionMeta::Source(NodeID::SYNTHESIZED)].into(),
        });
        Ok(dest)
    }

    /// Gets the variant tag for an enum variant, looking up the original module's catalog
    /// for imported enums to ensure correct tag ordering.
    fn get_variant_tag(&self, enum_symbol: &Symbol, variant_name: &Label) -> Result<i64, IRError> {
        // First, try to get from the original module's catalog for imported enums
        if let Some(module_id) = enum_symbol.external_module_id()
            && let Some(module) = self.config.modules.get_module(module_id)
            && let Some(variants) = module.types.catalog.variants.get(enum_symbol)
            && let Some(tag) = variants.get_index_of(variant_name)
        {
            return Ok(tag as i64);
        }

        // Fall back to local catalog
        let variants = self
            .typed
            .types
            .catalog
            .variants
            .get(enum_symbol)
            .ok_or_else(|| {
                IRError::TypeNotFound(format!("missing enum variants for {enum_symbol:?}"))
            })?;

        let tag = variants.get_index_of(variant_name).ok_or_else(|| {
            IRError::TypeNotFound(format!(
                "missing enum variant {variant_name:?} on {enum_symbol:?}"
            ))
        })?;

        Ok(tag as i64)
    }

    fn plan_value_ty<'b>(&self, plan: &'b MatchPlan, value_id: ValueId) -> &'b Ty {
        match &plan.values[value_id.0] {
            ValueRef::Scrutinee { ty } => ty,
            ValueRef::Field { ty, .. } => ty,
        }
    }

    fn plan_value(
        &mut self,
        plan: &MatchPlan,
        value_id: ValueId,
        scrutinee_register: Register,
        value_regs: &FxHashMap<ValueId, Register>,
    ) -> Result<(Value, Ty), IRError> {
        match &plan.values[value_id.0] {
            ValueRef::Scrutinee { ty } => {
                let reg = value_regs
                    .get(&value_id)
                    .copied()
                    .unwrap_or(scrutinee_register);
                Ok((Value::Reg(reg.0), ty.clone()))
            }
            ValueRef::Field { base, proj, ty } => {
                let (base_value, base_ty) =
                    self.plan_value(plan, *base, scrutinee_register, value_regs)?;
                let record = base_value.as_register()?;
                let field = match proj {
                    Projection::Tuple(index) => Label::Positional(*index),
                    Projection::Record(label) => self.field_index(&base_ty, label),
                    Projection::VariantPayload(index) => Label::Positional(index + 1),
                };
                let dest = *value_regs.get(&value_id).ok_or_else(|| {
                    IRError::TypeNotFound(format!("missing register for {value_id:?}"))
                })?;
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record,
                    field,
                    meta: vec![InstructionMeta::Source(NodeID::SYNTHESIZED)].into(),
                });
                Ok((dest.into(), ty.clone()))
            }
        }
    }

    fn ensure_match_binding(&mut self, symbol: Symbol, _ty: Ty) {
        if self.current_func_mut().bindings.contains_key(&symbol) {
            return;
        }

        if self.typed.resolved_names.captured.contains(&symbol) {
            let addr = self.next_register();
            self.insert_binding(symbol, Binding::Pointer(addr.into()));
        } else {
            let reg = self.next_register();
            self.insert_binding(symbol, reg.into());
        }
    }

    fn store_match_binding(
        &mut self,
        symbol: Symbol,
        value: Value,
        ty: &Ty,
    ) -> Result<(), IRError> {
        let binding = self
            .current_func_mut()
            .bindings
            .get(&symbol)
            .cloned()
            .ok_or_else(|| IRError::TypeNotFound(format!("missing binding for {symbol:?}")))?;

        match binding {
            Binding::Register(reg) => {
                if matches!(value, Value::Reg(src) if src == reg) {
                    return Ok(());
                }

                self.push_instr(Instruction::Constant {
                    dest: Register(reg),
                    val: value,
                    ty: ty.clone(),
                    meta: vec![InstructionMeta::Source(NodeID::SYNTHESIZED)].into(),
                });
            }
            Binding::Pointer(addr) => {
                if let Value::Reg(reg) = addr {
                    self.push_instr(Instruction::Alloc {
                        dest: Register(reg),
                        ty: ty.clone(),
                        count: Value::Int(1),
                    });
                }
                self.push_instr(Instruction::Store {
                    value,
                    ty: ty.clone(),
                    addr,
                });
            }
            Binding::Capture { index, ty } => {
                let dest = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: Ty::RawPtr,
                    record: Register(0),
                    field: Label::Positional(index),
                    meta: vec![InstructionMeta::Source(NodeID::SYNTHESIZED)].into(),
                });
                self.push_instr(Instruction::Store {
                    value,
                    ty,
                    addr: dest.into(),
                });
            }
            Binding::Continued { index, ty } => {
                tracing::warn!("ignoring continued binding {index:?}, {ty:?}");
            }
        }

        Ok(())
    }

    fn plan_value_registers(
        &mut self,
        plan: &MatchPlan,
        scrutinee_register: Register,
    ) -> FxHashMap<ValueId, Register> {
        let mut value_regs = FxHashMap::default();
        for (idx, value) in plan.values.iter().enumerate() {
            let id = ValueId(idx);
            let reg = match value {
                ValueRef::Scrutinee { .. } => scrutinee_register,
                ValueRef::Field { .. } => self.next_register(),
            };
            value_regs.insert(id, reg);
        }
        value_regs
    }

    fn lower_record_literal(
        &mut self,
        expr: &TypedExpr,
        fields: &[TypedRecordField],
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let mut field_vals_by_label: FxHashMap<Label, (Value, Ty)> = FxHashMap::default();
        let mut field_labels = vec![];
        for field in fields.iter() {
            let (val, ty) = self.lower_expr(&field.value, Bind::Fresh)?;
            field_vals_by_label.insert(field.name.clone(), (val, ty));
            field_labels.push(field.name.to_string());
        }

        let record_id = RecordId::Record(self.next_record_id);
        self.next_record_id += 1;
        self.record_labels.insert(record_id, field_labels);

        let dest = self.ret(bind);

        let ty = expr.ty.clone();

        // Check if this record literal is typed as a nominal struct
        if let Ty::Nominal { symbol, type_args } = &ty {
            let nominal = self
                .lookup_nominal(symbol)
                .cloned()
                .unwrap_or_else(|| unreachable!("didn't get nominal: {symbol:?}"));
            let properties = nominal.substitute_properties(type_args);
            let record_vals = properties
                .keys()
                .map(|label| {
                    field_vals_by_label
                        .get(label)
                        .unwrap_or_else(|| unreachable!("missing record literal field {label:?}"))
                        .0
                        .clone()
                })
                .collect::<Vec<_>>();

            self.push_instr(Instruction::Nominal {
                dest,
                sym: *symbol,
                ty: ty.clone(),
                record: record_vals.into(),
                meta: vec![InstructionMeta::Source(expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        }

        let Ty::Record(_, row) = &ty else {
            return Err(IRError::TypeNotFound(format!(
                "expected record type for record literal, got: {ty:?}"
            )));
        };

        let record_vals = row
            .close()
            .keys()
            .map(|label| {
                field_vals_by_label
                    .get(label)
                    .unwrap_or_else(|| unreachable!("missing record literal field {label:?}"))
                    .0
                    .clone()
            })
            .collect::<Vec<_>>();

        self.push_instr(Instruction::Record {
            dest,
            ty: ty.clone(),
            record: record_vals.into(),
            meta: vec![
                InstructionMeta::Source(expr.id),
                InstructionMeta::RecordId(record_id),
            ]
            .into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_constructor(
        &mut self,
        name: &Symbol,
        expr: &TypedExpr,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let constructor_sym = *self
            .typed
            .types
            .catalog
            .initializers
            .get(name)
            .unwrap_or_else(|| unreachable!("did not get inits for {name:?}"))
            .get(&Label::Named("init".into()))
            .unwrap_or_else(|| unreachable!("did not get init for {name:?}"));

        let init_entry = self
            .typed
            .types
            .get_symbol(&constructor_sym)
            .cloned()
            .expect("did not get init entry");

        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty: init_entry.as_mono_ty().clone(),
            val: Value::Func(constructor_sym),
        });

        Ok((dest.into(), init_entry.as_mono_ty().clone()))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    #[allow(clippy::too_many_arguments)]
    fn lower_enum_constructor(
        &mut self,
        id: NodeID,
        enum_symbol: &Symbol,
        variant_name: &Label,
        arg_exprs: &[TypedExpr],
        mut args: Vec<Value>,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let constructor_sym = *self
            .typed
            .types
            .catalog
            .variants
            .get(enum_symbol)
            .unwrap_or_else(|| panic!("did not get variants for {enum_symbol:?}"))
            .get(variant_name)
            .unwrap_or_else(|| panic!("didn't get {:?}", enum_symbol));

        let tag = self.get_variant_tag(enum_symbol, variant_name)? as usize;

        let _enum_entry = self
            .typed
            .types
            .get_symbol(enum_symbol)
            .unwrap_or_else(|| panic!("did not get enum entry {enum_symbol:?}"))
            .clone();
        let _init_entry = self
            .typed
            .types
            .get_symbol(&constructor_sym)
            .cloned()
            .expect("did not get enum constructor entry");

        let mut args_tys: Vec<Ty> = vec![Ty::Int];
        for value in arg_exprs.iter() {
            args_tys.push(value.ty.clone());
        }

        // Set the tag as the first entry
        args.insert(0, Value::Int(tag as i64));

        let row = args_tys
            .iter()
            .enumerate()
            .fold(Row::Empty, |acc, (i, ty)| Row::Extend {
                row: acc.into(),
                label: Label::Positional(i),
                ty: ty.clone(),
            });

        let ty = Ty::Record(Some(*enum_symbol), row.into());
        let dest = self.ret(bind);
        self.push_instr(Instruction::Nominal {
            sym: *enum_symbol,
            dest,
            ty: ty.clone(),
            record: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, receiver))]
    #[allow(clippy::todo)]
    fn lower_member(
        &mut self,
        expr: &TypedExpr,
        receiver: &Option<Box<TypedExpr>>,
        label: &Label,
        witness: Option<Symbol>,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        if let Some(box receiver) = &receiver {
            if matches!(receiver.kind, TypedExprKind::Hole)
                && let Ty::Nominal { symbol, .. } = &expr.ty
                && self
                    .typed
                    .types
                    .catalog
                    .variants
                    .get(symbol)
                    .is_some_and(|variants| variants.contains_key(label))
            {
                return self.lower_enum_constructor(
                    expr.id,
                    symbol,
                    label,
                    Default::default(),
                    Default::default(),
                    bind,
                );
            }

            if let TypedExprKind::Constructor(name, ..) = &receiver.kind {
                return self.lower_enum_constructor(
                    receiver.id,
                    name,
                    label,
                    Default::default(),
                    Default::default(),
                    bind,
                );
            }

            let reg = self.next_register();
            let member_bind = Bind::Assigned(reg);
            let (receiver_val, _) = self.lower_expr(receiver, member_bind)?;
            let ty = expr.ty.clone();
            let dest = self.ret(bind);

            let receiver_ty = receiver.ty.clone();

            if let Ty::Nominal { symbol, .. } = &receiver_ty
                && let Some(method) = self.lookup_instance_method(symbol, label)
            {
                tracing::debug!("lowering method: {label} {method:?}");

                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val: Value::Func(method),
                });
            } else {
                let label = self.field_index(&receiver_ty, label);
                tracing::debug!("lowering field {label}");
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record: receiver_val.as_register()?,
                    field: label,
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
            };

            Ok((dest.into(), ty))
        } else {
            todo!("gotta handle unqualified lookups")
        }
    }

    /// Check if a symbol refers to a global constant (from external module or current module).
    fn is_global_constant(&self, sym: &Symbol) -> bool {
        self.config.modules.lookup_global_constant(sym).is_some()
            || self.typed.types.catalog.global_constants.contains_key(sym)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_variable(&mut self, name: &Symbol, expr: &TypedExpr) -> Result<(Value, Ty), IRError> {
        let ty = expr.ty.clone();
        // If we currently have a binding for this symbol, prefer that over just passing names around
        if self.current_func_mut().bindings.contains_key(name) {
            return Ok((self.get_binding(name).into(), ty));
        }

        // For synthesized symbols, check if the original symbol has a binding.
        // Only use it if no type specialization was applied (i.e., for non-generic functions).
        // For generic functions, we need to use the specialized Func directly.
        let specialized_callee = self.typed.specialized_callees.get(name);
        let original_symbol = specialized_callee.map(|s| s.original_symbol);
        if let Some(callee) = specialized_callee {
            // Only use original binding if no type specializations were applied
            if callee.specializations.ty.is_empty() {
                let original = callee.original_symbol;
                if self.current_func_mut().bindings.contains_key(&original) {
                    return Ok((self.get_binding(&original).into(), ty));
                }
            }
        }

        // Get the lookup name for captures (use original if this is a synthesized symbol)
        let capture_lookup_name = original_symbol.as_ref().unwrap_or(name);

        let ret = if matches!(ty, Ty::Func(..)) {
            // Check if this function has captures
            if let Some(captures) = self
                .typed
                .resolved_names
                .captures
                .get(capture_lookup_name)
                .cloned()
                && !captures.is_empty()
            {
                let env: Vec<Value> = captures
                    .iter()
                    .filter_map(|cap| {
                        // Global functions and constants are resolved by symbol/inline;
                        // don't treat them as captured env fields.
                        // This matches the logic in lower_func.
                        let cap_ty = self.ty_from_symbol(&cap.symbol).ok()?;
                        let is_handler = self
                            .typed
                            .resolved_names
                            .handler_symbols
                            .contains(&cap.symbol);
                        if matches!(cap.symbol, Symbol::Global(_)) && !is_handler {
                            if matches!(cap_ty, Ty::Func(..) | Ty::Constructor { .. }) {
                                return None;
                            }
                            if self.is_global_constant(&cap.symbol)
                                && !self
                                    .typed
                                    .resolved_names
                                    .mutated_symbols
                                    .contains(&cap.symbol)
                            {
                                return None;
                            }
                        }

                        Some(
                            match self.current_func_mut().bindings.get(&cap.symbol).cloned() {
                                Some(Binding::Pointer(addr)) => addr,
                                Some(Binding::Register(reg)) => Value::Reg(reg),
                                Some(Binding::Capture { index, ty }) => {
                                    let dest = self.next_register();
                                    self.push_instr(Instruction::GetField {
                                        dest,
                                        ty,
                                        record: Register(0),
                                        field: Label::Positional(index),
                                        meta: vec![].into(),
                                    });
                                    dest.into()
                                }
                                other => panic!("unexpected binding for capture: {other:?}"),
                            },
                        )
                    })
                    .collect();
                if env.is_empty() {
                    Value::Func(*name)
                } else {
                    Value::Closure {
                        func: *name,
                        env: env.into(),
                    }
                }
            } else {
                Value::Func(*name)
            }
        } else {
            // Check for global constant (external module or current module)
            let global_constant = name
                .external_module_id()
                .and_then(|_| self.config.modules.lookup_global_constant(name).cloned())
                .or_else(|| self.typed.types.catalog.global_constants.get(name).cloned());
            if let Some(constant) = global_constant {
                let dest = self.next_register();
                let val = match &constant {
                    crate::types::type_catalog::GlobalConstant::Int(i) => Value::Int(*i),
                    crate::types::type_catalog::GlobalConstant::Float(f) => Value::Float(*f),
                    crate::types::type_catalog::GlobalConstant::Bool(b) => Value::Bool(*b),
                };
                self.push_instr(Instruction::Constant {
                    dest,
                    ty: ty.clone(),
                    val,
                    meta: vec![].into(),
                });
                return Ok((dest.into(), ty));
            }
            if name.external_module_id().is_some() {
                // External non-constant symbols are functions whose type may not
                // have resolved to Ty::Func (e.g. stored as a type parameter).
                return Ok((Value::Func(*name), ty));
            }
            Value::Reg(self.get_binding(name).0)
        };

        Ok((ret, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    #[allow(clippy::too_many_arguments)]
    fn lower_constructor_call(
        &mut self,
        id: NodeID,
        name: &Symbol,
        callee: &TypedExpr,
        mut args: Vec<Value>,
        dest: Register,
        callee_sym: Option<Symbol>,
    ) -> Result<(Value, Ty), IRError> {
        let record_dest = self.next_register();

        // Look up the initializer - use provided callee_sym (specialized) if available
        let init_sym = callee_sym.unwrap_or_else(|| {
            self.typed
                .types
                .catalog
                .initializers
                .get(name)
                .unwrap_or_else(|| panic!("didn't get initializers for {name:?}"))
                .get(&Label::Named("init".into()))
                .copied()
                .unwrap_or_else(|| {
                    self.config
                        .modules
                        .lookup_initializers(name)
                        .unwrap_or_else(|| panic!("did not get initializers for {name:?}"))
                        .get(&Label::Named("init".into()))
                        .copied()
                        .expect("did not get init")
                })
        });

        let init_entry = self
            .typed
            .types
            .get_symbol(&init_sym)
            .cloned()
            .expect("did not get init entry");

        let properties = self
            .typed
            .types
            .catalog
            .properties
            .get(name)
            .cloned()
            .unwrap_or_default();

        // Extract return type from the initializer function
        let mut params = init_entry.as_mono_ty().clone().uncurry_params();
        let _ret = params.pop().expect("did not get init ret");

        let Ty::Constructor { box ret, .. } = &callee.ty else {
            unreachable!()
        };

        self.push_instr(Instruction::Nominal {
            sym: *name,
            dest: record_dest,
            ty: ret.clone(),
            record: properties
                .iter()
                .map(|_| Value::Uninit)
                .collect::<Vec<_>>()
                .into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });
        args.insert(0, record_dest.into());

        self.push_instr(Instruction::Call {
            dest,
            ty: ret.clone(),
            callee: Value::Func(init_sym),
            args: args.into(),
            self_dest: None,
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok((dest.into(), ret.clone()))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, call_expr, callee, args))]
    fn lower_call(
        &mut self,
        call_expr: &TypedExpr,
        callee: &TypedExpr,
        args: &[TypedExpr],
        callee_sym: Option<&Symbol>,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        // Handle yield builtin call before consuming bind - this has its own control flow
        if let TypedExprKind::Variable(name) = &callee.kind
            && name == &Symbol::YIELD
        {
            return self.lower_yield_call(call_expr, args, bind);
        }

        // Handle print builtin
        if let TypedExprKind::Variable(name) = &callee.kind
            && name == &Symbol::PRINT
        {
            let arg = self.lower_expr(&args[0], Bind::Fresh)?;
            self.push_instr(Instruction::_Print { val: arg.0 });
            return Ok((Value::Void, Ty::Void));
        }

        let dest = self.ret(bind);
        let ty = call_expr.ty.clone();
        let mut arg_vals = vec![];
        let mut arg_tys = vec![];
        for arg in args {
            let (arg, arg_ty) = self.lower_expr(arg, Bind::Fresh)?;
            arg_vals.push(arg);
            arg_tys.push(arg_ty)
        }

        if let TypedExprKind::Constructor(name, ..) = &callee.kind {
            return self.lower_constructor_call(
                call_expr.id,
                name,
                callee,
                arg_vals,
                dest,
                callee_sym.copied(),
            );
        }

        if let TypedExprKind::Member {
            receiver: box receiver,
            label: member,
            ..
        } = &callee.kind
        {
            return self.lower_method_call(
                call_expr,
                callee,
                receiver.clone(),
                member,
                callee_sym.copied(),
                args,
                arg_vals,
                dest,
            );
        }

        // Handle Property (function-typed struct field) calls.
        // The specialization pass transforms `self.poll(args)` into Variable(property_sym)
        // with the receiver prepended as the first arg. We need to extract the field value
        // from the receiver and call it indirectly.
        if let Some(sym @ Symbol::Property(..)) = callee_sym {
            let receiver_ty = &arg_tys[0];
            let property_name = self
                .typed
                .resolved_names
                .symbol_names
                .get(sym)
                .or_else(|| self.config.modules.resolve_name(sym))
                .ok_or_else(|| IRError::TypeNotFound(format!("no name for property symbol {sym}")))?
                .clone();
            let label = self.label_from_name(&property_name);
            let field_label = self.field_index(receiver_ty, &label);

            let receiver_reg = arg_vals[0].as_register().map_err(|_| {
                IRError::TypeNotFound("expected register for property call receiver".into())
            })?;

            let field_reg = self.next_register();
            self.push_instr(Instruction::GetField {
                dest: field_reg,
                ty: callee.ty.clone(),
                record: receiver_reg,
                field: field_label,
                meta: Default::default(),
            });

            let field_args: Vec<Value> = arg_vals[1..].to_vec();
            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: field_reg.into(),
                args: field_args.into(),
                self_dest: None,
                meta: vec![InstructionMeta::Source(callee.id)].into(),
            });

            return Ok((dest.into(), ty));
        }

        // For specialized method calls (callee is Variable but was originally a method),
        // the first arg is `self`. Check if it's a variable and set up self_dest.
        // This applies to InstanceMethod calls and Synthesized calls (which are specialized methods).
        let is_method_like = matches!(
            callee_sym,
            Some(Symbol::InstanceMethod(_)) | Some(Symbol::Synthesized(_))
        );
        let (self_dest, receiver_binding, first_arg_var_sym) = if is_method_like
            && !arg_vals.is_empty()
            && let Some(first_arg) = args.first()
            && let TypedExprKind::Variable(var_sym) = &first_arg.kind
        {
            let self_dest_reg = self.next_register();
            let binding = self.current_func().bindings.get(var_sym).cloned();
            // Initialize self_dest_reg with current self value (in case method doesn't mutate)
            self.push_instr(Instruction::Constant {
                dest: self_dest_reg,
                ty: first_arg.ty.clone(),
                val: arg_vals[0].clone(),
                meta: Default::default(),
            });
            // For non-Pointer bindings, update the binding now
            // For Pointer bindings, we'll emit a Store after the Call
            if !matches!(binding, Some(Binding::Pointer(_))) && binding.is_some() {
                self.set_binding(var_sym, self_dest_reg);
            }
            (
                Some(self_dest_reg),
                binding,
                Some((var_sym, first_arg.ty.clone())),
            )
        } else {
            (None, None, None)
        };

        let callee_ir = self.lower_expr(callee, Bind::Fresh)?.0;

        self.push_instr(Instruction::Call {
            dest,
            ty: ty.clone(),
            callee: callee_ir,
            args: arg_vals.into(),
            self_dest,
            meta: vec![InstructionMeta::Source(callee.id)].into(),
        });

        // For Pointer bindings, emit Store AFTER the Call
        if let (Some(self_dest_reg), Some(Binding::Pointer(addr)), Some((_, first_arg_ty))) =
            (self_dest, receiver_binding, first_arg_var_sym)
        {
            self.push_instr(Instruction::Store {
                value: self_dest_reg.into(),
                ty: first_arg_ty,
                addr,
            });
        }

        Ok((dest.into(), ty))
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(level = tracing::Level::TRACE, skip(self, call_expr, callee_expr, receiver, arg_exprs, args ))]
    fn lower_method_call(
        &mut self,
        call_expr: &TypedExpr,
        callee_expr: &TypedExpr,
        mut receiver: TypedExpr,
        label: &Label,
        witness: Option<Symbol>,
        arg_exprs: &[TypedExpr],
        mut args: Vec<Value>,
        dest: Register,
    ) -> Result<(Value, Ty), IRError> {
        let ty = call_expr.ty.clone();

        if matches!(receiver.kind, TypedExprKind::Hole)
            && let Ty::Nominal { symbol, .. } = &call_expr.ty
            && self
                .typed
                .types
                .catalog
                .variants
                .get(symbol)
                .is_some_and(|variants| variants.contains_key(label))
        {
            return self.lower_enum_constructor(
                callee_expr.id,
                symbol,
                label,
                arg_exprs,
                args,
                Bind::Assigned(dest),
            );
        }

        if let Ty::Constructor {
            name: Name::Resolved(enum_symbol @ Symbol::Enum(..), ..),
            ..
        } = &receiver.ty
        {
            return self.lower_enum_constructor(
                callee_expr.id,
                enum_symbol,
                label,
                arg_exprs,
                args,
                Bind::Assigned(dest),
            );
        }

        // Function types are Showable at compile time -- emit their signature as a string literal
        if matches!(&receiver.ty, Ty::Func(..)) && label.to_string() == "show" {
            let formatter = crate::types::format::TypeFormatter::new(
                crate::types::format::SymbolNames::new(
                    Some(&self.typed.resolved_names.symbol_names),
                    None,
                ),
            );
            let sig = formatter.format_ty_for_show(&receiver.ty);
            let string_expr = TypedExpr {
                id: call_expr.id,
                ty: Ty::String(),
                kind: TypedExprKind::LiteralString(sig.clone()),
            };
            return self.lower_string(&string_expr, &sig, Bind::Assigned(dest));
        }

        // Capture the receiver variable symbol before any modification
        // This is needed to write back mutated self after the method call
        let receiver_var_sym = if let TypedExprKind::Variable(sym) = &receiver.kind {
            Some(*sym)
        } else {
            None
        };

        // Is this an instance method call on a constructor? If so we don't need
        // to prepend a self arg because it's passed explicitly (like Foo.bar(fizz) where
        // fizz == self)
        if let TypedExprKind::Constructor(_name, ..) = &receiver.kind {
            receiver = arg_exprs[0].clone();
        } else {
            let (receiver_ir, _) = self.lower_expr(&receiver, Bind::Fresh)?;
            args.insert(0, receiver_ir);
        }

        // Use the provided callee_sym if available (from specialization pass),
        // otherwise look it up from the receiver type
        let sym = if let Some(specialized_sym) = witness {
            specialized_sym
        } else {
            let callee_sym = match &receiver.ty {
                Ty::Primitive(sym) => self.lookup_member(sym, label),
                Ty::Nominal { symbol, .. } => self.lookup_member(symbol, label),
                Ty::Constructor {
                    name: Name::Resolved(sym, ..),
                    ..
                } => self.lookup_static_member(sym, label),
                Ty::Param(_, protocol_ids) => {
                    let mut found = None;
                    for pid in protocol_ids {
                        if let Some(sym) = self.lookup_member(&Symbol::Protocol(*pid), label) {
                            found = Some(sym);
                            break;
                        }
                    }
                    found
                },
                _ => {
                    return Err(IRError::WitnessNotFound(format!(
                        "could not determine callee sym for {:?}.{label:?}",
                        receiver.ty
                    )));
                }
            };

            callee_sym.ok_or_else(|| {
                IRError::WitnessNotFound(format!(
                    "could not determine callee sym for {receiver:?}.{label:?}"
                ))
            })?
        };

        // Determine self_dest: if receiver is a variable, allocate a register
        // to receive the mutated self
        let (self_dest, receiver_binding) = if let Some(var_sym) = receiver_var_sym {
            let self_dest_reg = self.next_register();
            let binding = self.current_func().bindings.get(&var_sym).cloned();
            tracing::trace!(
                ?var_sym,
                ?binding,
                ?self_dest_reg,
                "lower_method_call: checking receiver binding"
            );
            // Initialize self_dest_reg with current self value (in case method doesn't mutate)
            self.push_instr(Instruction::Constant {
                dest: self_dest_reg,
                ty: receiver.ty.clone(),
                val: args[0].clone(),
                meta: Default::default(),
            });
            // For non-Pointer bindings, update the binding now
            // For Pointer bindings, we'll emit a Store after the Call
            if !matches!(binding, Some(Binding::Pointer(_))) {
                if binding.is_some() {
                    tracing::trace!(
                        ?var_sym,
                        ?self_dest_reg,
                        "lower_method_call: updating binding"
                    );
                    self.set_binding(&var_sym, self_dest_reg);
                } else {
                    tracing::trace!(
                        ?var_sym,
                        "lower_method_call: no binding found, skipping set_binding"
                    );
                }
            }
            (Some(self_dest_reg), binding)
        } else {
            (None, None)
        };

        self.push_instr(Instruction::Call {
            dest,
            ty: call_expr.ty.clone(),
            callee: Value::Func(sym),
            args: args.into(),
            self_dest,
            meta: vec![InstructionMeta::Source(callee_expr.id)].into(),
        });

        // For Pointer bindings, emit Store AFTER the Call so that self_dest_reg
        // has the mutated value from the callee
        if let (Some(self_dest_reg), Some(Binding::Pointer(addr))) = (self_dest, receiver_binding) {
            let ty = receiver.ty.clone();
            self.push_instr(Instruction::Store {
                value: self_dest_reg.into(),
                ty,
                addr,
            });
        }

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func.name = %func.name))]
    fn lower_func(
        &mut self,
        func: &TypedFunc,
        bind: Bind,

        terminates_with: FuncTermination,
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_symbol(&func.name)?;

        // Check if this function contains yield builtin calls - if so, compile as state machine
        // Note: Only explicit yield calls trigger state machine compilation, not effect calls.
        // Effect calls continue to use the closure-based continuation approach.
        let get_ty = |sym: &Symbol| {
            self.typed.types.get_symbol(sym).map(|entry| match entry {
                TypeEntry::Mono(ty) => ty.clone(),
                TypeEntry::Poly(scheme) => scheme.ty.clone(),
            })
        };
        if let Some(analysis) =
            super::effect_analysis::EffectAnalysis::analyze_yield_only(func, get_ty)
        {
            // Function contains yield builtin calls - compile as state machine
            return self.lower_func_as_state_machine(func, analysis, bind);
        }

        let (mut param_tys, mut ret_ty) = uncurry_function(ty);

        // Track if this is a handler (needs continuation param)
        let is_handler = matches!(terminates_with, FuncTermination::Continuation(..));

        // Do we have captures? If so this is a closure
        let capture_env = if let Some(captures) =
            self.typed.resolved_names.captures.get(&func.name).cloned()
            && !captures.is_empty()
        {
            let mut env_fields = vec![];
            for capture in captures {
                let ty = self
                    .ty_from_symbol(&capture.symbol)
                    .expect("didn't get capture ty")
                    .clone();
                let is_handler = self
                    .typed
                    .resolved_names
                    .handler_symbols
                    .contains(&capture.symbol);
                // Global functions are resolved by symbol; don't treat them as captured env fields.
                // Immutable global constants are inlined by lower_variable; don't capture them.
                if matches!(capture.symbol, Symbol::Global(_)) && !is_handler {
                    if matches!(ty, Ty::Func(..)) {
                        continue;
                    }
                    if self.is_global_constant(&capture.symbol)
                        && !self
                            .typed
                            .resolved_names
                            .mutated_symbols
                            .contains(&capture.symbol)
                    {
                        continue;
                    }
                }

                let val = match self
                    .current_func_mut()
                    .bindings
                    .get(&capture.symbol)
                    .cloned()
                {
                    Some(Binding::Pointer(val)) => val,
                    Some(Binding::Capture { index, .. }) => {
                        // Captured from outer closure's env - emit getfield
                        let dest = self.next_register();
                        self.push_instr(Instruction::GetField {
                            dest,
                            ty: Ty::RawPtr,
                            record: 0.into(), // env is always %0
                            field: Label::Positional(index),
                            meta: vec![].into(),
                        });
                        Value::Reg(dest.0)
                    }
                    other => unreachable!("unexpected binding for capture: {other:?}"),
                };

                env_fields.push((capture.symbol, ty.clone(), val));
            }

            if env_fields.is_empty() {
                None
            } else {
                Some(env_fields)
            }
        } else {
            None
        };

        let _s = tracing::trace_span!("pushing new current function");
        self.current_function_stack
            .push(CurrentFunction::new(func.name));

        let mut params = vec![];

        // For handlers, the continuation closure is the first parameter
        if is_handler {
            let cont_reg = self.next_register();
            params.push(Value::Reg(cont_reg.0));
        }

        if let Some(env_fields) = capture_env.clone() {
            for (i, (binding, ty, ..)) in env_fields.iter().enumerate() {
                self.insert_binding(
                    *binding,
                    Binding::Capture {
                        index: i,
                        ty: ty.clone(),
                    },
                );
            }

            // Allocate env as %0
            let env_reg = self.next_register();
            params.push(Value::Reg(env_reg.0));
            param_tys.insert(
                0,
                Ty::Record(
                    None,
                    env_fields
                        .iter()
                        .enumerate()
                        .fold(Row::Empty, |row, (i, _)| Row::Extend {
                            row: row.into(),
                            label: Label::Positional(i),
                            ty: Ty::RawPtr,
                        })
                        .into(),
                ),
            );
        }

        for param in func.params.iter() {
            let register = self.next_register();
            params.push(Value::Reg(register.0));
            self.lower_param_binding(param, register);
        }

        let mut ret = Value::Void;
        for node in func.body.body.iter() {
            (ret, ret_ty) = self.lower_node(node)?;
        }

        // If we were lowering into a continuation, finalize it
        if let Some(idx) = self.current_continuation_idx.take() {
            // Set the terminator on the continuation
            if let Some(last_block) = self.pending_continuations[idx].0.blocks.last_mut() {
                last_block.terminator = Terminator::Ret {
                    val: ret.clone(),
                    ty: ret_ty.clone(),
                };
            }
            // Parent function should return the handler's result (stored in dest)
            let parent_dest = self.pending_continuations[idx].2;
            ret = parent_dest.into();
            // Keep the same ret_ty since handler returns the same type
        }

        // For methods, get the final self register (after any mutations).
        // This must be done before the terminator because get_binding may emit Load instructions.
        let self_out = func.params.first().map(|p| self.get_binding(&p.name));

        if ret == Value::Poison {
            self.push_terminator(Terminator::Unreachable);
        } else {
            self.push_terminator(Terminator::Ret {
                val: ret,
                ty: ret_ty.clone(),
            });
        }

        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");
        drop(_s);

        let func_ty = curry_ty(param_tys.iter(), ret_ty);
        self.functions.insert(
            current_function.symbol,
            PolyFunction {
                name: current_function.symbol,
                params,
                blocks: current_function.blocks,
                ty: func_ty.clone(),
                register_count: (current_function.registers.next) as usize,
                self_out,
            },
        );

        // Finalize any pending continuations
        for (continuation, parent_name, _parent_dest) in
            std::mem::take(&mut self.pending_continuations)
        {
            // Register the continuation symbol name
            self.typed.resolved_names.symbol_names.insert(
                continuation.symbol,
                format!("continuation({})", parent_name),
            );

            // Continuation receives captured env as first param, resumed value as second
            let cont_params = vec![Value::Reg(0), Value::Reg(1)];

            // Get the continuation's return type from its terminator
            let cont_ret_ty = continuation
                .blocks
                .last()
                .and_then(|b| match &b.terminator {
                    Terminator::Ret { ty, .. } => Some(ty.clone()),
                    _ => None,
                })
                .unwrap_or(Ty::Void);

            // Build env type from the continued bindings
            let env_ty = Ty::Record(
                None,
                continuation
                    .bindings
                    .values()
                    .filter_map(|b| match b {
                        Binding::Continued { ty, .. } => Some(ty.clone()),
                        _ => None,
                    })
                    .enumerate()
                    .fold(Row::Empty, |row, (i, ty)| Row::Extend {
                        row: row.into(),
                        label: Label::Positional(i),
                        ty,
                    })
                    .into(),
            );

            let cont_ty = Ty::Func(env_ty.into(), cont_ret_ty.into(), Row::Empty.into());

            self.functions.insert(
                continuation.symbol,
                PolyFunction {
                    name: continuation.symbol,
                    params: cont_params,
                    blocks: continuation.blocks,
                    ty: cont_ty,
                    register_count: continuation.registers.next as usize,
                    self_out: None,
                },
            );
        }

        let func_sym = func.name;
        let func_val = if let Some(env) = capture_env {
            Value::Closure {
                func: func_sym,
                env: env.into_iter().map(|e| e.2.clone()).collect_vec().into(),
            }
        } else {
            Value::Func(func_sym)
        };

        if bind != Bind::Discard {
            let dest = self.ret(bind);
            self.push_instr(Instruction::Ref {
                dest,
                ty: func_ty.clone(),
                val: func_val.clone(),
            });
            // Bind the function symbol to the register so later references use the Ref'd value
            self.insert_binding(func_sym, Binding::Register(dest.0));
        }

        Ok((func_val, func_ty))
    }

    /// Lower an effectful function as a state machine.
    /// The generated function has signature:
    ///   (state: Int, state_data: Record, resumed: T) -> (Int, Record, Poll<R>)
    fn lower_func_as_state_machine(
        &mut self,
        func: &TypedFunc,
        analysis: super::effect_analysis::EffectAnalysis,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        let func_ty = self.ty_from_symbol(&func.name)?;
        let (param_tys, ret_ty) = uncurry_function(func_ty.clone());

        // Generate a poll function name
        let poll_func_sym =
            Symbol::Synthesized(self.typed.symbols.next_synthesized(self.config.module_id));
        self.typed.resolved_names.symbol_names.insert(
            poll_func_sym,
            format!(
                "{}_poll",
                self.typed
                    .resolved_names
                    .symbol_names
                    .get(&func.name)
                    .cloned()
                    .unwrap_or_else(|| format!("{:?}", func.name))
            ),
        );

        // Create the poll function
        self.current_function_stack
            .push(CurrentFunction::new(poll_func_sym));

        // Parameters for poll function: state: Int, state_data: Record, resumed: T
        let state_var = self.next_register();
        let state_data = self.next_register();
        let resumed_var = self.next_register();

        let poll_params = vec![
            Value::Reg(state_var.0),
            Value::Reg(state_data.0),
            Value::Reg(resumed_var.0),
        ];

        // Block 0 is reserved for the dispatch block (will be filled in later).
        // Create block 1 for the initial state (state 0 code).
        let dispatch_block_id = self.current_block_id(); // block 0
        let initial_state_block = self.new_basic_block(); // block 1
        self.set_current_block(initial_state_block);

        // Set up state machine context
        self.state_machine_context = Some(StateMachineContext {
            analysis: analysis.clone(),
            current_state: 0,
            state_var,
            state_data,
            resumed_var,
            func_name: func.name,
            state_entries: vec![initial_state_block],
        });

        // Build parameter bindings for the original function parameters.
        for (i, param) in func.params.iter().enumerate() {
            self.insert_binding(
                param.name,
                Binding::Continued {
                    index: i,
                    ty: param.ty.clone(),
                },
            );
        }

        // Lower the function body - the state machine context will cause
        // yield calls to emit state transitions
        let mut _ret = Value::Void;
        let mut ret_ty_local = ret_ty.clone();
        for node in func.body.body.iter() {
            (_ret, ret_ty_local) = self.lower_node(node)?;
        }

        // Build GeneratorState::done to return when the generator finishes
        let done_state_ty = Ty::Tuple(vec![Ty::Int]);
        let done_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: done_reg,
            ty: done_state_ty.clone(),
            record: vec![Value::Int(1)].into(), // 1 = done tag
            meta: Default::default(),
        });

        let final_state_reg = self.next_register();
        self.push_instr(Instruction::Constant {
            dest: final_state_reg,
            val: Value::Int(
                self.state_machine_context
                    .as_ref()
                    .map_or(0, |ctx| ctx.analysis.state_count() as i64),
            ),
            ty: Ty::Int,
            meta: Default::default(),
        });

        let return_val = self.next_register();
        self.push_instr(Instruction::Record {
            dest: return_val,
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr, done_state_ty.clone()]),
            record: vec![final_state_reg.into(), state_data.into(), done_reg.into()].into(),
            meta: Default::default(),
        });

        self.push_terminator(Terminator::Ret {
            val: return_val.into(),
            ty: Ty::Tuple(vec![Ty::Int, Ty::RawPtr, done_state_ty.clone()]),
        });

        // The "done" block we just finished is the fallback for unknown states
        let done_block_id = self.current_block_id();

        // Build the dispatch block (block 0). It checks state_var and branches
        // to the appropriate state entry block.
        let state_entries = self
            .state_machine_context
            .as_ref()
            .map(|ctx| ctx.state_entries.clone())
            .unwrap_or_default();

        self.set_current_block(dispatch_block_id);

        // Chain of comparisons: if state == 0 goto state_0, elif state == 1 goto state_1, ...
        // For the last state, fall through to "done"
        let mut current_check_block = dispatch_block_id;
        for (i, &entry_block) in state_entries.iter().enumerate() {
            self.set_current_block(current_check_block);

            let cmp_reg = self.next_register();
            self.push_instr(Instruction::Cmp {
                dest: cmp_reg,
                op: CmpOperator::Equals,
                lhs: state_var.into(),
                rhs: Value::Int(i as i64),
                ty: Ty::Int,
                meta: Default::default(),
            });

            if i + 1 < state_entries.len() {
                // More states to check — create a new block for the next comparison
                let next_check_block = self.new_basic_block();
                self.push_terminator(Terminator::Branch {
                    cond: cmp_reg.into(),
                    conseq: entry_block,
                    alt: next_check_block,
                });
                current_check_block = next_check_block;
            } else {
                // Last state — else goes to "done" block
                self.push_terminator(Terminator::Branch {
                    cond: cmp_reg.into(),
                    conseq: entry_block,
                    alt: done_block_id,
                });
            }
        }

        // If there are no state entries (shouldn't happen), just jump to done
        if state_entries.is_empty() {
            self.set_current_block(dispatch_block_id);
            self.push_terminator(Terminator::Jump { to: done_block_id });
        }

        // Clear state machine context
        self.state_machine_context = None;

        let poll_func = self
            .current_function_stack
            .pop()
            .expect("no current function");

        // Poll function type: (Int, RawPtr, R) -> (Int, RawPtr, GeneratorState<Y>)
        let poll_ret_ty = Ty::Tuple(vec![
            Ty::Int,
            Ty::RawPtr,
            Ty::Tuple(vec![Ty::Int, ret_ty_local.clone()]),
        ]);
        let poll_func_ty = Ty::Func(
            Ty::Tuple(vec![Ty::Int, Ty::RawPtr, Ty::Void]).into(),
            poll_ret_ty.clone().into(),
            Row::Empty.into(),
        );

        self.functions.insert(
            poll_func_sym,
            PolyFunction {
                name: poll_func_sym,
                params: poll_params,
                blocks: poll_func.blocks,
                ty: poll_func_ty.clone(),
                register_count: poll_func.registers.next as usize,
                self_out: None,
            },
        );

        // Now create the wrapper function (gen itself) that returns a Generator record.
        // This is a proper function that can be called: it creates the Generator and returns it.
        self.current_function_stack
            .push(CurrentFunction::new(func.name));

        // Burn registers for any parameters the original function had
        let mut wrapper_params = vec![];
        for _param in func.params.iter() {
            let reg = self.next_register();
            wrapper_params.push(Value::Reg(reg.0));
        }

        // Create reference to poll function
        let poll_ref_reg = self.next_register();
        self.push_instr(Instruction::Ref {
            dest: poll_ref_reg,
            ty: poll_func_ty.clone(),
            val: Value::Func(poll_func_sym),
        });

        // Initial state is 0
        let initial_state_reg = self.next_register();
        self.push_instr(Instruction::Constant {
            dest: initial_state_reg,
            val: Value::Int(0),
            ty: Ty::Int,
            meta: Default::default(),
        });

        // Initial state_data is a null pointer
        let initial_state_data_reg = self.next_register();
        self.push_instr(Instruction::Constant {
            dest: initial_state_data_reg,
            val: Value::Int(0),
            ty: Ty::RawPtr,
            meta: Default::default(),
        });

        // Create the Generator record: { poll, state, state_data }
        // Row::Extend nesting: outermost label is first in closed row
        let generator_ty = Ty::Record(
            None,
            Row::Extend {
                row: Row::Extend {
                    row: Row::Extend {
                        row: Row::Empty.into(),
                        label: Label::Positional(2),
                        ty: Ty::RawPtr,
                    }
                    .into(),
                    label: Label::Positional(1),
                    ty: Ty::Int,
                }
                .into(),
                label: Label::Positional(0),
                ty: poll_func_ty.clone(),
            }
            .into(),
        );

        let gen_result_reg = self.next_register();
        self.push_instr(Instruction::Record {
            dest: gen_result_reg,
            ty: generator_ty.clone(),
            record: vec![
                poll_ref_reg.into(),
                initial_state_reg.into(),
                initial_state_data_reg.into(),
            ]
            .into(),
            meta: Default::default(),
        });

        self.push_terminator(Terminator::Ret {
            val: gen_result_reg.into(),
            ty: generator_ty.clone(),
        });

        let wrapper_func = self
            .current_function_stack
            .pop()
            .expect("no current function");

        let wrapper_func_ty = curry_ty(param_tys.iter(), generator_ty.clone());
        self.functions.insert(
            func.name,
            PolyFunction {
                name: func.name,
                params: wrapper_params,
                blocks: wrapper_func.blocks,
                ty: wrapper_func_ty.clone(),
                register_count: wrapper_func.registers.next as usize,
                self_out: None,
            },
        );

        // Return Value::Func so callers can call this function normally
        let dest = self.ret(bind);
        self.push_instr(Instruction::Constant {
            dest,
            val: Value::Func(func.name),
            ty: wrapper_func_ty.clone(),
            meta: Default::default(),
        });

        Ok((dest.into(), wrapper_func_ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_instr(&mut self, instruction: Instruction<Ty>) {
        let current_function = self.current_func_mut();
        let current_block_idx = current_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");
        current_function.blocks[*current_block_idx]
            .instructions
            .push(instruction);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_phi(&mut self, phi: Phi<Ty>) {
        let stack_function = self.stack_func_mut();
        let current_block_idx = stack_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");
        stack_function.blocks[*current_block_idx].phis.push(phi);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn new_basic_block(&mut self) -> BasicBlockId {
        let stack_function = self.stack_func_mut();
        let id = BasicBlockId(stack_function.blocks.len() as u32);
        let new_block = BasicBlock {
            id,
            phis: Default::default(),
            instructions: Default::default(),
            terminator: Terminator::Unreachable,
        };
        stack_function.blocks.push(new_block);
        id
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn set_current_block(&mut self, id: BasicBlockId) {
        self.stack_func_mut().current_block_idx.push(id.0 as usize);
    }

    fn current_block_id(&mut self) -> BasicBlockId {
        let stack_function = self.stack_func_mut();
        let current_block_idx = *stack_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");
        stack_function.blocks[current_block_idx].id
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, f))]
    fn in_basic_block<T>(
        &mut self,
        id: BasicBlockId,
        f: impl FnOnce(&mut Lowerer<'a>) -> Result<T, IRError>,
    ) -> Result<T, IRError> {
        // Block indices always go to the stack function, not continuations.
        // Continuations are for sequential code after effect calls, not for
        // control flow block structure.
        let stack_idx = self.current_function_stack.len() - 1;
        self.current_function_stack[stack_idx]
            .current_block_idx
            .push(id.0 as usize);

        // Clear continuation state for sibling blocks - an effect call in one
        // branch shouldn't affect other branches. The continuation state will
        // be re-established after all branches are processed.
        let saved_cont_idx = self.current_continuation_idx.take();

        // Save bindings so that method-call save-copy updates (set_binding in
        // lower_call/lower_method_call) don't leak across block boundaries.
        // Without this, a save-copy register defined only in one branch of an
        // if-expression would be referenced in the continuation block — an SSA
        // dominance violation.
        let saved_bindings = self.current_function_stack[stack_idx].bindings.clone();

        let ret = f(self);

        // Restore bindings. Mutable variables use Pointer bindings (alloc/store/load)
        // which are unaffected by this restore. Only Register bindings (for immutable
        // values) are affected, and their save-copies are just redundant copies of the
        // same value, so restoring the original binding is correct.
        self.current_function_stack[stack_idx].bindings = saved_bindings;

        // Merge continuation state: if a continuation was created in this block,
        // propagate it. Otherwise restore the saved state.
        if self.current_continuation_idx.is_none() {
            self.current_continuation_idx = saved_cont_idx;
        }

        self.current_function_stack[stack_idx]
            .current_block_idx
            .pop();

        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let stack_function = self.stack_func_mut();
        let current_block_idx = stack_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");

        let block = &mut stack_function.blocks[*current_block_idx];
        // Don't override an existing terminator (e.g., from an early return)
        if block.terminator != Terminator::Unreachable {
            tracing::warn!("trying to overwrite terminator");
            return;
        }
        block.terminator = terminator;
    }

    fn insert_binding(&mut self, symbol: Symbol, binding: Binding<Ty>) {
        self.current_func_mut().bindings.insert(symbol, binding);
    }

    fn get_binding(&mut self, symbol: &Symbol) -> Register {
        let binding = self
            .current_function_stack
            .iter()
            .rev()
            .find_map(|f| f.bindings.get(symbol))
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "did not get binding for {symbol:?} in {:?}",
                    self.current_func().bindings
                )
            });
        let ty = self
            .typed
            .types
            .get_symbol(symbol)
            .unwrap_or_else(|| panic!("did not get ty for {symbol:?}"))
            .as_mono_ty()
            .clone();

        match binding {
            Binding::Register(reg) => Register(reg),
            Binding::Continued { index, ty } => {
                let dest = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: ty.clone(),
                    record: Register(0),
                    field: Label::Positional(index),
                    meta: Default::default(),
                });
                dest
            }
            Binding::Capture { index, ty } => {
                let ptr = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest: ptr,
                    ty: Ty::RawPtr,
                    record: 0.into(),
                    field: Label::Positional(index),
                    meta: vec![].into(),
                });
                let dest = self.next_register();
                self.push_instr(Instruction::Load {
                    dest,
                    ty,
                    addr: ptr.into(),
                });
                dest
            }
            Binding::Pointer(addr) => {
                let dest = self.next_register();
                self.push_instr(Instruction::Load { dest, ty, addr });
                dest
            }
        }
    }

    fn set_binding(&mut self, symbol: &Symbol, value_register: Register) {
        let ty = self
            .typed
            .types
            .get_symbol(symbol)
            .expect("did not get ty for {symbol:?}")
            .as_mono_ty()
            .clone();

        let binding = self
            .current_func_mut()
            .bindings
            .get(symbol)
            .cloned()
            .expect("did not get binding");

        match binding {
            Binding::Register(..) => {
                self.current_func_mut()
                    .bindings
                    .insert(*symbol, value_register.into());
            }
            Binding::Continued { index, ty } => {
                let dest = self.next_register();
                self.push_instr(Instruction::SetField {
                    dest,
                    val: value_register.into(),
                    ty: ty.clone(),
                    record: Register(0),
                    field: Label::Positional(index),
                    meta: Default::default(),
                });
                self.current_func_mut()
                    .bindings
                    .insert(*symbol, Binding::Register(dest.0));
            }
            Binding::Capture { index, ty } => {
                let dest = self.next_register();
                self.push_instr(Instruction::GetField {
                    dest,
                    ty: Ty::RawPtr,
                    record: Register(0),
                    field: Label::Positional(index),
                    meta: vec![].into(),
                });

                self.push_instr(Instruction::Store {
                    value: value_register.into(),
                    ty,
                    addr: dest.into(),
                });
            }
            Binding::Pointer(addr) => {
                self.push_instr(Instruction::Store {
                    value: value_register.into(),
                    ty,
                    addr: addr.clone(),
                });
            }
        }
    }

    fn current_func_mut(&mut self) -> &mut CurrentFunction {
        if let Some(idx) = self.current_continuation_idx {
            &mut self.pending_continuations[idx].0
        } else {
            self.current_function_stack
                .last_mut()
                .expect("didn't get current function")
        }
    }

    fn current_func(&mut self) -> &CurrentFunction {
        if let Some(idx) = self.current_continuation_idx {
            &self.pending_continuations[idx].0
        } else {
            self.current_function_stack
                .last()
                .expect("didn't get current function")
        }
    }

    // Always returns the stack function, ignoring continuations.
    // Used for block-related operations (blocks belong to the function that created them).
    fn stack_func_mut(&mut self) -> &mut CurrentFunction {
        self.current_function_stack
            .last_mut()
            .expect("didn't get stack function")
    }

    fn next_register(&mut self) -> Register {
        let register = self.current_func_mut().registers.next();
        tracing::trace!("allocated register: {register}");
        register
    }

    fn ret(&mut self, bind: Bind) -> Register {
        match bind {
            Bind::Assigned(value) => value,
            Bind::Fresh => self.next_register(),
            Bind::Discard => Register::DROP,
            Bind::Indirect(..) => self.next_register(),
        }
    }

    fn parsed_ty(&mut self, ty: &TypeAnnotation) -> Ty {
        let sym = ty.symbol().expect("did not get ty symbol");
        let entry = self
            .typed
            .types
            .types_by_symbol
            .get(&sym)
            .cloned()
            .expect("did not get entry");
        entry.as_mono_ty().clone()
    }

    fn parsed_register(
        &self,
        reg: &crate::node_kinds::inline_ir_instruction::Register,
        dest: Register,
    ) -> Register {
        if reg.0 == "?" {
            dest
        } else {
            Register(reg.0.parse().expect("did not get register"))
        }
    }

    fn parsed_value(
        &self,
        value: &crate::node_kinds::inline_ir_instruction::Value,
        binds: &[Value],
    ) -> Value {
        match value {
            crate::node_kinds::inline_ir_instruction::Value::Reg(v) => Value::Reg(*v),
            crate::node_kinds::inline_ir_instruction::Value::Int(v) => Value::Int(*v),
            crate::node_kinds::inline_ir_instruction::Value::Float(v) => Value::Float(*v),
            crate::node_kinds::inline_ir_instruction::Value::Bool(v) => Value::Bool(*v),
            crate::node_kinds::inline_ir_instruction::Value::Void => Value::Void,
            crate::node_kinds::inline_ir_instruction::Value::Uninit => Value::Uninit,
            crate::node_kinds::inline_ir_instruction::Value::Poison => Value::Poison,
            crate::node_kinds::inline_ir_instruction::Value::Record(id, values) => Value::Record(
                *id,
                values.iter().map(|v| self.parsed_value(v, binds)).collect(),
            ),
            crate::node_kinds::inline_ir_instruction::Value::RawPtr(v) => Value::RawPtr(Addr(*v)),
            crate::node_kinds::inline_ir_instruction::Value::RawBuffer(items) => {
                Value::RawBuffer(items.to_vec())
            }
            crate::node_kinds::inline_ir_instruction::Value::Bind(i) => binds[*i].clone(),
        }
    }

    fn field_index(&self, receiver_ty: &Ty, label: &Label) -> Label {
        match receiver_ty {
            Ty::Record(_, row) if let Some(idx) = row.close().get_index_of(label) => {
                Label::Positional(idx)
            }
            Ty::Nominal { symbol, .. }
                if let Some(idx) = self
                    .lookup_nominal(symbol)
                    .expect("didn't find nominal")
                    .properties
                    .get_index_of(label) =>
            {
                Label::Positional(idx)
            }
            _ => panic!("unable to determine field index of {receiver_ty:?}.{label}"),
        }
    }

    /// Look up instance/conformance methods — checks local catalog, then external modules
    fn lookup_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        self.typed
            .types
            .catalog
            .lookup_member(receiver, label)
            .map(|s| s.0)
            .or_else(|| self.config.modules.lookup_member(receiver, label))
    }

    /// Look up static methods — checks local catalog, then external modules
    fn lookup_static_member(&self, receiver: &Symbol, label: &Label) -> Option<Symbol> {
        self.typed
            .types
            .catalog
            .lookup_static_member(receiver, label)
            .or_else(|| self.config.modules.lookup_static_member(receiver, label))
    }

    /// Look up nominal type info — checks local catalog, then external modules
    fn lookup_nominal(&self, symbol: &Symbol) -> Option<&Nominal> {
        self.typed
            .types
            .catalog
            .nominals
            .get(symbol)
            .or_else(|| self.config.modules.lookup_nominal(symbol))
    }

    /// Look up an instance method by name — checks local catalog, then external modules
    fn lookup_instance_method(&self, symbol: &Symbol, label: &Label) -> Option<Symbol> {
        self.typed
            .types
            .catalog
            .instance_methods
            .get(symbol)
            .and_then(|methods| methods.get(label).copied())
            .or_else(|| {
                self.config
                    .modules
                    .lookup_instance_methods(symbol)
                    .and_then(|methods| methods.get(label).copied())
            })
    }

    fn label_from_name(&self, name: &str) -> Label {
        name.parse()
            .unwrap_or_else(|_| Label::Named(name.to_string()))
    }

    fn ty_from_symbol(&self, symbol: &Symbol) -> Result<Ty, IRError> {
        match self.typed.types.get_symbol(symbol) {
            Some(TypeEntry::Mono(ty)) => Ok(ty.clone()),
            Some(TypeEntry::Poly(scheme)) => Ok(scheme.ty.clone()),
            None => {
                if matches!(
                    symbol,
                    Symbol::Synthesized(SynthesizedId {
                        module_id: ModuleId::Current,
                        local_id: 0
                    })
                ) {
                    Ok(Ty::Func(
                        Ty::Void.into(),
                        Ty::Void.into(),
                        Row::Empty.into(),
                    ))
                } else {
                    Err(IRError::TypeNotFound(format!(
                        "Type not found for symbol: {symbol}"
                    )))
                }
            }
        }
    }
}

fn is_main_func(node: &TypedDecl, symbol_names: &FxHashMap<Symbol, String>) -> bool {
    if let TypedDeclKind::Let {
        initializer:
            Some(TypedExpr {
                kind: TypedExprKind::Func(TypedFunc { name: func_sym, .. }),
                ..
            }),
        ..
    } = &node.kind
        && symbol_names.get(func_sym).map(|s| s.as_str()) == Some("main")
    {
        return true;
    }

    false
}

pub fn curry_ty<'a, I: IntoIterator<Item = &'a Ty>>(params: I, ret: Ty) -> Ty {
    let mut params = params.into_iter().collect::<Vec<_>>();
    if params.is_empty() {
        params.push(&Ty::Void);
    }
    params.into_iter().rfold(ret, |acc, p| {
        Ty::Func(Box::new(p.clone()), Box::new(acc), Row::Empty.into())
    })
}
