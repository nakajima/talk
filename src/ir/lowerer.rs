use std::fmt::Display;

use crate::compiling::driver::{CompilationMode, DriverConfig};
use crate::compiling::module::ModuleId;
use crate::ir::basic_block::{Phi, PhiSource};
use crate::ir::function::Function;
use crate::ir::instruction::CmpOperator;
use crate::ir::ir_ty::IrTy;
use crate::ir::monomorphizer::uncurry_function;
use crate::ir::value::{Addr, RecordId, Reference};
use crate::label::Label;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::Symbols;
use crate::node_kinds::inline_ir_instruction::{InlineIRInstructionKind, TypedInlineIRInstruction};
use crate::node_kinds::type_annotation::TypeAnnotation;
use crate::types::infer_row::RowParamId;
use crate::types::infer_ty::TypeParamId;
use crate::types::predicate::Predicate;
use crate::types::row::Row;
use crate::types::typed_ast::{
    TypedAST, TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
    TypedMatchArm, TypedNode, TypedParameter, TypedPattern, TypedPatternKind, TypedRecordField,
    TypedStmt, TypedStmtKind,
};
use crate::{
    ir::{
        basic_block::{BasicBlock, BasicBlockId},
        instruction::{CallInstantiations, Instruction, InstructionMeta},
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
        matcher::{
            Constructor, MatchPlan, PlanNode, PlanNodeId, Projection, ValueId, ValueRef,
            plan_for_pattern,
        },
        scheme::ForAll,
        ty::Ty,
        type_operations::{InstantiationSubstitutions, collect_instantiations},
        type_session::{TypeEntry, Types},
    },
};
use derive_visitor::{Drive, Visitor};
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

#[derive(Clone, Debug, Default, PartialEq)]
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

#[derive(Default, Clone, Debug)]
pub(crate) struct Substitutions {
    pub ty: FxHashMap<Ty, Ty>,
    pub row: FxHashMap<RowParamId, Row>,
    /// Maps MethodRequirement symbols to their concrete implementations for witness specialization
    pub witnesses: FxHashMap<Symbol, Symbol>,
}

impl Substitutions {
    pub fn extend(&mut self, other: Substitutions) {
        self.ty.extend(other.ty);
        self.row.extend(other.row);
        self.witnesses.extend(other.witnesses);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PolyFunction {
    pub name: Symbol,
    pub params: Vec<Value>,
    pub blocks: Vec<BasicBlock<Ty>>,
    pub ty: Ty,
    pub register_count: usize,
}

#[derive(Debug, Clone)]
pub struct Specialization {
    pub name: Symbol,
    pub(super) substitutions: Substitutions,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SpecializationKey {
    ty: Vec<(TypeParamId, Ty)>,
    row: Vec<(RowParamId, Row)>,
    witnesses: Vec<(Symbol, Symbol)>,
}

impl SpecializationKey {
    pub(crate) fn new(substitutions: &Substitutions) -> Self {
        let mut ty: Vec<(TypeParamId, Ty)> = substitutions
            .ty
            .iter()
            .filter_map(|(k, v)| match k {
                Ty::Param(param) => Some((*param, v.clone())),
                other => {
                    tracing::warn!("unexpected type substitution key: {other:?} -> {v:?}");
                    None
                }
            })
            .collect();
        ty.sort_by_key(|(param, _)| *param);

        let mut row: Vec<(RowParamId, Row)> = substitutions
            .row
            .iter()
            .filter_map(|(param, row)| {
                if *row == Row::Param(*param) {
                    None
                } else {
                    Some((*param, row.clone()))
                }
            })
            .collect();
        row.sort_by_key(|(param, _)| *param);

        let mut witnesses: Vec<(Symbol, Symbol)> = substitutions
            .witnesses
            .iter()
            .map(|(req, imp)| (*req, *imp))
            .collect();
        witnesses.sort_by_key(|(req, _)| *req);

        Self { ty, row, witnesses }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.ty.is_empty() && self.row.is_empty() && self.witnesses.is_empty()
    }

    pub(crate) fn parts(&self) -> Vec<String> {
        let mut parts: Vec<String> = self.ty.iter().map(|(_p, ty)| format!("{ty}")).collect();
        parts.extend(self.row.iter().map(|(p, row)| format!("{p:?}={row:?}")));
        parts.extend(
            self.witnesses
                .iter()
                .map(|(req, imp)| format!("{req}->{imp}")),
        );
        parts
    }
}

pub enum FlowContext {
    Loop {
        top_block_id: BasicBlockId,
        join_block_id: BasicBlockId,
    },
}

type TypedFuncTy = TypedFunc<Ty>;

#[derive(Visitor)]
#[visitor(TypedFuncTy(enter))]
struct FuncForallsCollector {
    map: FxHashMap<Symbol, Vec<TypeParamId>>,
}

impl FuncForallsCollector {
    fn new() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }

    fn enter_typed_func_ty(&mut self, func: &TypedFuncTy) {
        let type_params: Vec<TypeParamId> = func
            .foralls
            .iter()
            .filter_map(|forall| match forall {
                ForAll::Ty(id) => Some(*id),
                _ => None,
            })
            .collect();

        if !type_params.is_empty() {
            self.map.entry(func.name).or_insert(type_params);
        }
    }
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

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer<'a> {
    pub(super) ast: &'a mut TypedAST<Ty>,
    pub(super) types: &'a mut Types,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,
    pub(super) config: &'a DriverConfig,

    pub(super) symbols: &'a mut Symbols,
    pub(super) resolved_names: &'a mut ResolvedNames,
    pub(super) specializations: IndexMap<Symbol, Vec<Specialization>>,
    pub(super) specialization_intern: FxHashMap<Symbol, FxHashMap<SpecializationKey, Symbol>>,
    func_foralls: FxHashMap<Symbol, Vec<TypeParamId>>,
    static_memory: StaticMemory,
    record_labels: FxHashMap<RecordId, Vec<String>>,
    next_record_id: u32,
    flow_context_stack: Vec<FlowContext>,
    pending_continuations: Vec<(CurrentFunction, Symbol, Register)>,
    current_continuation_idx: Option<usize>,
}

#[allow(clippy::panic)]
#[allow(clippy::expect_used)]
impl<'a> Lowerer<'a> {
    pub fn new(
        ast: &'a mut TypedAST<Ty>,
        types: &'a mut Types,
        symbols: &'a mut Symbols,
        resolved_names: &'a mut ResolvedNames,
        config: &'a DriverConfig,
    ) -> Self {
        let func_foralls = Self::collect_func_foralls(ast);
        Self {
            ast,
            types,
            functions: Default::default(),
            current_function_stack: Default::default(),
            symbols,
            specializations: Default::default(),
            specialization_intern: Default::default(),
            func_foralls,
            static_memory: Default::default(),
            config,
            resolved_names,
            next_record_id: 0,
            record_labels: Default::default(),
            flow_context_stack: Default::default(),
            pending_continuations: Default::default(),
            current_continuation_idx: None,
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.ast.roots().is_empty() {
            let mut program = Program::default();
            program.functions.insert(
                Symbol::Main,
                Function {
                    name: Symbol::Main,
                    params: Default::default(),
                    blocks: Default::default(),
                    ty: IrTy::Void,
                    register_count: 0,
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

        for root in self.ast.roots() {
            self.lower_node(&root, &Default::default())?;
        }

        // Check for required imports
        let funcs = self.functions.keys().cloned().collect_vec();
        for sym in funcs {
            _ = self.check_import(&sym, &Default::default());
        }

        let static_memory = std::mem::take(&mut self.static_memory);
        let record_labels = std::mem::take(&mut self.record_labels);
        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
            polyfunctions: monomorphizer.functions,
            static_memory,
            record_labels,
        })
    }

    fn lower_main(&mut self) {
        // Do we have a main func?
        let has_main_func = self
            .ast
            .decls
            .iter()
            .any(|d| is_main_func(d, &self.resolved_names.symbol_names));
        if !has_main_func {
            let main_symbol = Symbol::Main;
            let mut ret_ty = Ty::Void;

            let func = TypedFunc::<Ty> {
                name: main_symbol,
                foralls: Default::default(),
                params: Default::default(),
                effects: Default::default(),
                effects_row: Row::Empty,
                body: TypedBlock {
                    body: {
                        let nodes: Vec<TypedNode<Ty>> = self.ast.roots();

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
            self.ast.decls.push(TypedDecl {
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
                        instantiations: Default::default(),
                    }),
                },
            });

            self.types.define(
                main_symbol,
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into(), Row::Empty.into())),
            );

            self.resolved_names
                .symbol_names
                .insert(main_symbol, "main(synthesized)".to_string());
        }
    }

    fn lower_node(
        &mut self,
        node: &TypedNode<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        self.lower_node_with_bind(node, instantiations, Bind::Fresh)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, node), fields(node.id = %node.node_id()))]
    fn lower_node_with_bind(
        &mut self,
        node: &TypedNode<Ty>,
        instantiations: &Substitutions,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        tracing::info!("{node:?}");
        match node {
            TypedNode::Decl(decl) => self.lower_decl(decl, instantiations),
            TypedNode::Stmt(stmt) => self.lower_stmt(stmt, instantiations, bind),
            TypedNode::Expr(expr) => self.lower_expr(expr, bind, instantiations),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl), fields(decl.id = %decl.id))]
    fn lower_decl(
        &mut self,
        decl: &TypedDecl<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        match &decl.kind {
            TypedDeclKind::Let {
                pattern,
                initializer,
                ..
            } => {
                if matches!(
                    pattern.kind,
                    TypedPatternKind::Bind(_) | TypedPatternKind::Wildcard
                ) {
                    let bind = self.lower_pattern(pattern)?;
                    if let Some(initializer) = initializer {
                        match bind {
                            Bind::Assigned(reg) => {
                                self.lower_expr(initializer, Bind::Assigned(reg), instantiations)?;
                            }
                            Bind::Fresh => {
                                self.lower_expr(initializer, Bind::Fresh, instantiations)?;
                            }
                            Bind::Discard => {
                                self.lower_expr(initializer, Bind::Discard, instantiations)?;
                            }
                            Bind::Indirect(reg, ..) => {
                                let (val, ty) =
                                    self.lower_expr(initializer, Bind::Fresh, instantiations)?;
                                self.push_instr(Instruction::Store {
                                    value: val,
                                    ty,
                                    addr: reg.into(),
                                });
                            }
                        }
                    }
                } else if let Some(initializer) = initializer {
                    self.lower_let_pattern(pattern, initializer, instantiations)?;
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
                    self.lower_init(decl, symbol, initializer, instantiations)?;
                }

                for method in instance_methods.values() {
                    self.lower_method(method, instantiations)?;
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
                    self.lower_method(method, instantiations)?;
                }
            }
            TypedDeclKind::EnumDef {
                symbol,
                instance_methods,
                variants,
                ..
            } => {
                for method in instance_methods.values() {
                    self.lower_method(method, instantiations)?;
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
                    self.lower_method(method, instantiations)?;
                }
            }
        }

        Ok((Value::Void, Ty::Void))
    }

    fn lower_method(
        &mut self,
        func: &TypedFunc<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        self.lower_func(func, Bind::Discard, instantiations, FuncTermination::Return)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, initializer))]
    fn lower_init(
        &mut self,
        decl: &TypedDecl<Ty>,
        name: &Symbol,
        initializer: &TypedFunc<Ty>,
        instantiations: &Substitutions,
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
                self.types.get_symbol(name).unwrap(),
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

        let mut ret_ty = initializer.ret.clone();
        let mut ret = Value::Void;
        for node in initializer.body.body.iter() {
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
        }

        if ret == Value::Poison {
            self.push_terminator(Terminator::Unreachable);
        } else {
            self.push_terminator(Terminator::Ret {
                val: ret.clone(),
                ty: ret_ty.clone(),
            });
        }

        #[allow(clippy::expect_used)]
        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");

        self.functions.insert(
            initializer.name,
            PolyFunction {
                name: initializer.name,
                params: param_values,
                blocks: current_function.blocks,
                ty: Ty::Func(
                    Box::new(param_ty.clone()),
                    Box::new(ret_ty.clone()),
                    Row::Empty.into(),
                ),
                register_count: (current_function.registers.next) as usize,
            },
        );

        Ok((ret, ret_ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt), fields(stmt.id = %stmt.id))]
    fn lower_stmt(
        &mut self,
        stmt: &TypedStmt<Ty>,
        instantiations: &Substitutions,
        bind: Bind,
    ) -> Result<(Value, Ty), IRError> {
        match &stmt.kind {
            TypedStmtKind::Expr(typed_expr) => self.lower_expr(typed_expr, bind, instantiations),
            TypedStmtKind::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs, instantiations),
            TypedStmtKind::Return(typed_expr) => {
                self.lower_return(typed_expr, bind, instantiations)
            }
            TypedStmtKind::Continue(Some(expr)) => {
                self.lower_resume(stmt.id, expr, bind, instantiations)
            }
            TypedStmtKind::Continue(None) => self.lower_continue(),
            TypedStmtKind::Loop(cond, typed_block) => {
                self.lower_loop(&Some(cond.clone()), typed_block, instantiations)
            }
            TypedStmtKind::Break => self.lower_break(),
            TypedStmtKind::Handler { func, .. } => {
                self.lower_effect_handler(stmt.id, func, bind, instantiations)
            }
        }
    }

    fn lower_resume(
        &mut self,
        _id: NodeID,
        expr: &TypedExpr<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (val, val_ty) = self.lower_expr(expr, Bind::Fresh, instantiations)?;

        // Call continuation (register 0) with resumed value
        let dest = self.ret(bind);
        self.push_instr(Instruction::Call {
            dest,
            ty: val_ty.clone(),
            callee: Value::Reg(0),
            args: vec![val].into(),
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
        cond: &Option<TypedExpr<Ty>>,
        block: &TypedBlock<Ty>,
        instantiations: &Substitutions,
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
                let (val, _) = lowerer.lower_expr(cond, Bind::Fresh, instantiations)?;
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
            lowerer.lower_block(block, Bind::Discard, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: top_block_id });

            Ok(())
        })?;

        self.set_current_block(join_block_id);

        self.flow_context_stack.pop();

        Ok((Value::Void, Ty::Void))
    }

    fn lower_return(
        &mut self,
        expr: &Option<TypedExpr<Ty>>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (val, ty) = if let Some(expr) = expr {
            self.lower_expr(expr, bind, instantiations)?
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
        cond: &TypedExpr<Ty>,
        conseq: &TypedBlock<Ty>,
        alt: &TypedBlock<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let cond_ir = self.lower_expr(cond, Bind::Fresh, instantiations)?;

        let conseq_block_id = self.new_basic_block();
        let alt_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();

        let conseq_val = self.in_basic_block(conseq_block_id, |lowerer| {
            let (val, _) = lowerer.lower_block(conseq, Bind::Fresh, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(val)
        })?;

        let alt_val = self.in_basic_block(alt_block_id, |lowerer| {
            let (val, _) = lowerer.lower_block(alt, Bind::Fresh, instantiations)?;
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
    fn lower_block(
        &mut self,
        block: &TypedBlock<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        for (i, node) in block.body.iter().enumerate() {
            // We want to skip the last one in the loop so we can handle it outside the loop and use our Bind
            if i < block.body.len() - 1 {
                self.lower_node(node, instantiations)?;
            }
        }

        let (val, ty) = if let Some(node) = block.body.last() {
            self.lower_node_with_bind(node, instantiations, bind)?
        } else {
            (Value::Void, Ty::Void)
        };

        Ok((val, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs), fields(lhs.id = %lhs.id, rhs.id = %rhs.id))]
    fn lower_assignment(
        &mut self,
        lhs: &TypedExpr<Ty>,
        rhs: &TypedExpr<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let lvalue = self.lower_lvalue(lhs, instantiations)?;
        let (value, ty) = self.lower_expr(rhs, Bind::Fresh, instantiations)?;

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

    fn lower_lvalue(
        &mut self,
        expr: &TypedExpr<Ty>,
        instantiations: &Substitutions,
    ) -> Result<LValue, IRError> {
        match &expr.kind {
            TypedExprKind::Variable(name) => Ok(LValue::Variable(*name)),
            TypedExprKind::Member {
                receiver: box receiver,
                label,
            } => {
                let (receiver_ty, instantiations) = self
                    .specialized_ty(receiver, instantiations)
                    .expect("didn't get base ty");
                let receiver_lvalue = self.lower_lvalue(receiver, &instantiations)?;

                let receiver_ty = substitute(receiver_ty, &instantiations);

                Ok(LValue::Field {
                    base: receiver_lvalue.into(),
                    ty: receiver_ty.clone(),
                    field: label.clone(),
                })
            }
            _ => Err(IRError::InvalidAssignmentTarget(format!("{expr:?}"))),
        }
    }

    fn lower_param_binding(&mut self, param: &TypedParameter<Ty>, register: Register) {
        if self.resolved_names.is_captured.contains(&param.name)
            || self.resolved_names.mutated_symbols.contains(&param.name)
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
    fn lower_pattern(&mut self, pattern: &TypedPattern<Ty>) -> Result<Bind, IRError> {
        match &pattern.kind {
            TypedPatternKind::Or(..) => unimplemented!(),
            TypedPatternKind::Bind(symbol) => {
                let value = if self.resolved_names.is_captured.contains(symbol)
                    || self.resolved_names.mutated_symbols.contains(symbol)
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
        pattern: &TypedPattern<Ty>,
        initializer: &TypedExpr<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(), IRError> {
        let scrutinee_register = self.next_register();
        self.lower_expr(
            initializer,
            Bind::Assigned(scrutinee_register),
            instantiations,
        )?;

        let plan = plan_for_pattern(self.types, pattern.ty.clone(), pattern);
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
            if self.resolved_names.is_captured.contains(symbol) {
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
    fn lower_expr(
        &mut self,
        expr: &TypedExpr<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let mut instantiations = instantiations.clone();
        self.extend_instantiations_from_expr(&mut instantiations, expr);

        let (value, ty) = match &expr.kind {
            TypedExprKind::Hole => Err(IRError::TypeNotFound("nope".into())),
            TypedExprKind::CallEffect { effect, args } => {
                self.lower_effect_call(expr, effect, args, bind, &instantiations)
            }
            TypedExprKind::InlineIR(inline_irinstruction) => {
                self.lower_inline_ir(expr, inline_irinstruction, bind, &instantiations)
            }
            TypedExprKind::LiteralArray(typed_exprs) => {
                self.lower_array(expr, typed_exprs, bind, &instantiations)
            }
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
            TypedExprKind::LiteralString(val) => {
                self.lower_string(expr, val, bind, &instantiations)
            }
            TypedExprKind::Tuple(typed_exprs) => {
                self.lower_tuple(expr.id, typed_exprs, bind, &instantiations)
            }
            TypedExprKind::Block(typed_block) => {
                self.lower_block(typed_block, bind, &instantiations)
            }
            TypedExprKind::Call { callee, args, .. } => {
                self.lower_call(expr, callee, args, bind, &instantiations)
            }
            TypedExprKind::Member { receiver, label } => self.lower_member(
                expr,
                &Some(receiver.clone()),
                label,
                None,
                bind,
                &instantiations,
            ),
            TypedExprKind::ProtocolMember {
                receiver,
                label,
                witness,
            } => self.lower_member(
                expr,
                &Some(receiver.clone()),
                label,
                Some(*witness),
                bind,
                &instantiations,
            ),
            TypedExprKind::Func(typed_func) => {
                self.lower_func(typed_func, bind, &instantiations, FuncTermination::Return)
            }
            TypedExprKind::Variable(symbol) => {
                let (value, ty) = self.lower_variable(symbol, expr, &instantiations)?;
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
                self.lower_constructor(symbol, expr, bind, &instantiations)
            }
            TypedExprKind::If(cond, conseq, alt) => {
                self.lower_if_expr(cond, conseq, alt, bind, &instantiations)
            }
            TypedExprKind::Match(scrutinee, arms) => {
                self.lower_match(expr, scrutinee, arms, bind, &instantiations)
            }
            TypedExprKind::RecordLiteral { fields } => {
                self.lower_record_literal(expr, fields, bind, &instantiations)
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
        func: &TypedFunc<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (_val, _) = self.lower_func(
            func,
            bind,
            instantiations,
            FuncTermination::Continuation(func.name),
        )?;
        Ok((Value::Void, Ty::Void))
    }

    fn lower_effect_call(
        &mut self,
        expr: &TypedExpr<Ty>,
        _effect: &Symbol,
        args: &[TypedExpr<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let mut arg_vals = Vec::with_capacity(args.len());
        for arg in args {
            let (val, _ty) = self.lower_expr(arg, Bind::Fresh, instantiations)?;
            arg_vals.push(val);
        }

        let dest = self.ret(bind);

        let Some(handler_sym) = self.resolved_names.effect_handlers.get(&expr.id).copied() else {
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
            Symbol::Synthesized(self.symbols.next_synthesized(self.config.module_id));
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

    #[allow(clippy::todo)]
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_inline_ir(
        &mut self,
        expr: &TypedExpr<Ty>,
        instr: &TypedInlineIRInstruction<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let binds: Vec<_> = instr
            .binds
            .iter()
            .map(|b| self.lower_expr(b, Bind::Fresh, instantiations).map(|b| b.0))
            .try_collect()?;

        match &instr.kind {
            InlineIRInstructionKind::Constant { dest, ty, val } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
                let lhs = self.parsed_value(lhs, &binds);
                let rhs = self.parsed_value(rhs, &binds);
                self.push_instr(Instruction::Cmp {
                    dest,
                    ty: ty.clone(),
                    lhs,
                    rhs,
                    op: op.clone().into(),
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Add { dest, ty, a, b }
            | InlineIRInstructionKind::Sub { dest, ty, a, b }
            | InlineIRInstructionKind::Mul { dest, ty, a, b }
            | InlineIRInstructionKind::Div { dest, ty, a, b } => {
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                    meta: vec![InstructionMeta::Source(instr.id)].into(),
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Record { dest, ty, record } => {
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
                let ty = self.parsed_ty(ty, instr.id, instantiations);
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
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr, items))]
    fn lower_array(
        &mut self,
        expr: &TypedExpr<Ty>,
        items: &[TypedExpr<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let item_irs: Vec<(Value, Ty)> = items
            .iter()
            .map(|item| self.lower_expr(item, Bind::Fresh, instantiations))
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
        items: &[TypedExpr<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let item_irs: Vec<(Value, Ty)> = items
            .iter()
            .map(|expr| self.lower_expr(expr, Bind::Fresh, instantiations))
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
        expr: &TypedExpr<Ty>,
        string: &String,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let ret = self.ret(bind);
        let bytes = string.bytes().collect_vec();
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
        expr: &TypedExpr<Ty>,
        scrutinee: &TypedExpr<Ty>,
        arms: &[TypedMatchArm<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let result_type = arms.first().map(|a| a.body.ret.clone()).unwrap_or(Ty::Void);
        let Some(plan) = self.types.match_plans.get(&expr.id).cloned() else {
            self.lower_expr(scrutinee, Bind::Discard, instantiations)?;
            return Ok((Value::Void, result_type));
        };
        let produce_value = !matches!(bind, Bind::Discard);
        let result_register = if produce_value {
            self.ret(bind)
        } else {
            Register::DROP
        };

        let scrutinee_register = self.next_register();
        self.lower_expr(
            scrutinee,
            Bind::Assigned(scrutinee_register),
            instantiations,
        )?;

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
            if self.resolved_names.is_captured.contains(symbol) {
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
                let (arm_value, _arm_type) =
                    lowerer.lower_block(&arm.body, arm_bind, instantiations)?;
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
                let variants = self.types.catalog.variants.get(&symbol).ok_or_else(|| {
                    IRError::TypeNotFound(format!("missing enum variants for {symbol:?}"))
                })?;
                let label = self.label_from_name(name);
                let tag = variants.get_index_of(&label).ok_or_else(|| {
                    IRError::TypeNotFound(format!("missing enum variant {label:?} on {symbol:?}"))
                })? as i64;

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

        if self.resolved_names.is_captured.contains(&symbol) {
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
        expr: &TypedExpr<Ty>,
        fields: &[TypedRecordField<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let mut field_vals_by_label: FxHashMap<Label, (Value, Ty)> = FxHashMap::default();
        let mut field_labels = vec![];
        for field in fields.iter() {
            let (val, ty) = self.lower_expr(&field.value, Bind::Fresh, instantiations)?;
            field_vals_by_label.insert(field.name.clone(), (val, ty));
            field_labels.push(field.name.to_string());
        }

        let record_id = RecordId::Record(self.next_record_id);
        self.next_record_id += 1;
        self.record_labels.insert(record_id, field_labels);

        let dest = self.ret(bind);

        let ty = substitute(expr.ty.clone(), instantiations);

        // Check if this record literal is typed as a nominal struct
        if let Ty::Nominal { symbol, type_args } = &ty {
            let nominal = if let Some(module_id) = symbol.module_id()
                && module_id != self.config.module_id
            {
                self.config
                    .modules
                    .lookup_nominal(symbol)
                    .cloned()
                    .expect("didn't get external nominal")
            } else {
                self.types
                    .catalog
                    .nominals
                    .get(symbol)
                    .cloned()
                    .unwrap_or_else(|| unreachable!("didn't get nominal: {symbol:?}"))
            };
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
        expr: &TypedExpr<Ty>,
        bind: Bind,
        old_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let constructor_sym = *self
            .types
            .catalog
            .initializers
            .get(name)
            .unwrap_or_else(|| unreachable!("did not get inits for {name:?}"))
            .get(&Label::Named("init".into()))
            .unwrap_or_else(|| unreachable!("did not get init for {name:?}"));

        let init_entry = self
            .types
            .get_symbol(&constructor_sym)
            .cloned()
            .expect("did not get init entry");
        let (ty, mut instantiations) = self.specialize(&init_entry, expr.id)?;
        instantiations.extend(old_instantiations.clone());
        let ty = substitute(ty, &instantiations);
        let constructor_sym = self
            .monomorphize_name(constructor_sym, &instantiations)
            .symbol()
            .expect("did not get constructor sym");

        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty: ty.clone(),
            val: Value::Func(constructor_sym),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    #[allow(clippy::too_many_arguments)]
    fn lower_enum_constructor(
        &mut self,
        id: NodeID,
        enum_symbol: &Symbol,
        variant_name: &Label,
        arg_exprs: &[TypedExpr<Ty>],
        mut args: Vec<Value>,
        bind: Bind,
        old_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let constructor_sym = *self
            .types
            .catalog
            .variants
            .get(enum_symbol)
            .unwrap_or_else(|| panic!("did not get variants for {enum_symbol:?}"))
            .get(variant_name)
            .unwrap_or_else(|| panic!("didn't get {:?}", enum_symbol));

        let tag = self
            .types
            .catalog
            .variants
            .get(enum_symbol)
            .unwrap_or_else(|| panic!("did not get variants for {enum_symbol:?}"))
            .get_index_of(variant_name)
            .unwrap_or_else(|| panic!("did not get tag for {enum_symbol:?} {variant_name:?}"));

        let enum_entry = self
            .types
            .get_symbol(enum_symbol)
            .unwrap_or_else(|| panic!("did not get enum entry {enum_symbol:?}"))
            .clone();
        let (_, _ty_instantiations) = self.specialize(&enum_entry, id)?;
        let init_entry = self
            .types
            .get_symbol(&constructor_sym)
            .cloned()
            .expect("did not get enum constructor entry");
        let (_, mut instantiations) = self.specialize(&init_entry, id)?;
        instantiations.extend(old_instantiations.clone());

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
        expr: &TypedExpr<Ty>,
        receiver: &Option<Box<TypedExpr<Ty>>>,
        label: &Label,
        witness: Option<Symbol>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        if let Some(box receiver) = &receiver {
            if matches!(receiver.kind, TypedExprKind::Hole)
                && let Ty::Nominal { symbol, .. } = &expr.ty
                && self
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
                    instantiations,
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
                    instantiations,
                );
            }

            let reg = self.next_register();
            let member_bind = Bind::Assigned(reg);
            let (receiver_val, _) = self.lower_expr(receiver, member_bind, instantiations)?;
            let ty = expr.ty.clone();
            let dest = self.ret(bind);

            let (receiver_ty, _) = self.specialized_ty(receiver, instantiations)?;

            if let Ty::Nominal { symbol, .. } = &receiver_ty
                && let Some(methods) = self.types.catalog.instance_methods.get(symbol)
                && let Some(method) = methods.get(label).cloned()
            {
                tracing::debug!("lowering method: {label} {method:?}");

                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val: Value::Func(method),
                });
            } else if let Some(witness) =
                witness.or_else(|| self.witness_for(receiver, label, instantiations))
                && matches!(witness, Symbol::InstanceMethod(..))
            {
                tracing::debug!("lowering req {label} {witness:?}");
                self.push_instr(Instruction::Ref {
                    dest,
                    ty: ty.clone(),
                    val: Value::Func(witness),
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

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_variable(
        &mut self,
        name: &Symbol,
        expr: &TypedExpr<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (ty, instantiations) = self.specialized_ty(expr, instantiations)?;
        let monomorphized_ty = substitute(ty.clone(), &instantiations);

        let original_name_sym = name;

        // If we currently have a binding for this symbol, prefer that over just passing names around
        let needs_specialization = !(instantiations.ty.is_empty()
            && instantiations.row.is_empty()
            && instantiations.witnesses.is_empty());
        if self
            .current_func_mut()
            .bindings
            .contains_key(original_name_sym)
        {
            if matches!(monomorphized_ty, Ty::Func(..)) && needs_specialization {
                _ = self.monomorphize_name(*name, &instantiations);
            }
            return Ok((self.get_binding(original_name_sym).into(), ty));
        }

        // If it's a func we've registered, lower it with instantiations
        let (_, instantiations) = self.specialized_ty(expr, &instantiations)?;

        let ret = if matches!(monomorphized_ty, Ty::Func(..)) {
            let monomorphized_name = self
                .monomorphize_name(*name, &instantiations)
                .symbol()
                .expect("did not get symbol");

            // Check if this function has captures
            if let Some(captures) = self.resolved_names.captures.get(name).cloned()
                && !captures.is_empty()
            {
                let env: Vec<Value> = captures
                    .iter()
                    .map(
                        |cap| match self.current_func_mut().bindings.get(&cap.symbol).cloned() {
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
                    .collect();
                Value::Closure {
                    func: monomorphized_name,
                    env: env.into(),
                }
            } else {
                Value::Func(monomorphized_name)
            }
        } else {
            Value::Reg(self.get_binding(name).0)
        };

        Ok((ret, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    #[allow(clippy::too_many_arguments)]
    fn lower_constructor_call(
        &mut self,
        call_expr: &TypedExpr<Ty>,
        name: &Symbol,
        callee: &TypedExpr<Ty>,
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let record_dest = self.next_register();

        // Look up the initializer and specialize it using the already-computed instantiations
        let init_sym = self
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
            });

        let init_entry = self
            .types
            .get_symbol(&init_sym)
            .cloned()
            .expect("did not get init entry");
        let (init_ty, mut concrete_tys) = self.specialize(&init_entry, callee.id)?;
        concrete_tys.extend(instantiations.clone());
        let init_ty = substitute(init_ty, &concrete_tys);

        let properties = self
            .types
            .catalog
            .properties
            .get(name)
            .cloned()
            .unwrap_or_default();

        // Extract return type from the initializer function
        let mut params = init_ty.clone().uncurry_params();
        let ret = params.pop().expect("did not get init ret");

        self.push_instr(Instruction::Nominal {
            sym: *name,
            dest: record_dest,
            ty: ret.clone(),
            record: properties
                .iter()
                .map(|_| Value::Uninit)
                .collect::<Vec<_>>()
                .into(),
            meta: vec![InstructionMeta::Source(call_expr.id)].into(),
        });
        args.insert(0, record_dest.into());

        let call_instantiations = self.call_instantiations_for(call_expr, init_sym, instantiations);
        self.emit_specialized_call(
            call_expr,
            init_sym,
            dest,
            ret.clone(),
            args,
            call_instantiations,
        );

        Ok((dest.into(), ret))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, call_expr, callee, args, parent_instantiations))]
    fn lower_call(
        &mut self,
        call_expr: &TypedExpr<Ty>,
        callee: &TypedExpr<Ty>,
        args: &[TypedExpr<Ty>],
        bind: Bind,
        parent_instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let dest = self.ret(bind);

        if let TypedExprKind::Variable(name) = &callee.kind
            && name == &Symbol::PRINT
        {
            let arg = self.lower_expr(&args[0], Bind::Fresh, parent_instantiations)?;
            self.push_instr(Instruction::_Print { val: arg.0 });
            return Ok((Value::Void, Ty::Void));
        }

        let instantiations = parent_instantiations.clone();

        let ty = call_expr.ty.clone();
        let mut arg_vals = vec![];
        for arg in args {
            let (arg, _arg_ty) = self.lower_expr(arg, Bind::Fresh, &instantiations)?;
            arg_vals.push(arg);
        }

        if let TypedExprKind::Call {
            resolved: Some(target),
            ..
        } = &call_expr.kind
        {
            let call_instantiations =
                self.call_instantiations_for(call_expr, target.symbol, &instantiations);
            self.emit_specialized_call(
                call_expr,
                target.symbol,
                dest,
                ty.clone(),
                arg_vals,
                call_instantiations,
            );

            return Ok((dest.into(), ty));
        }

        if let TypedExprKind::Constructor(name, ..) = &callee.kind {
            return self.lower_constructor_call(
                call_expr,
                name,
                callee,
                arg_vals,
                dest,
                &instantiations,
            );
        }

        if let TypedExprKind::Member {
            receiver: box receiver,
            label: member,
        } = &callee.kind
        {
            return self.lower_method_call(
                call_expr,
                callee,
                receiver.clone(),
                member,
                None,
                args,
                arg_vals,
                dest,
                &instantiations,
            );
        }

        if let TypedExprKind::ProtocolMember {
            receiver: box receiver,
            label: member,
            witness,
        } = &callee.kind
        {
            return self.lower_method_call(
                call_expr,
                callee,
                receiver.clone(),
                member,
                Some(*witness),
                args,
                arg_vals,
                dest,
                &instantiations,
            );
        }

        if let TypedExprKind::Variable(name) = &callee.kind
            && !self.current_func_mut().bindings.contains_key(name)
        {
            let mut call_instantiations =
                self.call_instantiations_for(call_expr, *name, &instantiations);
            if call_instantiations.instantiations.ty.is_empty()
                && call_instantiations.instantiations.row.is_empty()
            {
                let inferred = self.infer_call_instantiations(*name, args, &call_expr.ty);
                call_instantiations.instantiations.extend(inferred);
            }
            self.emit_specialized_call(
                call_expr,
                *name,
                dest,
                ty.clone(),
                arg_vals,
                call_instantiations,
            );

            return Ok((dest.into(), ty));
        }

        let callee_ir = self.lower_expr(callee, Bind::Fresh, &instantiations)?.0;

        self.push_instr(Instruction::Call {
            dest,
            ty: ty.clone(),
            callee: callee_ir,
            args: arg_vals.into(),
            meta: vec![InstructionMeta::Source(call_expr.id)].into(),
        });

        Ok((dest.into(), ty))
    }

    #[allow(clippy::too_many_arguments)]
    #[instrument(level = tracing::Level::TRACE, skip(self, call_expr, callee_expr, receiver, arg_exprs, args, instantiations ))]
    fn lower_method_call(
        &mut self,
        call_expr: &TypedExpr<Ty>,
        callee_expr: &TypedExpr<Ty>,
        mut receiver: TypedExpr<Ty>,
        label: &Label,
        witness: Option<Symbol>,
        arg_exprs: &[TypedExpr<Ty>],
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (_, instantiations) = self.specialized_ty(callee_expr, instantiations)?;
        let (ty, mut instantiations) = self.specialized_ty(call_expr, &instantiations)?;

        if matches!(receiver.kind, TypedExprKind::Hole)
            && let Ty::Nominal { symbol, .. } = &call_expr.ty
            && self
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
                &instantiations,
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
                &instantiations,
            );
        }

        // Is this an instance method call on a constructor? If so we don't need
        // to prepend a self arg because it's passed explicitly (like Foo.bar(fizz) where
        // fizz == self)
        if let TypedExprKind::Constructor(_name, ..) = &receiver.kind {
            receiver = arg_exprs[0].clone();
        } else {
            let (receiver_ir, _) = self.lower_expr(&receiver, Bind::Fresh, &instantiations)?;
            args.insert(0, receiver_ir);
        }

        // If the receiver is a nominal type with type arguments (e.g. `Array<Int>`), extend the
        // current substitutions with the nominal’s own type-parameter substitutions so generic
        // method bodies (e.g. inline-IR `load Element`) monomorphize correctly.
        let receiver_ty = substitute(receiver.ty.clone(), &instantiations);
        if let Ty::Nominal { symbol, type_args } = &receiver_ty {
            let nominal = if let Some(module_id) = symbol.module_id()
                && module_id != self.config.module_id
            {
                self.config
                    .modules
                    .lookup_nominal(symbol)
                    .cloned()
                    .expect("didn't get external nominal")
            } else {
                self.types
                    .catalog
                    .nominals
                    .get(symbol)
                    .cloned()
                    .unwrap_or_else(|| unreachable!("didn't get nominal: {symbol:?}"))
            };
            instantiations.ty.extend(nominal.substitutions(type_args));
        }

        let (_method_sym, val, ty) = if let Some(method_sym) =
            self.lookup_instance_method(&receiver, label, &instantiations)?
        {
            let call_instantiations =
                self.call_instantiations_for(call_expr, method_sym, &instantiations);
            self.emit_specialized_call(
                call_expr,
                method_sym,
                dest,
                ty.clone(),
                args,
                call_instantiations,
            );

            (method_sym, dest.into(), ty)
        } else if let Some(witness) =
            witness.or_else(|| self.witness_for(&receiver, label, &instantiations))
        {
            let call_instantiations =
                self.call_instantiations_for(call_expr, witness, &instantiations);
            self.emit_specialized_call(
                call_expr,
                witness,
                dest,
                ty.clone(),
                args,
                call_instantiations,
            );

            (witness, dest.into(), ty)
        } else {
            tracing::warn!(
                "No witness found for {:?} in {:?} ({:?}).",
                label,
                receiver,
                receiver.ty.clone()
            );

            return Err(IRError::WitnessNotFound(format!(
                "No witness found for {label:?} in {receiver:?} ({:?}). Instantiations: {instantiations:?}",
                receiver.ty
            )));
        };

        // Go through the method and make sure all witnesses are resolved inside it

        Ok((val, ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func.name = %func.name))]
    fn lower_func(
        &mut self,
        func: &TypedFunc<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
        terminates_with: FuncTermination,
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_symbol(&func.name)?;

        let (mut param_tys, mut ret_ty) = uncurry_function(ty);

        // Track if this is a handler (needs continuation param)
        let is_handler = matches!(terminates_with, FuncTermination::Continuation(..));

        // Do we have captures? If so this is a closure
        let capture_env = if let Some(captures) =
            self.resolved_names.captures.get(&func.name).cloned()
            && !captures.is_empty()
        {
            let mut env_fields = vec![];
            for capture in captures {
                let ty = self
                    .ty_from_symbol(&capture.symbol)
                    .expect("didn't get capture ty")
                    .clone();
                let is_handler = self
                    .resolved_names
                    .handler_symbols
                    .contains(&capture.symbol);
                // Global functions are resolved by symbol; don't treat them as captured env fields.
                if matches!(capture.symbol, Symbol::Global(_))
                    && matches!(ty, Ty::Func(..))
                    && !is_handler
                {
                    continue;
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
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
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
            },
        );

        // Finalize any pending continuations
        for (continuation, parent_name, _parent_dest) in
            std::mem::take(&mut self.pending_continuations)
        {
            // Register the continuation symbol name
            self.resolved_names.symbol_names.insert(
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
        }

        Ok((func_val, func_ty))
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

        let ret = f(self);

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
            tracing::error!("trying to overwrite terminator");
            return;
        }
        block.terminator = terminator;
    }

    fn insert_binding(&mut self, symbol: Symbol, binding: Binding<Ty>) {
        self.current_func_mut().bindings.insert(symbol, binding);
    }

    fn get_binding(&mut self, symbol: &Symbol) -> Register {
        let binding = self
            .current_func_mut()
            .bindings
            .get(symbol)
            .cloned()
            .unwrap_or_else(|| panic!("did not get binding for {symbol:?}"));
        let ty = self
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

    fn find_function(&self, symbol: &Symbol) -> Option<&PolyFunction> {
        let module_id = symbol.module_id().unwrap_or(ModuleId::Current);
        if module_id == self.config.module_id || (module_id == ModuleId::Current) {
            self.functions.get(symbol)
        } else {
            let program = self.config.modules.program_for(module_id)?;
            program.polyfunctions.get(symbol)
        }
    }

    /// Check to see if this symbol calls any symbols we don't have.
    ///
    /// Returns the monomorphized `Name` for `symbol` under `instantiations` when the symbol’s body
    /// can be found (either in the current module or an imported module).
    fn check_import(&mut self, symbol: &Symbol, instantiations: &Substitutions) -> Option<Name> {
        let func = self.find_function(symbol).cloned()?;

        let name = self.monomorphize_name(*symbol, instantiations);
        self.functions.insert(*symbol, func.clone());

        // Recursively import any functions this function calls
        let callees: Vec<Symbol> = func
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instr| {
                if let Instruction::Call {
                    callee:
                        Value::Func(sym)
                        | Value::Ref(Reference::Func(sym))
                        | Value::Ref(Reference::Closure(sym, ..)),
                    ..
                } = instr
                {
                    Some(*sym)
                } else {
                    None
                }
            })
            .collect();

        for callee_sym in callees {
            // Already imported, avoid infinite recursion
            if self.functions.contains_key(&callee_sym) {
                continue;
            }
            _ = self.check_import(&callee_sym, instantiations);
        }

        Some(name)
    }

    fn resolve_name(&self, sym: &Symbol) -> Option<&str> {
        if matches!(sym, Symbol::Main) {
            return Some("main");
        }

        if matches!(sym, Symbol::Library) {
            return Some("lib");
        }

        if let Some(string) = self.resolved_names.symbol_names.get(sym) {
            return Some(string);
        }

        if let Some(string) = self.config.modules.resolve_name(sym) {
            return Some(string);
        }

        None
    }

    fn monomorphize_name(&mut self, symbol: Symbol, instantiations: &Substitutions) -> Name {
        let name = Name::Resolved(
            symbol,
            self.resolve_name(&symbol)
                .unwrap_or_else(|| {
                    unreachable!(
                        "did not get symbol name: {symbol:?} in {:?}",
                        self.resolved_names.symbol_names
                    )
                })
                .to_string(),
        );

        let key = SpecializationKey::new(instantiations);
        if key.is_empty() {
            return name;
        }

        if let Some(existing) = self
            .specialization_intern
            .get(&symbol)
            .and_then(|m| m.get(&key))
            .copied()
        {
            let parts = key.parts();
            let new_name_str = format!("{}[{}]", name.name_str(), parts.join(", "));
            return Name::Resolved(existing, new_name_str);
        }

        let new_symbol: Symbol = self.symbols.next_synthesized(self.config.module_id).into();
        self.resolved_names
            .symbol_names
            .insert(new_symbol, name.name_str());
        let parts = key.parts();
        let new_name_str = format!("{}[{}]", name.name_str(), parts.join(", "));
        let new_name = Name::Resolved(new_symbol, new_name_str.clone());

        tracing::trace!("monomorphized {name:?} -> {new_name:?}");
        self.resolved_names
            .symbol_names
            .insert(new_symbol, new_name_str);

        self.specialization_intern
            .entry(symbol)
            .or_default()
            .insert(key, new_symbol);

        self.specializations
            .entry(name.symbol().expect("name not resolved"))
            .or_default()
            .push(Specialization {
                name: new_symbol,
                substitutions: instantiations.clone(),
            });

        new_name
    }

    fn resolve_call_symbol(
        &mut self,
        callee_sym: Symbol,
        call_instantiations: &CallInstantiations,
    ) -> Symbol {
        if self.call_instantiations_are_concrete(call_instantiations) {
            let substitutions = self.substitutions_from_call_instantiations(call_instantiations);
            let name = self
                .check_import(&callee_sym, &substitutions)
                .unwrap_or_else(|| self.monomorphize_name(callee_sym, &substitutions));
            name.symbol().expect("did not get call symbol")
        } else {
            _ = self.check_import(&callee_sym, &Default::default());
            callee_sym
        }
    }

    fn emit_specialized_call(
        &mut self,
        call_expr: &TypedExpr<Ty>,
        callee_sym: Symbol,
        dest: Register,
        ty: Ty,
        args: Vec<Value>,
        call_instantiations: CallInstantiations,
    ) -> Symbol {
        let resolved_callee = self.resolve_call_symbol(callee_sym, &call_instantiations);
        let mut meta_items = vec![InstructionMeta::Source(call_expr.id)];
        if !call_instantiations.is_empty() {
            meta_items.push(InstructionMeta::CallInstantiations(call_instantiations));
        }

        self.push_instr(Instruction::Call {
            dest,
            ty,
            callee: Value::Func(resolved_callee),
            args: args.into(),
            meta: meta_items.into(),
        });

        resolved_callee
    }

    fn call_instantiations_for(
        &mut self,
        call_expr: &TypedExpr<Ty>,
        callee: Symbol,
        substitutions: &Substitutions,
    ) -> CallInstantiations {
        let mut instantiations = call_expr.instantiations.clone();
        instantiations.ty = instantiations
            .ty
            .into_iter()
            .map(|(param, ty)| (param, substitute(ty, substitutions)))
            .collect();
        instantiations.row = instantiations
            .row
            .into_iter()
            .map(|(param, row)| (param, substitute_row(row, substitutions)))
            .collect();
        if let TypedExprKind::Call { type_args, .. } = &call_expr.kind
            && !type_args.is_empty()
            && let Some(params) = self.type_params_for_symbol(callee)
        {
            for (param_id, arg_ty) in params.iter().zip(type_args.iter()) {
                let arg_ty = substitute(arg_ty.clone(), substitutions);
                instantiations.ty.entry(*param_id).or_insert_with(|| arg_ty);
            }
        }
        if instantiations.ty.is_empty() && instantiations.row.is_empty() {
            if let Some(params) = self.type_params_for_symbol(callee) {
                for param_id in params {
                    let key = Ty::Param(param_id);
                    if let Some(ty) = substitutions.ty.get(&key) {
                        instantiations.ty.insert(param_id, ty.clone());
                    }
                }
            } else {
                for (key, ty) in substitutions.ty.iter() {
                    let Ty::Param(param_id) = key else {
                        continue;
                    };
                    instantiations.ty.insert(*param_id, ty.clone());
                }
            }
            for (row_param_id, row) in substitutions.row.iter() {
                instantiations
                    .row
                    .entry(*row_param_id)
                    .or_insert_with(|| row.clone());
            }
        }
        instantiations
            .witnesses
            .extend(substitutions.witnesses.iter().map(|(k, v)| (*k, *v)));

        CallInstantiations {
            callee,
            instantiations,
        }
    }

    fn infer_call_instantiations(
        &mut self,
        callee: Symbol,
        args: &[TypedExpr<Ty>],
        ret_ty: &Ty,
    ) -> InstantiationSubstitutions<Ty> {
        let entry = self
            .types
            .get_symbol(&callee)
            .cloned()
            .or_else(|| self.config.modules.lookup(&callee));

        let Some(entry) = entry else {
            return InstantiationSubstitutions::default();
        };

        let signature = match entry {
            TypeEntry::Mono(ty) => ty,
            TypeEntry::Poly(scheme) => scheme.ty,
        };

        let (params, returns) = uncurry_function(signature);
        let mut instantiations = InstantiationSubstitutions::default();
        for (expected, arg) in params.iter().zip(args.iter()) {
            collect_instantiations(expected, &arg.ty, &mut instantiations);
        }
        collect_instantiations(&returns, ret_ty, &mut instantiations);
        instantiations
    }

    fn call_instantiations_are_concrete(&self, instantiations: &CallInstantiations) -> bool {
        instantiations
            .instantiations
            .ty
            .values()
            .all(is_concrete_ty)
            && instantiations
                .instantiations
                .row
                .iter()
                .all(|(param, row)| *row == Row::Param(*param) || is_concrete_row(row))
    }

    fn substitutions_from_call_instantiations(
        &self,
        instantiations: &CallInstantiations,
    ) -> Substitutions {
        let mut substitutions = Substitutions::default();
        for (param_id, ty) in &instantiations.instantiations.ty {
            substitutions.ty.insert(Ty::Param(*param_id), ty.clone());
        }
        for (row_param_id, row) in &instantiations.instantiations.row {
            substitutions.row.insert(*row_param_id, row.clone());
        }
        substitutions.witnesses.extend(
            instantiations
                .instantiations
                .witnesses
                .iter()
                .map(|(k, v)| (*k, *v)),
        );
        substitutions
    }

    fn type_params_for_symbol(&self, symbol: Symbol) -> Option<Vec<TypeParamId>> {
        self.types
            .get_symbol(&symbol)
            .and_then(Self::type_params_from_entry)
            .filter(|params| !params.is_empty())
            .or_else(|| {
                self.config
                    .modules
                    .lookup(&symbol)
                    .as_ref()
                    .and_then(Self::type_params_from_entry)
                    .filter(|params| !params.is_empty())
            })
            .or_else(|| self.func_foralls.get(&symbol).cloned())
    }

    fn type_params_from_entry(entry: &TypeEntry) -> Option<Vec<TypeParamId>> {
        let TypeEntry::Poly(scheme) = entry else {
            return None;
        };

        Some(
            scheme
                .foralls
                .iter()
                .filter_map(|forall| match forall {
                    ForAll::Ty(id) => Some(*id),
                    _ => None,
                })
                .collect(),
        )
    }

    fn collect_func_foralls(ast: &TypedAST<Ty>) -> FxHashMap<Symbol, Vec<TypeParamId>> {
        let mut collector = FuncForallsCollector::new();
        ast.drive(&mut collector);
        collector.map
    }

    fn parsed_ty(&mut self, ty: &TypeAnnotation, id: NodeID, instantiations: &Substitutions) -> Ty {
        let sym = ty.symbol().expect("did not get ty symbol");
        let entry = self
            .types
            .types_by_symbol
            .get(&sym)
            .cloned()
            .expect("did not get entry");
        let (ty, _) = self
            .specialize(&entry, id)
            .expect("unable to specialize ty");
        substitute(ty, instantiations)
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

    fn lookup_instance_method(
        &mut self,
        expr: &TypedExpr<Ty>,
        label: &Label,
        instantiations: &Substitutions,
    ) -> Result<Option<Symbol>, IRError> {
        let ty = expr.ty.clone();

        let symbol = match ty {
            Ty::Primitive(primitive) => primitive,
            Ty::Nominal { symbol, .. } => symbol,
            _ => {
                let specialized = self.specialized_ty(expr, instantiations)?.0;
                let Ty::Nominal { symbol, .. } = specialized else {
                    return Ok(None);
                };

                symbol
            }
        };

        if let Some(sym) = self.config.modules.lookup_concrete_member(&symbol, label)
        // && matches!(sym, Symbol::InstanceMethod(..))
        {
            Ok(Some(sym))
        } else if let Some(methods) = self.types.catalog.instance_methods.get(&symbol)
            && let Some(method) = methods.get(label)
        {
            Ok(Some(*method))
        } else {
            Ok(None)
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn extend_instantiations_from_expr(
        &self,
        instantiations: &mut Substitutions,
        expr: &TypedExpr<Ty>,
    ) {
        for (param_id, concrete_ty) in &expr.instantiations.ty {
            instantiations
                .ty
                .insert(Ty::Param(*param_id), concrete_ty.clone());
        }
        for (row_param_id, row) in &expr.instantiations.row {
            instantiations.row.insert(*row_param_id, row.clone());
        }
        instantiations
            .witnesses
            .extend(expr.instantiations.witnesses.iter().map(|(k, v)| (*k, *v)));
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn specialized_ty(
        &mut self,
        expr: &TypedExpr<Ty>,
        instantiations: &Substitutions,
    ) -> Result<(Ty, Substitutions), IRError> {
        let symbol = match &expr.kind {
            TypedExprKind::Variable(name) => *name,
            TypedExprKind::Func(func) => func.name,
            TypedExprKind::Constructor(name, ..) => *name,
            TypedExprKind::Member { receiver, label } => {
                let receiver_ty = substitute(receiver.ty.clone(), instantiations);
                let receiver_sym = match &receiver_ty {
                    Ty::Constructor { name, .. } => name.symbol().expect("didn't get sym"),
                    _ => {
                        let Some(sym) = self.symbol_for_ty(&receiver_ty) else {
                            return Ok((expr.ty.clone(), Default::default()));
                        };
                        sym
                    }
                };

                if let Some((member, _)) = self.types.catalog.lookup_member(&receiver_sym, label) {
                    member
                } else if let Some(member) = self.config.modules.lookup_member(&receiver_sym, label)
                {
                    member
                } else {
                    return Ok((expr.ty.clone(), Default::default()));
                }
            }
            _ => {
                tracing::trace!("expr has no substitutions: {expr:?}");
                let mut instantiations = instantiations.clone();
                self.extend_instantiations_from_expr(&mut instantiations, expr);
                return Ok((expr.ty.clone(), instantiations));
            }
        };

        let entry = self
            .types
            .get_symbol(&symbol)
            .cloned()
            .ok_or(IRError::TypeNotFound(format!(
                "no type found for {symbol:?}"
            )))?;

        let (ty, substitutions) = self.specialize(&entry, expr.id)?;
        _ = self.monomorphize_name(symbol, &substitutions);

        let mut instantiations = instantiations.clone();
        instantiations.extend(substitutions);
        self.extend_instantiations_from_expr(&mut instantiations, expr);

        Ok((ty, instantiations))
    }

    #[instrument(skip(self, entry))]
    fn specialize(
        &mut self,
        entry: &TypeEntry,
        id: NodeID,
    ) -> Result<(Ty, Substitutions), IRError> {
        match entry {
            TypeEntry::Mono(ty) => Ok((ty.clone(), Default::default())),
            TypeEntry::Poly(scheme) => {
                let substitutions = Substitutions::default();
                let ty = substitute(scheme.ty.clone(), &substitutions);
                Ok((ty, substitutions))
            }
        }
    }

    #[instrument(skip(self), ret)]
    fn witness_for(
        &mut self,
        receiver: &TypedExpr<Ty>,
        label: &Label,
        instantiations: &Substitutions,
    ) -> Option<Symbol> {
        // First try with any known type substitutions (important for `Self`-like params).
        let receiver_ty = substitute(receiver.ty.clone(), instantiations);

        // Concrete receiver: proceed as before.
        if let Some(sym) = self.symbol_for_ty(&receiver_ty)
            && let Some(methods) = self.types.catalog.instance_methods.get(&sym)
            && let Some(witness) = methods.get(label)
        {
            return Some(*witness);
        } else if let Ty::Param(param_id) = receiver_ty {
            // Abstract receiver (e.g. protocol `Self`): use the current function’s Scheme
            // predicates to find a constraining protocol, then resolve the member against
            // that protocol (including transitive superprotocol lookup).
            let current_func_sym = self.current_func_mut().symbol;
            if let Some(TypeEntry::Poly(scheme)) = self.types.get_symbol(&current_func_sym) {
                for pred in &scheme.predicates {
                    if let Predicate::Conforms { param, protocol_id } = pred
                        && *param == param_id
                    {
                        let proto = Symbol::Protocol(*protocol_id);
                        if let Some((member, _src)) =
                            self.types.catalog.lookup_member(&proto, label)
                        {
                            return Some(member);
                        }
                    }
                }
            }
            return None;
        }

        let sym = self.symbol_for_ty(&receiver.ty)?;

        // See if there's a witness
        if let Some(methods) = self.types.catalog.instance_methods.get(&sym)
            && let Some(witness) = methods.get(label)
        {
            return Some(*witness);
        }

        let conformances = self
            .types
            .catalog
            .conformances
            .values()
            .filter(|c| c.conforming_id == sym)
            .collect_vec();

        if conformances.is_empty() {
            return None;
        }

        for conformance in conformances {
            if let Some(witness) = conformance.witnesses.methods.get(label).copied() {
                _ = self.check_import(&witness, instantiations);
                return Some(witness);
            }

            // See if there's a default method
            let Some(member) = self
                .types
                .catalog
                .instance_methods
                .entry(Symbol::Protocol(conformance.protocol_id))
                .or_default()
                .get(label)
                .copied()
                .or_else(|| {
                    self.config
                        .modules
                        .lookup_concrete_member(&Symbol::Protocol(conformance.protocol_id), label)
                })
            else {
                continue;
            };

            _ = self.check_import(&member, instantiations);
            let _m = self.monomorphize_name(member, instantiations);

            return Some(member);
        }

        None
    }

    fn symbol_for_ty(&self, ty: &Ty) -> Option<Symbol> {
        match ty {
            Ty::Primitive(symbol) => Some(*symbol),
            Ty::Nominal { symbol, .. } => Some(*symbol),
            _ => None,
        }
    }

    fn field_index(&self, receiver_ty: &Ty, label: &Label) -> Label {
        match receiver_ty {
            Ty::Record(_, row) if let Some(idx) = row.close().get_index_of(label) => {
                Label::Positional(idx)
            }
            Ty::Nominal { symbol, .. }
                if let Some(idx) = self
                    .types
                    .catalog
                    .nominals
                    .get(symbol)
                    .expect("didn't find nominal")
                    .properties
                    .get_index_of(label) =>
            {
                Label::Positional(idx)
            }
            _ => panic!("unable to determine field index of {receiver_ty}.{label}"),
        }
    }

    fn label_from_name(&self, name: &str) -> Label {
        name.parse()
            .unwrap_or_else(|_| Label::Named(name.to_string()))
    }

    fn ty_from_symbol(&self, symbol: &Symbol) -> Result<Ty, IRError> {
        match self.types.get_symbol(symbol) {
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

pub(crate) fn substitute(ty: Ty, substitutions: &Substitutions) -> Ty {
    match ty {
        Ty::Primitive(..) => ty,
        Ty::Param(type_param_id) => substitutions
            .ty
            .get(&ty)
            .unwrap_or_else(|| {
                tracing::trace!("didn't find id {type_param_id:?} in {substitutions:?}");
                &ty
            })
            .clone(),
        Ty::Constructor {
            name,
            params,
            box ret,
        } => Ty::Constructor {
            name,
            params: params
                .into_iter()
                .map(|p| substitute(p, substitutions))
                .collect(),
            ret: substitute(ret, substitutions).into(),
        },
        Ty::Func(box param, box ret, box effects) => Ty::Func(
            substitute(param, substitutions).into(),
            substitute(ret, substitutions).into(),
            substitute_row(effects, substitutions).into(),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .into_iter()
                .map(|i| substitute(i, substitutions))
                .collect(),
        ),
        Ty::Record(sym, box row) => Ty::Record(sym, substitute_row(row, substitutions).into()),
        Ty::Nominal { symbol, type_args } => Ty::Nominal {
            symbol,
            type_args: type_args
                .into_iter()
                .map(|a| substitute(a, substitutions))
                .collect(),
        },
    }
}

pub(crate) fn substitute_row(row: Row, substitutions: &Substitutions) -> Row {
    match row {
        Row::Empty => row,
        Row::Param(id) => substitutions.row.get(&id).unwrap_or(&row).clone(),
        Row::Extend { box row, label, ty } => Row::Extend {
            row: substitute_row(row, substitutions).into(),
            label,
            ty: substitute(ty, substitutions),
        },
    }
}

pub(crate) fn is_concrete_ty(ty: &Ty) -> bool {
    match ty {
        Ty::Primitive(..) => true,
        Ty::Param(..) => false,
        Ty::Constructor { params, ret, .. } => {
            params.iter().all(is_concrete_ty) && is_concrete_ty(ret)
        }
        Ty::Func(param, ret, effects) => {
            is_concrete_ty(param) && is_concrete_ty(ret) && is_concrete_row(effects)
        }
        Ty::Tuple(items) => items.iter().all(is_concrete_ty),
        Ty::Record(_, row) => is_concrete_row(row),
        Ty::Nominal { type_args, .. } => type_args.iter().all(is_concrete_ty),
    }
}

pub(crate) fn is_concrete_row(row: &Row) -> bool {
    match row {
        Row::Empty => true,
        Row::Param(..) => false,
        Row::Extend { row, ty, .. } => is_concrete_row(row) && is_concrete_ty(ty),
    }
}

fn is_main_func(node: &TypedDecl<Ty>, symbol_names: &FxHashMap<Symbol, String>) -> bool {
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
