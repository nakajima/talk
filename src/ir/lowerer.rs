use std::fmt::Display;

use crate::compiling::driver::{CompilationMode, DriverConfig};
use crate::compiling::module::ModuleId;
use crate::ir::basic_block::{Phi, PhiSource};
use crate::ir::instruction::CmpOperator;
use crate::ir::ir_ty::IrTy;
use crate::ir::monomorphizer::uncurry_function;
use crate::ir::value::{Addr, Reference};
use crate::label::Label;
use crate::name_resolution::name_resolver::ResolvedNames;
use crate::name_resolution::symbol::{
    GlobalId, InitializerId, InstanceMethodId, StaticMethodId, Symbols,
};
use crate::node_kinds::inline_ir_instruction::{InlineIRInstructionKind, TypedInlineIRInstruction};
use crate::node_kinds::type_annotation::TypeAnnotation;
use crate::types::infer_row::RowParamId;
use crate::types::row::Row;
use crate::types::type_session::TypeDefKind;
use crate::types::typed_ast::{
    TypedAST, TypedBlock, TypedDecl, TypedDeclKind, TypedExpr, TypedExprKind, TypedFunc,
    TypedMatchArm, TypedNode, TypedPattern, TypedRecordField, TypedStmt, TypedStmtKind,
};
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
    node_kinds::pattern::PatternKind,
    types::{
        scheme::ForAll,
        ty::Ty,
        type_session::{TypeEntry, Types},
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
    name: Symbol,
    current_block_idx: Vec<usize>,
    blocks: Vec<BasicBlock<Ty>>,
    pub registers: RegisterAllocator,
    bindings: FxHashMap<Symbol, Binding<Ty>>,
}

impl CurrentFunction {
    fn new(name: Symbol) -> Self {
        CurrentFunction {
            name,
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
            IrTy::RawPtr => Value::RawPtr(Addr(usize::from_le_bytes(bytes.try_into().unwrap()))),
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
pub(super) struct Substitutions {
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

#[derive(Debug, Clone)]
pub enum Binding<T> {
    Register(u32),
    Pointer(Value),
    Capture { index: usize, ty: T },
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

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer<'a> {
    pub(super) ast: &'a mut TypedAST<Ty>,
    pub(super) types: &'a mut Types,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,
    pub(super) config: &'a DriverConfig,

    symbols: &'a mut Symbols,
    symbol_names: &'a mut FxHashMap<Symbol, String>,
    resolved_names: &'a ResolvedNames,
    pub(super) specializations: IndexMap<Symbol, Vec<Specialization>>,
    static_memory: StaticMemory,
}

#[allow(clippy::panic)]
#[allow(clippy::expect_used)]
impl<'a> Lowerer<'a> {
    pub fn new(
        ast: &'a mut TypedAST<Ty>,
        types: &'a mut Types,
        symbols: &'a mut Symbols,
        symbol_names: &'a mut FxHashMap<Symbol, String>,
        resolved_names: &'a ResolvedNames,
        config: &'a DriverConfig,
    ) -> Self {
        Self {
            ast,
            types,
            functions: Default::default(),
            current_function_stack: Default::default(),
            symbols,
            symbol_names,
            specializations: Default::default(),
            static_memory: Default::default(),
            config,
            resolved_names,
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.ast.roots().is_empty() {
            return Ok(Program::default());
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
            self.check_import(&sym);
        }

        let static_memory = std::mem::take(&mut self.static_memory);
        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
            polyfunctions: monomorphizer.functions,
            static_memory,
        })
    }

    fn lower_main(&mut self) {
        // Do we have a main func?
        let has_main_func = self
            .ast
            .decls
            .iter()
            .any(|d| is_main_func(d, self.symbol_names));
        if !has_main_func {
            let main_symbol = Symbol::Synthesized(self.symbols.next_synthesized(ModuleId::Current));
            let mut ret_ty = Ty::Void;

            let func = TypedFunc::<Ty> {
                name: main_symbol,
                foralls: Default::default(),
                params: Default::default(),
                body: TypedBlock {
                    body: {
                        // Only include top-level statements (expressions) in the synthesized main,
                        // not declarations. Declarations are lowered separately via the normal
                        // AST iteration.
                        let stmts: Vec<TypedNode<Ty>> = self
                            .ast
                            .stmts
                            .iter()
                            .map(|a| TypedNode::Stmt(a.clone()))
                            .collect();

                        if let Some(last) = stmts.last() {
                            ret_ty = last.ty();
                        }

                        stmts
                    },
                    id: NodeID(FileID(0), 0),
                    ret: Ty::Void,
                },
                ret: Ty::Void,
            };

            #[allow(clippy::unwrap_used)]
            self.ast.decls.push(TypedDecl {
                id: NodeID(FileID(0), 0),
                ty: Ty::Func(Ty::Void.into(), Ty::Void.into()),
                kind: TypedDeclKind::Let {
                    pattern: TypedPattern {
                        id: NodeID(FileID(0), 0),
                        ty: Ty::Func(Ty::Void.into(), Ty::Void.into()),
                        kind: PatternKind::Bind(Name::Resolved(Symbol::Main, "main".into())),
                    },
                    ty: Ty::Func(Ty::Void.into(), Ty::Void.into()),
                    initializer: Some(TypedExpr {
                        id: NodeID(FileID(0), 0),
                        ty: Ty::Func(Ty::Void.into(), Ty::Void.into()),
                        kind: TypedExprKind::Func(func),
                    }),
                },
            });

            self.types.define(
                main_symbol,
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into())),
            );

            self.symbol_names
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
                let bind = self.lower_pattern(pattern)?;
                if let Some(initializer) = initializer {
                    self.lower_expr(initializer, bind, instantiations)?;
                }
            }
            TypedDeclKind::StructDef {
                symbol,
                initializers,
                instance_methods,
                ..
            } => {
                for initializer in initializers.values() {
                    self.lower_init(decl, symbol, initializer, instantiations)?;
                }

                for method in instance_methods.values() {
                    self.lower_method(method, instantiations)?;
                }
            }
            TypedDeclKind::Extend {
                instance_methods, ..
            } => {
                for method in instance_methods.values() {
                    self.lower_method(method, instantiations)?;
                }
            }
            TypedDeclKind::EnumDef {
                instance_methods, ..
            } => {
                for method in instance_methods.values() {
                    self.lower_method(method, instantiations)?;
                }
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
        self.lower_func(func, Bind::Discard, instantiations)
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
            self.insert_binding(param.name, register.into());
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
            *name,
            PolyFunction {
                name: *name,
                params: param_values,
                blocks: current_function.blocks,
                ty: Ty::Func(Box::new(param_ty.clone()), Box::new(ret_ty.clone())),
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
            TypedStmtKind::Loop(cond, typed_block) => {
                self.lower_loop(&Some(cond.clone()), typed_block, instantiations)
            }
            #[warn(clippy::todo)]
            TypedStmtKind::Break => todo!(),
        }
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

    #[instrument(level = tracing::Level::TRACE, skip(self, cond, conseq, alt))]
    fn lower_if_stmt(
        &mut self,
        cond: &TypedExpr<Ty>,
        conseq: &TypedBlock<Ty>,
        alt: &Option<TypedBlock<Ty>>,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let cond_ir = self.lower_expr(cond, Bind::Fresh, instantiations)?;

        let conseq_block_id = self.new_basic_block();
        let join_block_id = self.new_basic_block();

        self.in_basic_block(conseq_block_id, |lowerer| {
            lowerer.lower_block(conseq, Bind::Discard, instantiations)?;
            lowerer.push_terminator(Terminator::Jump { to: join_block_id });
            Ok(())
        })?;

        let else_id = if let Some(alt) = alt {
            let alt_block_id = self.new_basic_block();
            self.in_basic_block(alt_block_id, |lowerer| {
                lowerer.lower_block(alt, Bind::Discard, instantiations)?;
                lowerer.push_terminator(Terminator::Jump { to: join_block_id });
                Ok(())
            })?;
            alt_block_id
        } else {
            join_block_id
        };

        self.push_terminator(Terminator::Branch {
            cond: cond_ir.0,
            conseq: conseq_block_id,
            alt: else_id,
        });

        self.set_current_block(join_block_id);

        Ok((Value::Void, Ty::Void))
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

    // #[instrument(level = tracing::Level::TRACE, skip(self, pattern), fields(pattern.id = %pattern.id))]
    fn lower_pattern(&mut self, pattern: &TypedPattern<Ty>) -> Result<Bind, IRError> {
        match &pattern.kind {
            PatternKind::Bind(name) => {
                let symbol = name.symbol().expect("name not resolved");
                let value = if self.resolved_names.is_captured.contains(&symbol) {
                    let ty = self
                        .ty_from_symbol(&symbol)
                        .expect("did not get ty for sym");
                    let heap_addr = self.next_register();
                    self.push_instr(Instruction::Alloc {
                        dest: heap_addr,
                        ty,
                        count: 1.into(),
                    });
                    self.insert_binding(symbol, Binding::Pointer(heap_addr.into()));
                    Bind::Indirect(heap_addr, symbol)
                } else {
                    let val = self.next_register();

                    self.insert_binding(symbol, val.into());
                    Bind::Assigned(val)
                };

                Ok(value)
            }
            #[allow(clippy::todo)]
            PatternKind::LiteralInt(_) => todo!(),
            #[allow(clippy::todo)]
            PatternKind::LiteralFloat(_) => todo!(),
            #[allow(clippy::todo)]
            PatternKind::LiteralTrue => todo!(),
            #[allow(clippy::todo)]
            PatternKind::LiteralFalse => todo!(),
            #[allow(clippy::todo)]
            PatternKind::Tuple(..) => todo!(),
            PatternKind::Wildcard => Ok(Bind::Discard),
            #[allow(clippy::todo)]
            PatternKind::Variant { .. } => todo!(),
            #[allow(clippy::todo)]
            PatternKind::Record { .. } => todo!(),
            #[allow(clippy::todo)]
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr), fields(expr.id = %expr.id))]
    fn lower_expr(
        &mut self,
        expr: &TypedExpr<Ty>,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let (value, ty) = match &expr.kind {
            TypedExprKind::Hole => Err(IRError::TypeNotFound(format!("nope"))),
            TypedExprKind::InlineIR(inline_irinstruction) => {
                self.lower_inline_ir(inline_irinstruction, bind, instantiations)
            }
            TypedExprKind::LiteralArray(typed_exprs) => {
                self.lower_array(expr, typed_exprs, bind, instantiations)
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
            TypedExprKind::LiteralString(val) => self.lower_string(expr, val, bind, instantiations),
            TypedExprKind::Tuple(typed_exprs) => {
                self.lower_tuple(expr.id, typed_exprs, bind, instantiations)
            }
            TypedExprKind::Block(typed_block) => {
                self.lower_block(typed_block, bind, instantiations)
            }
            TypedExprKind::Call { callee, args, .. } => {
                self.lower_call(expr, callee, args, bind, instantiations)
            }
            TypedExprKind::Member { receiver, label } => self.lower_member(
                expr,
                &Some(receiver.clone()),
                label,
                None,
                bind,
                instantiations,
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
                instantiations,
            ),
            TypedExprKind::Func(typed_func) => self.lower_func(typed_func, bind, instantiations),
            TypedExprKind::Variable(symbol) => self.lower_variable(symbol, expr, instantiations),
            TypedExprKind::Constructor(symbol, _items) => {
                self.lower_constructor(symbol, expr, bind, instantiations)
            }
            TypedExprKind::If(cond, conseq, alt) => {
                self.lower_if_expr(cond, conseq, alt, bind, instantiations)
            }
            TypedExprKind::Match(scrutinee, arms) => {
                self.lower_match(scrutinee, arms, bind, instantiations)
            }
            TypedExprKind::RecordLiteral { fields } => {
                self.lower_record_literal(expr, fields, bind, instantiations)
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

    #[allow(clippy::todo)]
    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_inline_ir(
        &mut self,
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
                let ret = self.ret(bind);
                let dest = self.parsed_register(dest, ret);
                let count = self.parsed_value(count, &binds);
                self.push_instr(Instruction::Alloc {
                    dest,
                    ty: ty.clone(),
                    count,
                });
                Ok((dest.into(), ty))
            }
            InlineIRInstructionKind::Free { addr } => {
                let addr = self.parsed_value(addr, &binds);
                self.push_instr(Instruction::Free { addr });
                Ok((Value::Void, Ty::Void))
            }
            InlineIRInstructionKind::Load { dest, ty, addr } => {
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                let ty = self.parsed_ty(ty, instr.id);
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
                Ok((dest.into(), ty))
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
            meta: vec![InstructionMeta::Source(expr.id)].into(),
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
        scrutinee: &TypedExpr<Ty>,
        arms: &[TypedMatchArm<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let result_type = arms.first().map(|a| a.body.ret.clone()).unwrap_or(Ty::Void);
        let result_register = self.ret(bind);

        let (scrutinee_value, _scrutinee_type) =
            self.lower_expr(scrutinee, Bind::Fresh, instantiations)?;
        let scrutinee_register = scrutinee_value.as_register()?;

        let join_block_id = self.new_basic_block();

        let mut arm_block_ids = Vec::with_capacity(arms.len());
        let mut arm_result_registers = Vec::with_capacity(arms.len());

        for arm in arms {
            let arm_block_id = self.new_basic_block();
            arm_block_ids.push(arm_block_id);

            self.in_basic_block(arm_block_id, |lowerer| {
                let (arm_value, _arm_type) =
                    lowerer.lower_block(&arm.body, Bind::Fresh, instantiations)?;
                let arm_register = arm_value.as_register()?;
                arm_result_registers.push(arm_register);

                lowerer.push_terminator(Terminator::Jump { to: join_block_id });
                Ok(())
            })?;
        }

        // 3. Build the dispatch chain from the block that computed the scrutinee.
        self.build_match_dispatch(scrutinee, scrutinee_register.into(), arms, &arm_block_ids)?;

        // 4. Join block φ (if match produces a value).
        self.set_current_block(join_block_id);

        self.push_phi(Phi {
            dest: result_register,
            ty: result_type.clone(),
            sources: arm_block_ids
                .into_iter()
                .zip(arm_result_registers.into_iter())
                .map(|a| a.into())
                .collect::<Vec<PhiSource>>()
                .into(),
        });

        Ok((Value::Reg(result_register.0), result_type))
    }

    fn build_match_dispatch(
        &mut self,
        scrutinee_expr: &TypedExpr<Ty>,
        scrutinee_value: Value,
        arms: &[TypedMatchArm<Ty>],
        arm_block_ids: &[BasicBlockId],
    ) -> Result<(), IRError> {
        assert_eq!(
            arms.len(),
            arm_block_ids.len(),
            "arms and arm blocks must match"
        );

        // Type of scrutinee; used for the Cmp instruction.
        let scrutinee_type = scrutinee_expr.ty.clone();

        // Start dispatch from the block where the scrutinee was just computed.
        let current_function = self
            .current_function_stack
            .last()
            .expect("did not get current function");
        let current_block_index = *current_function
            .current_block_idx
            .last()
            .expect("did not get current block index");
        let mut current_test_block_id = current_function.blocks[current_block_index].id;

        for arm_index in 0..arms.len() {
            let arm = &arms[arm_index];
            let arm_block_id = arm_block_ids[arm_index];

            // If the pattern is Bind or Wildcard, this is a catch-all from here on.
            match &arm.pattern.kind {
                PatternKind::Bind(..) | PatternKind::Wildcard => {
                    self.set_current_block(current_test_block_id);
                    self.push_terminator(Terminator::Jump { to: arm_block_id });
                    return Ok(());
                }
                _ => {}
            }

            // Last arm: treat it as default (type checker should have enforced
            // exhaustiveness or complained earlier).
            if arm_index == arms.len() - 1 {
                self.set_current_block(current_test_block_id);
                self.push_terminator(Terminator::Jump { to: arm_block_id });
                break;
            }

            // For non-last arms, we emit: Cmp then Branch.
            self.set_current_block(current_test_block_id);

            let (pattern_value, _pattern_type) = self.lower_pattern_literal_value(&arm.pattern)?;

            let condition_register = self.next_register();
            self.push_instr(Instruction::Cmp {
                dest: condition_register,
                lhs: scrutinee_value.clone(),
                rhs: pattern_value,
                ty: scrutinee_type.clone(),
                op: CmpOperator::Equals,
                meta: vec![InstructionMeta::Source(arm.pattern.id)].into(),
            });

            let next_test_block_id = self.new_basic_block();

            self.push_terminator(Terminator::Branch {
                cond: Value::Reg(condition_register.0),
                conseq: arm_block_id,
                alt: next_test_block_id,
            });

            // Next iteration will emit into the fallthrough test block.
            current_test_block_id = next_test_block_id;
        }

        Ok(())
    }

    fn lower_pattern_literal_value(
        &mut self,
        pattern: &TypedPattern<Ty>,
    ) -> Result<(Value, Ty), IRError> {
        match &pattern.kind {
            PatternKind::LiteralInt(text) => {
                let parsed = text.parse::<i64>().map_err(|error| {
                    IRError::InvalidAssignmentTarget(format!(
                        "invalid integer literal in match pattern: {text} ({error})"
                    ))
                })?;
                Ok((Value::Int(parsed), Ty::Int))
            }

            PatternKind::LiteralFloat(text) => {
                let parsed = text.parse::<f64>().map_err(|error| {
                    IRError::InvalidAssignmentTarget(format!(
                        "invalid float literal in match pattern: {text} ({error})"
                    ))
                })?;
                Ok((Value::Float(parsed), Ty::Float))
            }

            PatternKind::LiteralTrue => Ok((Value::Bool(true), Ty::Bool)),
            PatternKind::LiteralFalse => Ok((Value::Bool(false), Ty::Bool)),

            PatternKind::Bind(..) | PatternKind::Wildcard => {
                // These are handled earlier in build_match_dispatch as defaults.
                unreachable!("Bind and Wildcard should not reach lower_pattern_literal_value")
            }

            // Everything else will need a more sophisticated scheme:
            // - Variant: compare enum tag, then destructure fields in the arm
            // - Tuple / Record / Struct: recursive structural matching
            // For now, make it explicit that these are not lowered here.
            other => Err(IRError::InvalidAssignmentTarget(format!(
                "pattern kind not yet supported in match dispatch lowering: {other:?}"
            ))),
        }
    }

    fn lower_record_literal(
        &mut self,
        expr: &TypedExpr<Ty>,
        fields: &[TypedRecordField<Ty>],
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let mut field_vals = vec![];
        let mut field_row = Row::Empty(TypeDefKind::Struct);
        for field in fields.iter() {
            let (val, ty) = self.lower_expr(&field.value, Bind::Fresh, instantiations)?;
            field_vals.push(val);
            field_row = Row::Extend {
                row: field_row.into(),
                label: field.name.clone(),
                ty,
            };
        }

        let dest = self.ret(bind);

        // Check if this record literal is typed as a nominal struct
        if let Ty::Nominal { symbol, .. } = &expr.ty {
            let ty = Ty::Record(Some(*symbol), field_row.into());
            self.push_instr(Instruction::Nominal {
                dest,
                sym: *symbol,
                ty: ty.clone(),
                record: field_vals.into(),
                meta: vec![InstructionMeta::Source(expr.id)].into(),
            });
            return Ok((dest.into(), ty));
        }

        let ty = Ty::Record(None, field_row.into());
        self.push_instr(Instruction::Record {
            dest,
            ty: ty.clone(),
            record: field_vals.into(),
            meta: vec![InstructionMeta::Source(expr.id)].into(),
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
        instantiations.ty.extend(old_instantiations.ty.clone());
        instantiations.row.extend(old_instantiations.row.clone());

        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty: ty.clone(),
            val: Value::Func(constructor_sym),
        });

        Ok((dest.into(), ty))
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_enum_constructor(
        &mut self,
        id: NodeID,
        enum_symbol: &Symbol,
        variant_name: &Label,
        values: &[TypedExpr<Ty>],
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
            .get_symbol(&enum_symbol)
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

        let mut args: Vec<Value> = Default::default();
        let mut args_tys: Vec<Ty> = vec![Ty::Int];
        for value in values.iter() {
            let (val, ty) = self.lower_expr(value, Bind::Fresh, &instantiations)?;
            args.push(val);
            args_tys.push(ty);
        }

        // Set the tag as the first entry
        args.insert(0, Value::Int(tag as i64));

        let row =
            args_tys
                .iter()
                .enumerate()
                .fold(Row::Empty(TypeDefKind::Enum), |acc, (i, ty)| Row::Extend {
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
            if let TypedExprKind::Constructor(name, ..) = &receiver.kind {
                return self.lower_enum_constructor(
                    receiver.id,
                    name,
                    label,
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
            } else if let Some(witness) = witness.or_else(|| self.witness_for(receiver, label))
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
        if self
            .current_func_mut()
            .bindings
            .contains_key(original_name_sym)
        {
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
        id: NodeID,
        name: &Symbol,
        callee: &TypedExpr<Ty>,
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<(Value, Ty), IRError> {
        let record_dest = self.next_register();

        // Look up the initializer and specialize it using the already-computed instantiations
        let init_sym = *self
            .types
            .catalog
            .initializers
            .get(name)
            .unwrap_or_else(|| panic!("did not get initializers for {name:?}"))
            .get(&Label::Named("init".into()))
            .expect("did not get init");

        let init_entry = self
            .types
            .get_symbol(&init_sym)
            .cloned()
            .expect("did not get init entry");
        let (init_ty, concrete_tys) = self.specialize(&init_entry, callee.id)?;

        let properties = self
            .types
            .catalog
            .properties
            .get(name)
            .expect("did not get properties");

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
            meta: vec![InstructionMeta::Source(id)].into(),
        });
        args.insert(0, record_dest.into());

        let init = self.monomorphize_name(init_sym, &concrete_tys);

        self.push_instr(Instruction::Call {
            dest,
            ty: ret.clone(),
            callee: Value::Func(init.symbol().expect("did not get symbol")),
            args: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

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
            let arg = self.lower_expr(&args[0], Bind::Assigned(dest), parent_instantiations)?;
            self.push_instr(Instruction::_Print { val: arg.0 });
            return Ok((Value::Void, Ty::Void));
        }

        let instantiations = parent_instantiations.clone();

        let ty = call_expr.ty.clone();
        let mut arg_vals = vec![];
        let mut arg_tys = vec![];
        for arg in args {
            let (arg, arg_ty) = self.lower_expr(&arg, Bind::Fresh, &instantiations)?;
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
        let (ty, instantiations) = self.specialized_ty(call_expr, &instantiations)?;

        // Is this an instance method call on a constructor? If so we don't need
        // to prepend a self arg because it's passed explicitly (like Foo.bar(fizz) where
        // fizz == self)
        if let TypedExprKind::Constructor(_name, ..) = &receiver.kind {
            receiver = arg_exprs[0].clone();
        } else {
            let (receiver_ir, _) = self.lower_expr(&receiver, Bind::Fresh, &instantiations)?;
            args.insert(0, receiver_ir);
        }

        let (method_sym, val, ty) = if let Some(method_sym) =
            self.lookup_instance_method(&receiver, label, &instantiations)?
        {
            let method = self.monomorphize_name(method_sym, &instantiations);
            self.check_import(&method_sym);
            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: Value::Func(method.symbol().expect("didn't get method sym")),
                args: args.into(),
                meta: vec![InstructionMeta::Source(call_expr.id)].into(),
            });

            (method_sym, dest.into(), ty)
        } else if let Some(witness) = witness.or_else(|| self.witness_for(&receiver, label)) {
            // For method calls on type parameters, look up the witness at the callee expression's node ID.
            // This returns a MethodRequirement symbol that the monomorphizer will substitute with
            // the concrete implementation when specializing.
            let method = self.monomorphize_name(witness, &instantiations);

            self.check_import(&witness);
            self.push_instr(Instruction::Call {
                dest,
                ty: ty.clone(),
                callee: Value::Func(method.symbol().expect("did not get witness sym")),
                args: args.into(),
                meta: vec![InstructionMeta::Source(call_expr.id)].into(),
            });

            (witness, dest.into(), ty)
        } else {
            tracing::warn!(
                "No witness found for {:?} in {:?} ({:?}).",
                label,
                receiver,
                receiver.ty.clone()
            );

            return Ok((Value::Void, Ty::Void));
            // return Err(IRError::TypeNotFound(format!(
            //     "No witness found for {:?} in {:?} ({:?}).",
            //     label,
            //     receiver,
            //     receiver.ty.clone(),
            // )));
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
    ) -> Result<(Value, Ty), IRError> {
        let ty = self.ty_from_symbol(&func.name)?;

        let (mut param_tys, mut ret_ty) = uncurry_function(ty);

        // Do we have captures? If so this is a closure
        let capture_env = if let Some(captures) =
            self.resolved_names.captures.get(&func.name).cloned()
            && !captures.is_empty()
        {
            let mut env_fields = vec![];
            for capture in captures.clone() {
                let ty = self
                    .ty_from_symbol(&capture.symbol)
                    .expect("didn't get capture ty")
                    .clone();

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

            Some(env_fields)
        } else {
            None
        };

        let _s = tracing::trace_span!("pushing new current function");
        self.current_function_stack
            .push(CurrentFunction::new(func.name));

        let mut params = vec![];

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
                        .fold(Row::Empty(TypeDefKind::Struct), |row, (i, _)| Row::Extend {
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
            self.insert_binding(param.name, register.into());
        }

        let mut ret = Value::Void;
        for node in func.body.body.iter() {
            (ret, ret_ty) = self.lower_node(node, instantiations)?;
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
            func.name,
            PolyFunction {
                name: func.name,
                params,
                blocks: current_function.blocks,
                ty: func_ty.clone(),
                register_count: (current_function.registers.next) as usize,
            },
        );

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
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
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
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let current_block_idx = current_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");
        current_function.blocks[*current_block_idx].phis.push(phi);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn new_basic_block(&mut self) -> BasicBlockId {
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let id = BasicBlockId(current_function.blocks.len() as u32);
        let new_block = BasicBlock {
            id,
            phis: Default::default(),
            instructions: Default::default(),
            terminator: Terminator::Unreachable,
        };
        current_function.blocks.push(new_block);
        id
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn get_current_block(&mut self) -> BasicBlockId {
        BasicBlockId(
            self.current_function_stack
                .last_mut()
                .expect("didn't get current func")
                .current_block_idx
                .last()
                .copied()
                .expect("didnt get current block id") as u32,
        )
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn set_current_block(&mut self, id: BasicBlockId) {
        self.current_function_stack
            .last_mut()
            .expect("didn't get current func")
            .current_block_idx
            .push(id.0 as usize);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, f))]
    fn in_basic_block<T>(
        &mut self,
        id: BasicBlockId,
        f: impl FnOnce(&mut Lowerer<'a>) -> Result<T, IRError>,
    ) -> Result<T, IRError> {
        self.current_function_stack
            .last_mut()
            .expect("didn't get current func")
            .current_block_idx
            .push(id.0 as usize);
        let ret = f(self);
        self.current_function_stack
            .last_mut()
            .expect("didn't get current func")
            .current_block_idx
            .pop();
        ret
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let current_function = self
            .current_function_stack
            .last_mut()
            .expect("didn't get current function");
        let current_block_idx = current_function
            .current_block_idx
            .last()
            .expect("didn't get current block idx");

        let block = &mut current_function.blocks[*current_block_idx];
        // Don't override an existing terminator (e.g., from an early return)
        if block.terminator != Terminator::Unreachable {
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
        self.current_function_stack
            .last_mut()
            .expect("didn't get current function")
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
            Bind::Indirect(reg, sym) => {
                let ty = self.ty_from_symbol(&sym).expect("did not get ty for bind");
                let value = self.next_register();
                self.push_instr(Instruction::Store {
                    value: value.into(),
                    ty,
                    addr: reg.into(),
                });
                value
            }
        }
    }

    /// Check to see if this symbol calls any symbols we don't have
    fn check_import(&mut self, symbol: &Symbol) {
        // if self.config.module_id == ModuleId::Core {
        //     println!("not core: {symbol}");
        //     // No imports can happen from core.
        //     return;
        // }

        let module_id = match symbol {
            Symbol::InstanceMethod(InstanceMethodId { module_id, .. }) => Some(*module_id),
            Symbol::StaticMethod(StaticMethodId { module_id, .. }) => Some(*module_id),
            Symbol::Initializer(InitializerId { module_id, .. }) => Some(*module_id),
            Symbol::Global(GlobalId { module_id, .. }) => Some(*module_id),
            Symbol::Synthesized(SynthesizedId { module_id, .. }) => Some(*module_id),
            _ => None,
        };

        let Some(module_id) = module_id else {
            return;
        };

        let func = if module_id == self.config.module_id || (module_id == ModuleId::Current) {
            let Some(func) = self.functions.get(symbol) else {
                return;
            };

            func
        } else {
            let Some(program) = self.config.modules.program_for(module_id) else {
                return;
            };
            // TODO: This won't work with external methods yet, only core works.
            let Some(method_func) = program.polyfunctions.get(symbol) else {
                return;
            };
            self.functions.insert(*symbol, method_func.clone());
            method_func
        };

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
            if matches!(callee_sym, Symbol::MethodRequirement(..)) {
                println!(" not so fast wise guy: {callee_sym:?}");
            }

            // Already imported, avoid infinite recursion
            if self.functions.contains_key(&callee_sym) {
                continue;
            }
            self.check_import(&callee_sym);
        }
    }

    fn resolve_name(&self, sym: &Symbol) -> Option<&String> {
        if let Some(string) = self.symbol_names.get(sym) {
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
                        self.symbol_names
                    )
                })
                .to_string(),
        );

        if instantiations.ty.is_empty() && instantiations.witnesses.is_empty() {
            return name;
        }

        let new_symbol = self.symbols.next_synthesized(self.config.module_id);
        self.symbol_names.insert(new_symbol.into(), name.name_str());
        let ty_parts: Vec<String> = instantiations.ty.values().map(|v| format!("{v}")).collect();
        let witness_parts: Vec<String> = instantiations
            .witnesses
            .values()
            .map(|v| format!("{v}"))
            .collect();
        let all_parts: Vec<String> = ty_parts.into_iter().chain(witness_parts).collect();
        let new_name_str = format!("{}[{}]", name, all_parts.join(", "));

        let new_name = Name::Resolved(new_symbol.into(), new_name_str);

        tracing::trace!("monomorphized {name:?} -> {new_name:?}");

        self.specializations
            .entry(name.symbol().expect("name not resolved"))
            .or_default()
            .push(Specialization {
                name: new_symbol.into(),
                substitutions: instantiations.clone(),
            });

        new_name
    }

    fn parsed_ty(&mut self, ty: &TypeAnnotation, id: NodeID) -> Ty {
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
        ty
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
            crate::node_kinds::inline_ir_instruction::Value::Record(symbol, values) => {
                Value::Record(
                    *symbol,
                    values.iter().map(|v| self.parsed_value(v, binds)).collect(),
                )
            }
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
            && matches!(sym, Symbol::InstanceMethod(..))
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
                let Ty::Constructor { name, .. } = &receiver.ty else {
                    return Ok((expr.ty.clone(), Default::default()));
                };

                let Some((member, _)) = self
                    .types
                    .catalog
                    .lookup_member(&name.symbol().expect("didn't get sym"), label)
                else {
                    return Ok((expr.ty.clone(), Default::default()));
                };

                member
            }
            TypedExprKind::ProtocolMember { witness, .. } => *witness,
            _ => {
                tracing::trace!("expr has no substitutions: {expr:?}");
                return Ok((expr.ty.clone(), Default::default()));
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
                let mut substitutions = Substitutions::default();
                for forall in scheme.foralls.iter() {
                    match forall {
                        ForAll::Ty(param) => {
                            let ty = self
                                .types
                                .catalog
                                .instantiations
                                .ty
                                .get(&(id, *param))
                                .cloned()
                                .unwrap_or(Ty::Param(*param));

                            if Ty::Param(*param) != ty {
                                substitutions.ty.insert(Ty::Param(*param), ty);
                            }
                        }

                        ForAll::Row(param) => {
                            let row = self
                                .types
                                .catalog
                                .instantiations
                                .row
                                .get(&(id, *param))
                                .cloned()
                                .unwrap_or(Row::Param(*param));

                            substitutions.row.insert(*param, row);
                        }
                    };
                }

                let ty = substitute(scheme.ty.clone(), &substitutions);

                Ok((ty, substitutions))
            }
        }
    }

    #[instrument(skip(self), ret)]
    fn witness_for(&mut self, receiver: &TypedExpr<Ty>, label: &Label) -> Option<Symbol> {
        println!("looking for witness: {receiver:?}");
        None
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
                    Ok(Ty::Func(Ty::Void.into(), Ty::Void.into()))
                } else {
                    Err(IRError::TypeNotFound(format!(
                        "Type not found for symbol: {symbol}"
                    )))
                }
            }
        }
    }
}

fn substitute(ty: Ty, substitutions: &Substitutions) -> Ty {
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
        Ty::Func(box param, box ret) => Ty::Func(
            substitute(param, substitutions).into(),
            substitute(ret, substitutions).into(),
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

fn substitute_row(row: Row, substitutions: &Substitutions) -> Row {
    match row {
        Row::Empty(..) => row,
        Row::Param(id) => substitutions.row.get(&id).unwrap_or(&row).clone(),
        Row::Extend { box row, label, ty } => Row::Extend {
            row: substitute_row(row, substitutions).into(),
            label,
            ty: substitute(ty, substitutions),
        },
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
    params
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p.clone()), Box::new(acc)))
}
