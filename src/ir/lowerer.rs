use crate::compiling::module::ModuleId;
use crate::formatter;
use crate::ir::ir_ty::IrTy;
use crate::ir::monomorphizer::uncurry_function;
use crate::ir::parse_instruction;
use crate::label::Label;
use crate::name_resolution::symbol::Symbols;
use crate::node_kinds::parameter::Parameter;
use crate::types::infer_row::RowParamId;
use crate::types::infer_ty::TypeParamId;
use crate::types::row::Row;
use crate::{
    ast::AST,
    compiling::driver::Source,
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
    name_resolution::{
        name_resolver::NameResolved,
        symbol::{Symbol, SynthesizedId},
    },
    node::Node,
    node_id::{FileID, NodeID},
    node_kinds::{
        block::Block,
        call_arg::CallArg,
        decl::{Decl, DeclKind},
        expr::{Expr, ExprKind},
        func::Func,
        pattern::{Pattern, PatternKind},
        stmt::{Stmt, StmtKind},
    },
    span::Span,
    types::{
        scheme::ForAll,
        ty::Ty,
        type_session::{TypeEntry, Types},
    },
};
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use tracing::instrument;

enum LValue<F> {
    Field {
        base: Box<LValue<F>>,
        field: F,
        ty: Ty,
    },
    Variable(Symbol),
}

#[derive(Debug)]
pub(super) struct CurrentFunction {
    current_block_idx: usize,
    blocks: Vec<BasicBlock<Ty, Label>>,
    pub registers: RegisterAllocator,
}

impl Default for CurrentFunction {
    fn default() -> Self {
        CurrentFunction {
            current_block_idx: 0,
            blocks: vec![BasicBlock::<Ty, Label> {
                id: BasicBlockId(0),
                instructions: Default::default(),
                terminator: Terminator::Unreachable,
            }],
            registers: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Bind {
    Assigned(Register),
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
    pub ty: FxHashMap<TypeParamId, Ty>,
    pub row: FxHashMap<RowParamId, Row>,
}

#[derive(Clone, Debug)]
pub(super) struct PolyFunction {
    pub name: Name,
    pub params: Vec<Value>,
    pub blocks: Vec<BasicBlock<Ty, Label>>,
    pub ty: Ty,
    pub register_count: usize,
}

#[derive(Debug, Clone)]
pub struct Specialization {
    pub name: Name,
    pub(super) substitutions: Substitutions,
}

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer {
    pub(super) asts: IndexMap<Source, AST<NameResolved>>,
    pub(super) types: Types,
    pub(super) functions: IndexMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,

    symbols: Symbols,
    bindings: FxHashMap<Symbol, Register>,
    pub(super) specializations: IndexMap<Symbol, Vec<Specialization>>,
}

impl Lowerer {
    pub fn new(asts: IndexMap<Source, AST<NameResolved>>, types: Types, symbols: Symbols) -> Self {
        Self {
            asts,
            types,
            functions: Default::default(),
            current_function_stack: Default::default(),
            bindings: Default::default(),
            symbols,
            specializations: Default::default(),
        }
    }

    pub fn lower(mut self) -> Result<Program, IRError> {
        if self.asts.is_empty() {
            return Ok(Program::default());
        }

        // Do we have a main func?
        let mut asts = std::mem::take(&mut self.asts);
        let has_main_func = asts.iter_mut().flat_map(|a| &a.1.roots).any(is_main_func);
        if !has_main_func {
            let main_symbol = Symbol::Synthesized(self.symbols.next_synthesized(ModuleId::Current));
            let mut ret_ty = Ty::Void;
            let func = Func {
                id: NodeID(FileID::SYNTHESIZED, 0),
                name: Name::Resolved(main_symbol, "main".into()),
                name_span: Span {
                    start: 0,
                    end: 0,
                    file_id: FileID(0),
                },
                generics: vec![],
                params: vec![],
                body: Block {
                    id: NodeID(FileID(0), 0),
                    args: vec![],
                    span: Span {
                        start: 0,
                        end: 0,
                        file_id: FileID(0),
                    },
                    body: {
                        let roots: Vec<Node> = asts
                            .values_mut()
                            .flat_map(|a| std::mem::take(&mut a.roots))
                            .collect();

                        if let Some(last) = roots.last() {
                            ret_ty = match self
                                .types
                                .get(&last.node_id())
                                .unwrap_or(&TypeEntry::Mono(Ty::Void))
                            {
                                TypeEntry::Mono(ty) => ty.clone(),
                                TypeEntry::Poly(scheme) => scheme.ty.clone(),
                            };
                        }

                        roots
                    },
                },
                ret: None,
                attributes: vec![],
            };

            let ast = asts.iter_mut().next().unwrap();
            ast.1.roots.push(Node::Decl(Decl {
                id: NodeID(FileID::SYNTHESIZED, 0),
                span: Span::SYNTHESIZED,
                kind: DeclKind::Let {
                    lhs: Pattern {
                        id: NodeID(FileID::SYNTHESIZED, 0),
                        span: Span::SYNTHESIZED,
                        kind: PatternKind::Bind(Name::Resolved(
                            SynthesizedId::from(0).into(),
                            "main".into(),
                        )),
                    },
                    type_annotation: None,
                    value: Some(Expr {
                        id: NodeID(FileID::SYNTHESIZED, 0),
                        span: Span::SYNTHESIZED,
                        kind: ExprKind::Func(func),
                    }),
                },
            }));

            self.types.define(
                main_symbol,
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into())),
            );
        }

        self.current_function_stack.push(CurrentFunction::default());

        for ast in asts.values_mut() {
            for root in ast.roots.iter() {
                self.lower_node(root, &Default::default())?;
            }
        }

        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
        })
    }

    fn lower_node(
        &mut self,
        node: &Node,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        match node {
            Node::Decl(decl) => self.lower_decl(decl, instantiations),
            Node::Stmt(stmt) => self.lower_stmt(stmt, instantiations),
            _ => unreachable!("node not handled: {node:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl), fields(decl.id = %decl.id))]
    fn lower_decl(
        &mut self,
        decl: &Decl,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                value: Some(value),
                ..
            } => {
                let bind = self.lower_pattern(lhs)?;
                self.lower_expr(value, bind, instantiations)?;
            }
            DeclKind::Struct { body, .. } => {
                for node in &body.body {
                    self.lower_node(node, instantiations)?;
                }
            }
            DeclKind::Init { name, params, body } => {
                self.lower_init(decl, name, params, body, instantiations)?;
            }
            DeclKind::Property { .. } => (),
            DeclKind::Method { func, .. } => {
                self.lower_method(func)?;
            }
            DeclKind::Associated { .. } => todo!(),
            DeclKind::Func(..) => todo!(),
            DeclKind::Extend { .. } => todo!(),
            DeclKind::Enum { .. } => todo!(),
            DeclKind::EnumVariant(..) => todo!(),
            DeclKind::FuncSignature(..) => todo!(),
            DeclKind::MethodRequirement(..) => todo!(),
            DeclKind::TypeAlias(..) => todo!(),
            _ => (), // Nothing to do
        }

        Ok(Value::Void)
    }

    fn lower_method(&mut self, func: &Func) -> Result<Value, IRError> {
        self.lower_func(func, Bind::Discard, &Default::default())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl, body))]
    fn lower_init(
        &mut self,
        decl: &Decl,
        name: &Name,
        params: &[Parameter],
        body: &Block,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let func_ty = match self.types.get_symbol(&name.symbol().unwrap()).unwrap() {
            TypeEntry::Mono(ty) => ty.clone(),
            TypeEntry::Poly(scheme) => scheme.ty.clone(),
        };

        let Ty::Func(..) = func_ty else {
            unreachable!();
        };

        let (param_tys, ret_ty) = uncurry_function(func_ty.clone());

        // Build param_ty from all params (for now, just use the first one for compatibility)
        let param_ty = if !param_tys.is_empty() {
            param_tys[0].clone()
        } else {
            let meta = Default::default();
            let formatter = formatter::Formatter::new(&meta);
            unreachable!(
                "init has no params - param_tys: {param_tys:?} name: {name:?}, sym: {:?}, ty: {:?}, {:?}",
                self.types.get_symbol(&name.symbol().unwrap()).unwrap(),
                func_ty,
                formatter.format(&[Node::Decl(decl.clone())], 80)
            );
        };

        self.current_function_stack.push(CurrentFunction::default());

        let mut param_values = vec![];
        for param in params.iter() {
            let register = self.next_register();
            param_values.push(Value::Reg(register.0));
            self.bindings.insert(param.name.symbol().unwrap(), register);
        }

        let mut ret = Value::Void;
        for node in body.body.iter() {
            ret = self.lower_node(node, instantiations)?;
        }
        self.push_terminator(Terminator::Ret {
            val: ret.clone(),
            ty: ret_ty.clone(),
        });

        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");

        self.functions.insert(
            name.symbol().unwrap(),
            PolyFunction {
                name: name.clone(),
                params: param_values,
                blocks: current_function.blocks,
                ty: Ty::Func(Box::new(param_ty.clone()), Box::new(ret_ty.clone())),
                register_count: (current_function.registers.next) as usize,
            },
        );

        Ok(ret)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt), fields(stmt.id = %stmt.id))]
    fn lower_stmt(
        &mut self,
        stmt: &Stmt,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.lower_expr(expr, Bind::Fresh, instantiations),
            StmtKind::If(_expr, _block, _block1) => todo!(),
            StmtKind::Return(_expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs, instantiations),
            StmtKind::Loop(_expr, _block) => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs), fields(lhs.id = %lhs.id, rhs.id = %rhs.id))]
    fn lower_assignment(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let lvalue = self.lower_lvalue(lhs)?;
        let value = self.lower_expr(rhs, Bind::Fresh, instantiations)?;

        self.emit_lvalue_store(lvalue, value)?;

        Ok(Value::Void)
    }

    fn emit_load_lvalue(&mut self, lvalue: &LValue<Label>) -> Result<Register, IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                // Variable is already in a register
                Ok(*self.bindings.get(sym).unwrap())
            }
            LValue::Field { base, field, ty } => {
                // Recursively load base, then extract field
                let base_val = self.emit_load_lvalue(base)?;
                let dest = self.next_register();

                self.push_instr(Instruction::GetField {
                    dest,
                    record: base_val,
                    field: field.clone(),
                    ty: ty.clone(),
                    meta: vec![].into(),
                });

                Ok(dest)
            }
        }
    }

    fn emit_lvalue_store(&mut self, lvalue: LValue<Label>, value: Value) -> Result<(), IRError> {
        match lvalue {
            LValue::Variable(sym) => {
                // Simple rebind
                let reg = value.as_register()?;
                self.bindings.insert(sym, reg);
                Ok(())
            }
            LValue::Field {
                box base,
                field,
                ty,
            } => {
                // This is the tricky part - need to rebuild the chain

                // 1. Load the base (to get what we're inserting into)
                let base_val = self.emit_load_lvalue(&base)?;

                // 2. Insert the new value at this level
                let dest = self.next_register();
                self.push_instr(Instruction::SetField {
                    dest,
                    record: base_val,
                    field: field.clone(),
                    val: value,
                    ty,
                    meta: vec![].into(),
                });

                // 3. Recursively store the updated value back into base!
                self.emit_lvalue_store(base, dest.into())?;

                Ok(())
            }
        }
    }

    fn lower_lvalue(&mut self, expr: &Expr) -> Result<LValue<Label>, IRError> {
        match &expr.kind {
            ExprKind::Variable(name) => Ok(LValue::Variable(name.symbol().unwrap())),
            ExprKind::Member(Some(box base), label, _span) => {
                let base_lvalue = self.lower_lvalue(base)?;
                let (base_ty, ..) = self.specialized_ty(base).expect("didn't get base ty");

                Ok(LValue::Field {
                    base: base_lvalue.into(),
                    ty: base_ty.clone(),
                    field: label.clone(),
                })
            }
            _ => Err(IRError::InvalidAssignmentTarget(format!("{expr:?}"))),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, pattern), fields(pattern.id = %pattern.id))]
    fn lower_pattern(&mut self, pattern: &Pattern) -> Result<Bind, IRError> {
        match &pattern.kind {
            PatternKind::Bind(name) => {
                let value = self.next_register();
                let symbol = name.symbol().unwrap();
                self.bindings.insert(symbol, value);
                Ok(Bind::Assigned(value))
            }
            PatternKind::LiteralInt(_) => todo!(),
            PatternKind::LiteralFloat(_) => todo!(),
            PatternKind::LiteralTrue => todo!(),
            PatternKind::LiteralFalse => todo!(),
            PatternKind::Tuple(..) => todo!(),
            PatternKind::Wildcard => todo!(),
            PatternKind::Variant { .. } => todo!(),
            PatternKind::Record { .. } => todo!(),
            PatternKind::Struct { .. } => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, expr), fields(expr.id = %expr.id))]
    fn lower_expr(
        &mut self,
        expr: &Expr,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        match &expr.kind {
            ExprKind::Func(func) => self.lower_func(func, bind, instantiations),
            ExprKind::LiteralArray(_exprs) => todo!(),
            ExprKind::LiteralInt(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::ConstantInt {
                    dest: ret,
                    val: str::parse(val).unwrap(),
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok(ret.into())
            }
            ExprKind::LiteralFloat(val) => {
                let ret = self.ret(bind);
                self.push_instr(Instruction::ConstantFloat {
                    dest: ret,
                    val: str::parse(val).unwrap(),
                    meta: vec![InstructionMeta::Source(expr.id)].into(),
                });
                Ok(ret.into())
            }
            ExprKind::LiteralTrue => todo!(),
            ExprKind::LiteralFalse => todo!(),
            ExprKind::LiteralString(_) => todo!(),
            ExprKind::Unary(..) => todo!(),
            ExprKind::Binary(..) => todo!(),
            ExprKind::Tuple(..) => todo!(),
            ExprKind::Block(..) => todo!(),
            ExprKind::Call {
                box callee, args, ..
            } => self.lower_call(expr.id, callee, args, bind, instantiations),
            ExprKind::Member(member, label, ..) => {
                self.lower_member(expr.id, member, label, bind, instantiations)
            }
            ExprKind::Variable(name) => self.lower_variable(name, expr, instantiations),
            ExprKind::Constructor(name) => self.lower_constructor(name, expr, bind, instantiations),
            ExprKind::If(..) => todo!(),
            ExprKind::Match(..) => todo!(),
            ExprKind::RecordLiteral { .. } => todo!(),
            ExprKind::RowVariable(..) => todo!(),
            _ => unreachable!("cannot lower expr: {expr:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_constructor(
        &mut self,
        name: &Name,
        expr: &Expr,
        bind: Bind,
        old_instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let init_sym = *self
            .types
            .catalog
            .initializers
            .get(&name.symbol().unwrap())
            .unwrap()
            .get(&Label::Named("init".into()))
            .unwrap();

        let init_entry = self.types.get_symbol(&init_sym).cloned().unwrap();
        let (ty, mut instantiations) = self.specialize(&init_entry, expr.id)?;
        instantiations.ty.extend(old_instantiations.ty.clone());
        instantiations.row.extend(old_instantiations.row.clone());

        let dest = self.ret(bind);
        self.push_instr(Instruction::Ref {
            dest,
            ty,
            val: Value::Func(Name::Resolved(init_sym, format!("{}_init", name))),
        });

        Ok(dest.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, receiver))]
    fn lower_member(
        &mut self,
        id: NodeID,
        receiver: &Option<Box<Expr>>,
        label: &Label,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        if let Some(box receiver) = &receiver {
            let reg = self.next_register();
            let member_bind = Bind::Assigned(reg);
            let receiver_val = self.lower_expr(receiver, member_bind, instantiations)?;
            let ty = self.ty_from_id(&id)?;
            let dest = self.ret(bind);

            let (receiver_ty, _) = self.specialized_ty(receiver)?;

            if let Ty::Nominal { symbol, .. } = &receiver_ty
                && let Some(method) = self
                    .types
                    .catalog
                    .instance_methods
                    .get(symbol)
                    .and_then(|m| m.get(label))
            {
                self.push_instr(Instruction::Ref {
                    dest,
                    ty,
                    val: Value::Func(Name::Resolved(*method, label.to_string())),
                });
            } else {
                self.push_instr(Instruction::GetField {
                    dest,
                    ty,
                    record: receiver_val.as_register()?,
                    field: label.clone(),
                    meta: vec![InstructionMeta::Source(id)].into(),
                });
            };

            Ok(dest.into())
        } else {
            todo!("gotta handle unqualified lookups")
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_variable(
        &mut self,
        name: &Name,
        expr: &Expr,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let (ty, instantiations) = self.specialized_ty(expr)?;
        let monomorphized_ty = substitute(ty, &instantiations);

        let ret = if matches!(monomorphized_ty, Ty::Func(..)) {
            // It's a func reference so we pass the name
            let monomorphized_name = self.monomorphize_name(name.clone(), &instantiations);
            Value::Func(monomorphized_name)
        } else {
            self.bindings.get(&name.symbol().unwrap()).unwrap().into()
        };

        Ok(ret)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    #[allow(clippy::too_many_arguments)]
    fn lower_constructor_call(
        &mut self,
        id: NodeID,
        name: &Name,
        callee: &Expr,
        mut args: Vec<Value>,
        dest: Register,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let record_dest = self.next_register();

        // Look up the initializer and specialize it using the already-computed instantiations
        let init_sym = *self
            .types
            .catalog
            .initializers
            .get(&name.symbol().unwrap())
            .unwrap()
            .get(&Label::Named("init".into()))
            .unwrap();

        let init_entry = self.types.get_symbol(&init_sym).cloned().unwrap();
        let (init_ty, concrete_tys) = self.specialize(&init_entry, callee.id)?;

        let properties = self
            .types
            .catalog
            .properties
            .get(&name.symbol().unwrap())
            .unwrap();

        // Extract return type from the initializer function
        let mut params = init_ty.clone().uncurry_params();
        let ret = params.pop().unwrap();

        self.push_instr(Instruction::Record {
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

        let init = self.monomorphize_name(
            Name::Resolved(init_sym, format!("{}_init", name)),
            &concrete_tys,
        );

        self.push_instr(Instruction::Call {
            dest,
            ty: ret.clone(),
            callee: Value::Func(init),
            args: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok(dest.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_call(
        &mut self,
        id: NodeID,
        callee: &Expr,
        args: &[CallArg],
        bind: Bind,
        parent_instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let dest = self.ret(bind);

        // Handle embedded IR call
        if let ExprKind::Variable(name) = &callee.kind
            && name.symbol().unwrap() == Symbol::IR
        {
            return self.lower_embedded_ir_call(args, dest);
        }

        let (_callee_ty, mut instantiations) = self.specialized_ty(callee).unwrap();
        instantiations.ty.extend(parent_instantiations.ty.clone());
        instantiations.row.extend(parent_instantiations.row.clone());

        let ty = self.ty_from_id(&id)?;
        let mut args = args
            .iter()
            .map(|arg| self.lower_expr(&arg.value, Bind::Fresh, &instantiations))
            .collect::<Result<Vec<Value>, _>>()?;

        if let ExprKind::Constructor(name) = &callee.kind {
            return self.lower_constructor_call(id, name, callee, args, dest, &instantiations);
        }

        let callee_ir = if let ExprKind::Member(Some(box receiver), member, ..) = &callee.kind
            && let Some(method_sym) = self.lookup_instance_method(receiver, member)?
        {
            // Handle method calls. It'd be nice if we could re-use lower_member here but i'm not sure
            // how we'd get the receiver value, which we need to pass as the first arg..
            let receiver_ir = self.lower_expr(receiver, Bind::Fresh, &instantiations)?;
            args.insert(0, receiver_ir);
            Value::Func(Name::Resolved(method_sym, member.to_string()))
        } else {
            self.lower_expr(callee, Bind::Fresh, &instantiations)?
        };

        self.push_instr(Instruction::Call {
            dest,
            ty,
            callee: callee_ir,
            args: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok(dest.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func.name = %func.name))]
    fn lower_func(
        &mut self,
        func: &Func,
        bind: Bind,
        instantiations: &Substitutions,
    ) -> Result<Value, IRError> {
        let ty = self.ty_from_symbol(&func.name.symbol().unwrap())?;

        let Ty::Func(param_tys, box ret_ty) = ty else {
            panic!("didn't get func ty");
        };

        let _s = tracing::trace_span!("pushing new current function");
        self.current_function_stack.push(CurrentFunction::default());

        let mut params = vec![];
        for param in func.params.iter() {
            let register = self.next_register();
            params.push(Value::Reg(register.0));
            self.bindings.insert(param.name.symbol().unwrap(), register);
        }

        let mut ret = Value::Void;
        for node in func.body.body.iter() {
            ret = self.lower_node(node, instantiations)?;
        }
        self.push_terminator(Terminator::Ret {
            val: ret,
            ty: ret_ty.clone(),
        });

        let current_function = self
            .current_function_stack
            .pop()
            .expect("did not get current function");
        drop(_s);
        self.functions.insert(
            func.name.symbol().unwrap(),
            PolyFunction {
                name: func.name.clone(),
                params,
                blocks: current_function.blocks,
                ty: Ty::Func(param_tys.clone(), ret_ty.clone().into()),
                register_count: (current_function.registers.next) as usize,
            },
        );

        let func = Value::Func(func.name.clone());
        if bind != Bind::Discard {
            let dest = self.ret(bind);
            self.push_instr(Instruction::Ref {
                dest,
                ty: Ty::Func(param_tys, ret_ty.into()),
                val: func.clone(),
            });
        }
        Ok(func)
    }

    fn lower_embedded_ir_call(
        &mut self,
        args: &[CallArg],
        dest: Register,
    ) -> Result<Value, IRError> {
        let ExprKind::LiteralString(string) = &args[0].value.kind else {
            unreachable!()
        };

        let mut string = string.clone();

        if string.contains("$?") {
            string = string.replace("$?", &format!("%{}", dest.0));
        }

        self.push_instr(parse_instruction::<IrTy, Label>(&string).into());

        Ok(dest.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_instr(&mut self, instruction: Instruction<Ty, Label>) {
        let current_function = self.current_function_stack.last_mut().unwrap();
        current_function.blocks[current_function.current_block_idx]
            .instructions
            .push(instruction);
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn push_terminator(&mut self, terminator: Terminator<Ty>) {
        let current_function = self.current_function_stack.last_mut().unwrap();
        current_function.blocks[current_function.current_block_idx].terminator = terminator;
    }

    fn next_register(&mut self) -> Register {
        let current_function = self.current_function_stack.last_mut().unwrap();
        let register = current_function.registers.next();
        tracing::trace!("allocated register: {register}");
        register
    }

    fn ret(&mut self, bind: Bind) -> Register {
        match bind {
            Bind::Assigned(value) => value,
            Bind::Fresh => self.next_register(),
            Bind::Discard => Register::DROP,
        }
    }

    fn monomorphize_name(&mut self, name: Name, instantiations: &Substitutions) -> Name {
        if instantiations.ty.is_empty() {
            return name;
        }

        let new_symbol = self.symbols.next_synthesized(ModuleId::Current);
        let new_name_str = format!(
            "{}[{}]",
            name,
            instantiations
                .ty
                .values()
                .map(|v| format!("{v}"))
                .collect::<Vec<_>>()
                .join(", ")
        );

        let new_name = Name::Resolved(new_symbol.into(), new_name_str);

        self.specializations
            .entry(name.symbol().unwrap())
            .or_default()
            .push(Specialization {
                name: new_name.clone(),
                substitutions: instantiations.clone(),
            });

        new_name
    }

    fn lookup_instance_method(
        &mut self,
        expr: &Expr,
        label: &Label,
    ) -> Result<Option<Symbol>, IRError> {
        println!("looking up instance method for {expr:?}");
        let symbol = match &expr.kind {
            ExprKind::LiteralInt(_) => Symbol::Int,
            ExprKind::LiteralFloat(_) => Symbol::Float,
            ExprKind::LiteralTrue | ExprKind::LiteralFalse => Symbol::Bool,
            _ => {
                let Ty::Nominal { symbol, .. } = self.specialized_ty(expr)?.0 else {
                    return Ok(None);
                };

                symbol
            }
        };

        if let Some(methods) = self.types.catalog.instance_methods.get(&symbol)
            && let Some(method) = methods.get(label)
        {
            return Ok(Some(*method));
        }

        println!(
            "didn't get a method: {:?}",
            self.types.catalog.instance_methods.get(&symbol)
        );

        Ok(None)
    }

    fn specialized_ty(&mut self, expr: &Expr) -> Result<(Ty, Substitutions), IRError> {
        let name = match &expr.kind {
            ExprKind::Variable(name) => name,
            ExprKind::Func(func) => &func.name,
            ExprKind::Constructor(name) => name,
            _ => {
                tracing::trace!("expr has no substitutions: {expr:?}");
                return Ok((self.ty_from_id(&expr.id)?, Default::default()));
            }
        };

        let symbol = name.symbol().unwrap();

        let entry = self
            .types
            .get_symbol(&symbol)
            .cloned()
            .ok_or(IRError::TypeNotFound(format!(
                "no type found for {symbol:?}"
            )))
            .unwrap();

        let (ty, substitutions) = self.specialize(&entry, expr.id)?;
        _ = self.monomorphize_name(name.clone(), &substitutions);

        Ok((ty, substitutions))
    }

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
                                .unwrap();

                            substitutions.ty.insert(*param, ty.clone());
                        }

                        ForAll::Row(param) => {
                            let row = self
                                .types
                                .catalog
                                .instantiations
                                .row
                                .get(&(id, *param))
                                .unwrap();

                            substitutions.row.insert(*param, row.clone());
                        }
                    };
                }

                let ty = substitute(scheme.ty.clone(), &substitutions);

                Ok((ty, substitutions))
            }
        }
    }

    fn ty_from_id(&self, id: &NodeID) -> Result<Ty, IRError> {
        match self.types.get(id) {
            Some(TypeEntry::Mono(ty)) => Ok(ty.clone()),
            Some(TypeEntry::Poly(scheme)) => Ok(scheme.ty.clone()),
            None => Err(IRError::TypeNotFound(format!("{id:?}"))),
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
                    Err(IRError::TypeNotFound(format!("{symbol}")))
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
            .get(&type_param_id)
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
        Ty::Record(box row) => Ty::Record(substitute_row(row, substitutions).into()),
        Ty::Nominal { symbol, box row } => Ty::Nominal {
            symbol,
            row: substitute_row(row, substitutions).into(),
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

fn is_main_func(node: &Node) -> bool {
    if let Node::Decl(Decl {
        kind:
            DeclKind::Let {
                value:
                    Some(Expr {
                        kind:
                            ExprKind::Func(Func {
                                name: Name::Resolved(Symbol::Global(..), name),
                                ..
                            }),
                        ..
                    }),
                ..
            },
        ..
    }) = node
        && name == "main"
    {
        return true;
    }

    false
}

pub fn curry_ty<'a, I: IntoIterator<Item = &'a Ty>>(params: I, ret: Ty) -> Ty {
    params
        .into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rfold(ret, |acc, p| Ty::Func(Box::new(p.clone()), Box::new(acc)))
}

#[cfg(test)]
pub mod tests {
    use crate::{
        assert_eq_diff, assert_eq_diff_display,
        compiling::{
            driver::{Driver, Source},
            module::ModuleId,
        },
        ir::{
            basic_block::{BasicBlock, BasicBlockId},
            function::Function,
            instruction::{Instruction, InstructionMeta},
            ir_ty::IrTy,
            list::List,
            lowerer::Lowerer,
            program::Program,
            register::Register,
            terminator::Terminator,
            value::Value,
        },
        label::Label,
        name::Name,
        name_resolution::symbol::{GlobalId, InstanceMethodId, Symbol, SynthesizedId},
        node_id::NodeID,
        types::ty::Ty,
    };

    fn meta() -> List<InstructionMeta> {
        vec![InstructionMeta::Source(NodeID::ANY)].into()
    }

    pub fn lower(input: &str) -> Program {
        let driver = Driver::new_bare(vec![Source::from(input)], Default::default());
        let typed = driver
            .parse()
            .unwrap()
            .resolve_names()
            .unwrap()
            .typecheck()
            .unwrap();

        let lowerer = Lowerer::new(typed.phase.asts, typed.phase.types, typed.phase.symbols);
        lowerer.lower().unwrap()
    }

    #[test]
    fn lowers_int_literal() {
        let program = lower("func main() { 123 }");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(GlobalId::from(1).into() => Function {
                register_count: 1,
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt { dest: 0.into(), val: 123, meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_float_literal() {
        let program = lower("func main() { 1.23 }");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(GlobalId::from(1).into() => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
                register_count: 1,
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Float.into()),
                blocks: vec![BasicBlock {
                id: BasicBlockId(0),
                instructions: vec![
                    Instruction::ConstantFloat { dest: 0.into(), val: 1.23, meta: vec![InstructionMeta::Source(NodeID::ANY)].into() }
                ],
                terminator: Terminator::Ret {
                    val: Value::Reg(0),
                    ty: IrTy::Float
                }
                }],
            })
        );
    }

    #[test]
    fn synthesizes_main() {
        let program = lower("123");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(SynthesizedId::from(1).into() => Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 1,
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                    blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt { dest: 0.into(), val: 123, meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_variables() {
        let program = lower("let a = 123 ; a");
        assert_eq!(
            program.functions,
            indexmap::indexmap!(SynthesizedId::from(1).into() => Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 1,
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                    blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt { dest: 0.into(), val: 123, meta: vec![InstructionMeta::Source(NodeID::ANY)].into(), }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn lowers_func_call() {
        let program = lower(
            "
        func foo(x: Int) { x }
        foo(123)
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 3,
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                            val: Value::Func(Name::Resolved(
                                GlobalId::from(1).into(),
                                "foo".into()
                            ))
                        },
                        Instruction::ConstantInt {
                            dest: 2.into(),
                            val: 123,
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                GlobalId::from(1).into(),
                                "foo".into()
                            )),
                            args: vec![Value::Reg(2)].into(),
                            meta: meta()
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(1),
                        ty: IrTy::Int
                    }
                }],
            }
        );
        assert_eq!(
            *program
                .functions
                .get(&Symbol::from(GlobalId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(GlobalId::from(1).into(), "foo".into()),
                params: vec![Value::Reg(0)].into(),
                register_count: 1,
                ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn lowers_struct_init_and_member() {
        let program = lower(
            "
        struct Foo { let bar: Int }
        Foo(bar: 123).bar
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(2)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(2).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 4,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 1.into(),
                            val: 123,
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 2.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(1)),
                                "@Foo:Type(_:1)_init".into(),
                            )),
                            args: vec![Register(2).into(), Register(1).into()].into(),
                            meta: meta(),
                        },
                        Instruction::GetField {
                            dest: 3.into(),
                            ty: IrTy::Int,
                            record: Register(0),
                            field: Label::Named("bar".into()),
                            meta: meta(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn monomorphizes_structs() {
        let program = lower(
            "
        struct Foo<T> { let bar: T }
        Foo(bar: 123).bar
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(2)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(2).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 4,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 1.into(),
                            val: 123,
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 2.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(4)),
                                "@@Foo:Type(_:1)_init:Synthesized(_:1)[Int]".into()
                            )),
                            args: vec![Register(2).into(), Register(1).into()].into(),
                            meta: meta(),
                        },
                        Instruction::GetField {
                            dest: 3.into(),
                            ty: IrTy::Int,
                            record: Register(0),
                            field: Label::Named("bar".into()),
                            meta: meta(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn lowers_add() {
        let program = lower("1 + 2");
        assert_eq_diff_display!(
            *program
                .functions
                .get(&Symbol::Synthesized(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                register_count: 1,
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 1.into(),
                            val: 2,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into(),
                        },
                        Instruction::ConstantInt {
                            dest: 2.into(),
                            val: 1,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into(),
                        },
                        Instruction::Call {
                            dest: Register(0),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                Symbol::Global(GlobalId {
                                    module_id: ModuleId::Core,
                                    local_id: 1
                                }),
                                "add".into()
                            )),
                            args: vec![Register(1).into(), Register(2).into()].into(),
                            meta: meta()
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn lowers_struct_method() {
        let program = lower(
            "
        struct Foo {
            let bar: Int

            func getBar() {
                self.bar
            }
        }

        Foo(bar: 123).getBar()
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(2)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(2).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 4,
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 2.into(),
                            val: 123,
                            meta: meta()
                        },
                        Instruction::Record {
                            dest: 3.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(1)),
                                "@Foo:Type(_:1)_init".into()
                            )),
                            args: vec![Register(3).into(), Register(2).into()].into(),
                            meta: meta(),
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                InstanceMethodId::from(1).into(),
                                "getBar".into()
                            )),
                            args: vec![Register(1).into()].into(),
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn embedded_ir() {
        let program = lower(
            "
        __IR<Int>(\"$? = add int 1 2\")
        ",
        );
        assert_eq!(
            program.functions,
            indexmap::indexmap!(SynthesizedId::from(1).into() => Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 1,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![Instruction::Add {
                        dest: 0.into(),
                        ty: IrTy::Int,
                        a: Value::Int(1),
                        b: Value::Int(2),
                        meta: vec![].into(),
                    }],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            })
        );
    }

    #[test]
    fn embedded_ir_uses_variables() {
        let program = lower(
            "
        let a = 1
        let b = 2
        __IR<Int>(\"$? = add int %0 %1\")
        ",
        );
        assert_eq!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                register_count: 3,
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 0.into(),
                            val: 1,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::ConstantInt {
                            dest: 1.into(),
                            val: 2,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Add {
                            dest: 2.into(),
                            ty: IrTy::Int,
                            a: Value::Reg(0),
                            b: Value::Reg(1),
                            meta: vec![].into(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(2),
                        ty: IrTy::Int
                    }
                }],
            }
        );
    }

    #[test]
    fn monomorphizes_simple_generic_func() {
        let program = lower(
            "
            func id(x) { x }
            id(123)
            id(1.23)
        ",
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(1)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(1).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Float.into()),
                register_count: 5,
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::Ref {
                            dest: 0.into(),
                            ty: IrTy::Func(vec![IrTy::Void], IrTy::Void.into()),
                            val: Value::Func(Name::Resolved(
                                Symbol::Global(GlobalId::from(1)),
                                "id".into()
                            ))
                        },
                        Instruction::ConstantInt {
                            dest: 2.into(),
                            val: 123,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Int,
                            callee: Value::Func(Name::Resolved(
                                Symbol::Synthesized(SynthesizedId::from(4)),
                                "@id:Global(_:1)[Int]".into()
                            )),
                            args: vec![Value::Reg(2)].into(),
                            meta: meta(),
                        },
                        Instruction::ConstantFloat {
                            dest: 4.into(),
                            val: 1.23,
                            meta: vec![InstructionMeta::Source(NodeID::ANY)].into()
                        },
                        Instruction::Call {
                            dest: 3.into(),
                            ty: IrTy::Float,
                            callee: Value::Func(Name::Resolved(
                                Symbol::Synthesized(SynthesizedId::from(7)),
                                "@id:Global(_:1)[Float]".into()
                            )),
                            args: vec![Value::Reg(4)].into(),
                            meta: meta(),
                        },
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(3),
                        ty: IrTy::Float
                    }
                }],
            }
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(3)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(3).into(), "@id:Global(_:1)[Int]".into()),
                params: vec![Value::Reg(0)].into(),
                ty: IrTy::Func(vec![IrTy::Int], IrTy::Int.into()),
                register_count: 1,
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Int
                    }
                }],
            }
        );

        assert_eq_diff!(
            *program
                .functions
                .get(&Symbol::from(SynthesizedId::from(5)))
                .unwrap(),
            Function {
                name: Name::Resolved(
                    SynthesizedId::from(5).into(),
                    "@id:Global(_:1)[Float]".into()
                ),
                params: vec![Value::Reg(0)].into(),
                ty: IrTy::Func(vec![IrTy::Float], IrTy::Float.into()),
                register_count: 1,
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![],
                    terminator: Terminator::Ret {
                        val: Value::Reg(0),
                        ty: IrTy::Float
                    }
                }],
            }
        );
    }
}
