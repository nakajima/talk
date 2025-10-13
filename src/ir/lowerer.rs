use crate::formatter;
use crate::ir::ir_ty::IrTy;
use crate::ir::parse_instruction;
use crate::label::Label;
use crate::node_kinds::parameter::Parameter;
use crate::types::infer_ty::TypeParamId;
use crate::types::row::Row;
use crate::types::scheme::Scheme;
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

#[derive(Clone)]
pub(super) struct PolyFunction {
    pub name: Name,
    pub foralls: Vec<ForAll>,
    pub params: Vec<Value>,
    pub blocks: Vec<BasicBlock<Ty, Label>>,
    pub ty: Ty,
}

// Lowers an AST with Types to a monomorphized IR
pub struct Lowerer {
    pub(super) asts: IndexMap<Source, AST<NameResolved>>,
    pub(super) types: Types,
    pub(super) functions: FxHashMap<Symbol, PolyFunction>,
    pub(super) current_function_stack: Vec<CurrentFunction>,
    pub(super) needs_monomorphization: Vec<Name>,
    pub(super) instantiations: FxHashMap<NodeID, FxHashMap<ForAll, Ty>>,

    bindings: FxHashMap<Symbol, Register>,
}

impl Lowerer {
    pub fn new(asts: IndexMap<Source, AST<NameResolved>>, types: Types) -> Self {
        Self {
            asts,
            types,
            functions: Default::default(),
            current_function_stack: Default::default(),
            needs_monomorphization: Default::default(),
            instantiations: Default::default(),
            bindings: Default::default(),
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
            let mut ret_ty = Ty::Void;
            let func = Func {
                id: NodeID(FileID::SYNTHESIZED, 0),
                name: Name::Resolved(Symbol::Synthesized(SynthesizedId::from(0)), "main".into()),
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
                NodeID(FileID::SYNTHESIZED, 0),
                TypeEntry::Mono(Ty::Func(Ty::Void.into(), ret_ty.into())),
            );
        }

        self.current_function_stack.push(CurrentFunction::default());

        for ast in asts.values_mut() {
            for root in ast.roots.iter() {
                self.lower_node(root)?;
            }
        }

        let mut monomorphizer = Monomorphizer::new(self);

        Ok(Program {
            functions: monomorphizer.monomorphize(),
        })
    }

    fn lower_node(&mut self, node: &Node) -> Result<Value, IRError> {
        match node {
            Node::Decl(decl) => self.lower_decl(decl),
            Node::Stmt(stmt) => self.lower_stmt(stmt),
            _ => unreachable!("node not handled: {node:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, decl), fields(decl.id = %decl.id))]
    fn lower_decl(&mut self, decl: &Decl) -> Result<Value, IRError> {
        match &decl.kind {
            DeclKind::Let {
                lhs,
                value: Some(value),
                ..
            } => {
                let bind = self.lower_pattern(lhs)?;
                self.lower_expr(value, bind)?;
            }
            DeclKind::Struct { body, .. } => {
                for node in &body.body {
                    self.lower_node(node)?;
                }
            }
            DeclKind::Init { name, params, body } => {
                self.lower_init(decl, name, params, body)?;
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
        self.lower_func(func, Bind::Discard)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_init(
        &mut self,
        decl: &Decl,
        name: &Name,
        params: &[Parameter],
        body: &Block,
    ) -> Result<Value, IRError> {
        let (func_ty, foralls) = match self.types.get_symbol(&name.symbol().unwrap()).unwrap() {
            TypeEntry::Mono(ty) => (ty.clone(), vec![]),
            TypeEntry::Poly(scheme) => (scheme.ty.clone(), scheme.foralls.clone()),
        };

        // Uncurry the function type to extract all param types and the final return type

        let Ty::Func(param, box ret_ty) = func_ty else {
            unreachable!();
        };
        let param_tys = param.uncurry_params();

        // Build param_ty from all params (for now, just use the first one for compatibility)
        let param_ty = if !param_tys.is_empty() {
            param_tys[0].clone()
        } else {
            let meta = Default::default();
            let formatter = formatter::Formatter::new(&meta);
            unreachable!(
                "init has no params - id: {:?}, sym: {:?}, ty: {:?}, {:?}",
                decl.id,
                self.types.get_symbol(&name.symbol().unwrap()).unwrap(),
                self.types.get(&decl.id).unwrap(),
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
            ret = self.lower_node(node)?;
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
                foralls,
                ty: Ty::Func(Box::new(param_ty.clone()), Box::new(ret_ty.clone())),
            },
        );

        Ok(ret)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, stmt), fields(stmt.id = %stmt.id))]
    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<Value, IRError> {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.lower_expr(expr, Bind::Fresh),
            StmtKind::If(_expr, _block, _block1) => todo!(),
            StmtKind::Return(_expr) => todo!(),
            StmtKind::Break => todo!(),
            StmtKind::Assignment(lhs, rhs) => self.lower_assignment(lhs, rhs),
            StmtKind::Loop(_expr, _block) => todo!(),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, lhs, rhs), fields(lhs.id = %lhs.id, rhs.id = %rhs.id))]
    fn lower_assignment(&mut self, lhs: &Expr, rhs: &Expr) -> Result<Value, IRError> {
        let lvalue = self.lower_lvalue(lhs)?;
        let value = self.lower_expr(rhs, Bind::Fresh)?;

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
                let base_ty = self.get_ty(base).expect("didn't get base ty");

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
    fn lower_expr(&mut self, expr: &Expr, bind: Bind) -> Result<Value, IRError> {
        match &expr.kind {
            ExprKind::Func(func) => self.lower_func(func, bind),
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
            } => self.lower_call(expr.id, callee, args, bind),
            ExprKind::Member(member, label, ..) => self.lower_member(expr.id, member, label, bind),
            ExprKind::Variable(name) => self.lower_variable(name),
            ExprKind::Constructor(name) => self.lower_constructor(name, bind),
            ExprKind::If(..) => todo!(),
            ExprKind::Match(..) => todo!(),
            ExprKind::RecordLiteral { .. } => todo!(),
            ExprKind::RowVariable(..) => todo!(),
            _ => unreachable!("cannot lower expr: {expr:?}"),
        }
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_constructor(&mut self, name: &Name, bind: Bind) -> Result<Value, IRError> {
        let init_sym = *self
            .types
            .catalog
            .initializers
            .get(&name.symbol().unwrap())
            .unwrap()
            .get(&Label::Named("init".into()))
            .unwrap();

        let dest = self.ret(bind);
        let ty = self.types.get_symbol(&init_sym).unwrap();
        self.push_instr(Instruction::Ref {
            dest,
            ty: match ty {
                TypeEntry::Mono(ty) => ty.clone(),
                TypeEntry::Poly(scheme) => scheme.ty.clone(),
            },
            val: Value::Func(Name::Resolved(
                init_sym,
                format!("{}_init", name.name_str()),
            )),
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
    ) -> Result<Value, IRError> {
        if let Some(box receiver) = &receiver {
            let reg = self.next_register();
            let member_bind = Bind::Assigned(reg);
            let receiver_val = self.lower_expr(receiver, member_bind)?;
            let ty = self.ty_from_id(&id)?;
            let dest = self.ret(bind);

            let receiver_ty = self.get_ty(receiver)?;

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
    fn lower_variable(&mut self, name: &Name) -> Result<Value, IRError> {
        let ty = self
            .types
            .get_symbol(&name.symbol().unwrap())
            .unwrap_or_else(|| panic!("did not get variable type: {name:?}"));

        let ret = if matches!(
            ty,
            TypeEntry::Mono(Ty::Func(..))
                | TypeEntry::Poly(Scheme {
                    ty: Ty::Func(..),
                    ..
                })
        ) {
            // It's a func reference so we pass the name
            Value::Func(name.clone())
        } else {
            self.bindings.get(&name.symbol().unwrap()).unwrap().into()
        };

        Ok(ret)
    }

    #[instrument(level = tracing::Level::TRACE, skip(self))]
    fn lower_constructor_call(
        &mut self,
        id: NodeID,
        name: &Name,
        callee: &Expr,
        callee_val: &Value,
        mut args: Vec<Value>,
        dest: Register,
    ) -> Result<Value, IRError> {
        let record_dest = self.next_register();
        let ty = self.get_ty(callee)?;

        let properties = self
            .types
            .catalog
            .properties
            .get(&name.symbol().unwrap())
            .unwrap();

        self.push_instr(Instruction::Record {
            dest: record_dest,
            ty: ty.clone(),
            record: properties
                .iter()
                .map(|_| Value::Uninit)
                .collect::<Vec<_>>()
                .into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });
        args.insert(0, record_dest.into());

        let init_sym = *self
            .types
            .catalog
            .initializers
            .get(&name.symbol().unwrap())
            .unwrap()
            .get(&Label::Named("init".into()))
            .unwrap();

        let ty @ Ty::Func(..) = &self.ty_from_symbol(&init_sym).unwrap() else {
            unreachable!("{:?}", self.ty_from_symbol(&init_sym).unwrap());
        };
        let mut params = ty.clone().uncurry_params();
        let ret = params.pop().unwrap();
        params.insert(0, ret.clone());

        self.push_instr(Instruction::Call {
            dest,
            ty: ret.clone(),
            callee: Value::Func(Name::Resolved(
                init_sym,
                format!("{}_init", name.name_str()),
            )),
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
    ) -> Result<Value, IRError> {
        let dest = self.ret(bind);

        // Handle embedded IR call
        if let ExprKind::Variable(name) = &callee.kind
            && name.symbol().unwrap() == Symbol::IR
        {
            return self.lower_embedded_ir_call(args, dest);
        }

        let callee_ty = self.get_ty(callee).unwrap();
        println!("callee_entry: {callee_ty:?}");

        let ty = self.ty_from_id(&id)?;
        let mut args = args
            .iter()
            .map(|arg| self.lower_expr(&arg.value, Bind::Fresh))
            .collect::<Result<Vec<Value>, _>>()?;

        let callee_ir = if let ExprKind::Member(Some(box receiver), member, ..) = &callee.kind
            && let Some(method_sym) = self.lookup_instance_method(receiver, member)?
        {
            // Handle method calls. It'd be nice if we could re-use lower_member here but i'm not sure
            // how we'd get the receiver value, which we need to pass as the first arg..
            let receiver_ir = self.lower_expr(receiver, Bind::Fresh)?;
            args.insert(0, receiver_ir);
            Value::Func(Name::Resolved(method_sym, member.to_string()))
        } else {
            self.lower_expr(callee, Bind::Fresh)?
        };

        if let ExprKind::Constructor(name) = &callee.kind {
            return self.lower_constructor_call(callee.id, name, callee, &callee_ir, args, dest);
        }

        self.push_instr(Instruction::Call {
            dest,
            ty,
            callee: callee_ir,
            args: args.into(),
            meta: vec![InstructionMeta::Source(id)].into(),
        });

        Ok(dest.into())
    }

    #[instrument(level = tracing::Level::TRACE, skip(self, func), fields(func = %func.name))]
    fn lower_func(&mut self, func: &Func, bind: Bind) -> Result<Value, IRError> {
        let ty = self.ty_from_id(&func.id)?;

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
            ret = self.lower_node(node)?;
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
                foralls: Default::default(),
                ty: Ty::Func(param_tys.clone(), ret_ty.clone().into()),
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

    fn lookup_instance_method(
        &self,
        expr: &Expr,
        label: &Label,
    ) -> Result<Option<Symbol>, IRError> {
        let Ty::Nominal { symbol, .. } = self.get_ty(expr)? else {
            return Ok(None);
        };

        if let Some(methods) = self.types.catalog.instance_methods.get(&symbol)
            && let Some(method) = methods.get(label)
        {
            return Ok(Some(*method));
        }

        Ok(None)
    }

    fn get_ty(&self, expr: &Expr) -> Result<Ty, IRError> {
        let symbol = match &expr.kind {
            ExprKind::Variable(name) => name.symbol().unwrap(),
            ExprKind::Func(func) => func.name.symbol().unwrap(),
            ExprKind::Constructor(name) => name.symbol().unwrap(),
            _ => return self.ty_from_id(&expr.id),
        };

        let entry = self
            .types
            .get_symbol(&symbol)
            .ok_or(IRError::TypeNotFound(format!(
                "no type found for {symbol:?}"
            )))
            .unwrap();

        match entry {
            TypeEntry::Mono(ty) => Ok(ty.clone()),
            TypeEntry::Poly(scheme) => {
                let mut substitutions = FxHashMap::<TypeParamId, Ty>::default();
                for forall in scheme.foralls.iter() {
                    let ForAll::Ty(param) = forall else { continue };
                    let concrete = self
                        .types
                        .catalog
                        .instantiations
                        .get(&(expr.id, *param))
                        .unwrap();

                    substitutions.insert(*param, concrete.clone());
                }

                let ty = substitute(scheme.ty.clone(), &substitutions);
                println!("BEFORE: {:?}\nAFTER: {ty:?}", scheme.ty);

                Ok(ty)
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
            None => Err(IRError::TypeNotFound(format!("{symbol}"))),
        }
    }
}

fn substitute(ty: Ty, substitutions: &FxHashMap<TypeParamId, Ty>) -> Ty {
    match ty {
        Ty::Primitive(..) => ty,
        Ty::Param(type_param_id) => substitutions.get(&type_param_id).unwrap().clone(),
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
        Ty::Nominal {
            symbol,
            type_args,
            box row,
        } => Ty::Nominal {
            symbol,
            type_args: type_args
                .into_iter()
                .map(|a| substitute(a, substitutions))
                .collect(),
            row: substitute_row(row, substitutions).into(),
        },
    }
}

fn substitute_row(row: Row, substitutions: &FxHashMap<TypeParamId, Ty>) -> Row {
    match row {
        Row::Empty(..) => row,
        Row::Param(..) => row,
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
        assert_eq_diff,
        compiling::driver::{Driver, Source},
        fxhashmap,
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

        let lowerer = Lowerer::new(typed.phase.asts, typed.phase.types);
        lowerer.lower().unwrap()
    }

    #[test]
    fn lowers_int_literal() {
        let program = lower("func main() { 123 }");
        assert_eq!(
            program.functions,
            fxhashmap!(GlobalId::from(1).into() => Function {
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
            fxhashmap!(GlobalId::from(1).into() => Function {
                name: Name::Resolved(GlobalId::from(1).into(), "main".into()),
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
            fxhashmap!(SynthesizedId::from(0).into() => Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
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
    fn lowers_variables() {
        let program = lower("let a = 123 ; a");
        assert_eq!(
            program.functions,
            fxhashmap!(SynthesizedId::from(0).into() => Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
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
                .get(&Symbol::from(SynthesizedId::from(0)))
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
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
                .get(&SynthesizedId::from(0).into())
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 1.into(),
                            val: 123,
                            meta: meta()
                        },
                        Instruction::Ref {
                            dest: 2.into(),
                            ty: IrTy::Func(
                                vec![IrTy::Record(vec![IrTy::Int]), IrTy::Int],
                                IrTy::Record(vec![IrTy::Int]).into()
                            ),
                            val: Value::Func(Name::Resolved(
                                SynthesizedId::from(1).into(),
                                "Foo_init".into()
                            ))
                        },
                        Instruction::Record {
                            dest: 3.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 0.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(1)),
                                "Foo_init".into()
                            )),
                            args: vec![Register(3).into(), Register(1).into()].into(),
                            meta: meta(),
                        },
                        Instruction::GetField {
                            dest: 4.into(),
                            ty: IrTy::Int,
                            record: Register(0),
                            field: Label::Named("bar".into()),
                            meta: meta(),
                        }
                    ],
                    terminator: Terminator::Ret {
                        val: Value::Reg(4),
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
                .get(&SynthesizedId::from(0).into())
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
                blocks: vec![BasicBlock::<IrTy, Label> {
                    id: BasicBlockId(0),
                    instructions: vec![
                        Instruction::ConstantInt {
                            dest: 2.into(),
                            val: 123,
                            meta: meta()
                        },
                        Instruction::Ref {
                            dest: 3.into(),
                            ty: IrTy::Func(
                                vec![IrTy::Record(vec![IrTy::Int]), IrTy::Int],
                                IrTy::Record(vec![IrTy::Int]).into()
                            ),
                            val: Value::Func(Name::Resolved(
                                SynthesizedId::from(1).into(),
                                "Foo_init".into()
                            ))
                        },
                        Instruction::Record {
                            dest: 4.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            record: vec![Value::Uninit].into(),
                            meta: meta()
                        },
                        Instruction::Call {
                            dest: 1.into(),
                            ty: IrTy::Record(vec![IrTy::Int]),
                            callee: Value::Func(Name::Resolved(
                                Symbol::from(SynthesizedId::from(1)),
                                "Foo_init".into()
                            )),
                            args: vec![Register(4).into(), Register(2).into()].into(),
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
            fxhashmap!(SynthesizedId::from(0).into() => Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
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
                .get(&SynthesizedId::from(0).into())
                .unwrap(),
            Function {
                name: Name::Resolved(SynthesizedId::from(0).into(), "main".into()),
                params: vec![].into(),
                ty: IrTy::Func(vec![], IrTy::Int.into()),
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

        println!("{program}");
    }
}
