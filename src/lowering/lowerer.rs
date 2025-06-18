use std::{collections::HashMap, ops::AddAssign, str::FromStr};

use crate::{
    Lowered, SourceFile, SymbolID, SymbolInfo, SymbolKind, SymbolTable, Typed,
    analysis::{
        cfg::ControlFlowGraph, function_analysis::definite_initialization::DefiniteInitizationPass,
        function_analysis_pass::FunctionAnalysisPass,
    },
    diagnostic::Diagnostic,
    environment::{StructDef, TypeDef},
    expr::{Expr, ExprMeta, Pattern},
    lowering::{
        instr::Instr, ir_error::IRError, ir_module::IRModule, ir_type::IRType,
        parsing::parser::ParserError, register::Register,
    },
    name::Name,
    parser::ExprID,
    token::Token,
    token_kind::TokenKind,
    type_checker::Ty,
    typed_expr::TypedExpr,
};

#[derive(Debug, Clone, PartialEq)]
pub enum RefKind {
    Func(String),
}

impl FromStr for RefKind {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The string representation of a RefKind::Func is just the function name,
        // which starts with '@'.
        if s.starts_with('@') {
            Ok(RefKind::Func(s.to_string()))
        } else {
            Err(ParserError::UnexpectedToken(
                vec![],
                crate::lowering::parsing::lexer::Tokind::Identifier(s.to_string()),
            ))
        }
    }
}

impl std::fmt::Display for RefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // f.write_str("ref ")?;
        match self {
            Self::Func(name) => f.write_str(name)?,
        };
        Ok(())
    }
}

impl Ty {
    pub(super) fn to_ir(&self, lowerer: &Lowerer) -> IRType {
        match self {
            Ty::Pointer => IRType::Pointer,
            Ty::Init(_, params) => IRType::Func(
                params.iter().map(|t| t.to_ir(lowerer)).collect(),
                IRType::Void.into(),
            ),
            Ty::Void => IRType::Void,
            Ty::Int => IRType::Int,
            Ty::Bool => IRType::Bool,
            Ty::Float => IRType::Float,
            Ty::Func(items, ty, _generics) => IRType::Func(
                items.iter().map(|t| t.to_ir(lowerer)).collect(),
                Box::new(ty.to_ir(lowerer)),
            ),
            Ty::TypeVar(type_var_id) => IRType::TypeVar(format!("T{}", type_var_id.0)),
            Ty::Enum(_symbol_id, generics) => {
                IRType::Enum(generics.iter().map(|i| i.to_ir(lowerer)).collect())
            }
            Ty::EnumVariant(_symbol_id, _items) => todo!(),
            Ty::Closure { func, .. } => func.to_ir(lowerer),
            Ty::Tuple(_items) => todo!(),
            Ty::Array(_) => todo!(),
            Ty::Struct(symbol_id, _generics) => {
                let Some(TypeDef::Struct(struct_def)) = lowerer.source_file.type_def(symbol_id)
                else {
                    panic!("Unable to determine definition of struct: {symbol_id:?}");
                };

                IRType::Struct(
                    *symbol_id,
                    struct_def
                        .properties
                        .values()
                        .map(|p| p.ty.to_ir(lowerer))
                        .collect(),
                )
            }
        }
    }
}

pub enum IRPattern {
    Bind,
    Wildcard,
    EnumVariant { tag: u32, bindings: Vec<IRType> },
    IntLiteral(i64),
    FloatLiteral(f64),
    LiteralBool(bool),
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub struct BasicBlockID(pub u32);

impl BasicBlockID {
    pub const ENTRY: BasicBlockID = BasicBlockID(0);
}

impl AddAssign<u32> for BasicBlockID {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs
    }
}

impl FromStr for BasicBlockID {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "entry" {
            Ok(BasicBlockID(0))
        } else {
            Ok(BasicBlockID(str::parse(&s[1..]).unwrap()))
        }
    }
}

impl std::fmt::Display for BasicBlockID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub id: BasicBlockID,
    pub instructions: Vec<Instr>,
}

impl BasicBlock {
    fn push_instr(&mut self, instr: Instr) {
        self.instructions.push(instr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PhiPredecessors(pub Vec<(Register, BasicBlockID)>);

impl std::fmt::Display for PhiPredecessors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (i, (reg, id)) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{id}: {reg}")?;
        }
        f.write_str("]")?;
        Ok(())
    }
}

impl FromStr for PhiPredecessors {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let inner = s
            .trim()
            .strip_prefix('[')
            .and_then(|s| s.strip_suffix(']'))
            .ok_or(ParserError::UnexpectedEOF)?;

        if inner.trim().is_empty() {
            return Ok(PhiPredecessors(vec![]));
        }

        inner
            .split(',')
            .map(|pair_str| {
                let mut parts = pair_str.trim().splitn(2, ':');

                let bb_str = parts.next().ok_or(ParserError::UnexpectedEOF)?.trim();
                let reg_str = parts.next().ok_or(ParserError::UnexpectedEOF)?.trim();

                let bb = bb_str.parse::<BasicBlockID>()?;
                let reg = reg_str.parse::<Register>().map_err(ParserError::from)?;

                Ok((reg, bb))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(PhiPredecessors)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RegisterList(pub Vec<Register>);

impl RegisterList {
    pub const EMPTY: RegisterList = RegisterList(vec![]);
}

impl From<Vec<Register>> for RegisterList {
    fn from(value: Vec<Register>) -> Self {
        Self(value)
    }
}

impl std::fmt::Display for RegisterList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, reg) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{reg}")?;
        }
        Ok(())
    }
}

// Replace the old implementation with this one.
impl FromStr for RegisterList {
    type Err = ParserError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The input 's' is the content *between* the parentheses, e.g., "%1, %2" or "".
        let s = s.trim();
        if s.is_empty() {
            // Correctly handle the case of zero arguments.
            return Ok(RegisterList(vec![]));
        }

        // For non-empty arguments, split by comma and parse each part.
        s.split(',')
            .map(|part| part.trim().parse::<Register>())
            .collect::<Result<Vec<Register>, _>>()
            .map(RegisterList)
            .map_err(|e| e.into())
    }
}

#[derive(Debug, Clone)]
pub enum SymbolValue {
    Register(Register),
    Capture(usize, IRType),
    Struct(StructDef),
}

impl From<Register> for SymbolValue {
    fn from(value: Register) -> Self {
        Self::Register(value)
    }
}

#[derive(Debug)]
struct CurrentFunction {
    current_block_idx: usize,
    next_block_id: BasicBlockID,
    blocks: Vec<BasicBlock>,
    env_ty: IRType,
    pub registers: RegisterAllocator,
    pub symbol_registers: HashMap<SymbolID, SymbolValue>,
}

impl CurrentFunction {
    #[track_caller]
    fn new(env_ty: IRType) -> Self {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!("new CurrentFunction from {}:{}", loc.file(), loc.line());
        }
        Self {
            next_block_id: BasicBlockID(0),
            current_block_idx: 0,
            blocks: Default::default(),
            env_ty,
            registers: RegisterAllocator::new(),
            symbol_registers: Default::default(),
        }
    }

    fn next_block_id(&mut self) -> BasicBlockID {
        let id = self.next_block_id;
        self.next_block_id += 1;
        id
    }

    fn add_block(&mut self, block: BasicBlock) {
        self.blocks.push(block);
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        &mut self.blocks[self.current_block_idx]
    }

    fn set_current_block(&mut self, id: BasicBlockID) {
        let index = self.blocks.iter().position(|blk| blk.id == id).unwrap();
        self.current_block_idx = index;
    }

    #[track_caller]
    fn register_symbol(&mut self, symbol_id: SymbolID, register: SymbolValue) {
        if cfg!(debug_assertions) {
            let loc = std::panic::Location::caller();
            log::trace!(
                "register symbol {:?}: {:?} from {}:{}",
                symbol_id,
                register,
                loc.file(),
                loc.line()
            );
        }
        self.symbol_registers.insert(symbol_id, register);
    }

    fn lookup_symbol(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.symbol_registers.get(symbol_id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRFunction {
    pub ty: IRType,
    pub name: String,
    pub blocks: Vec<BasicBlock>,
    pub env_ty: IRType,
    pub env_reg: Register,
}

impl IRFunction {
    pub(crate) fn args(&self) -> &[IRType] {
        let (IRType::Func(ref args, _) | IRType::Struct(_, ref args)) = self.ty else {
            unreachable!("didn't get func for ty: {:?}", self.ty)
        };

        args
    }

    pub(crate) fn ret(&self) -> &IRType {
        if let IRType::Func(_, ref ret) = self.ty {
            return ret;
        };

        if let IRType::Struct(_, _) = self.ty {
            return &self.ty;
        };

        unreachable!()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct RegisterAllocator {
    next_id: i32,
}

impl RegisterAllocator {
    fn new() -> Self {
        log::trace!("new register allocator");
        Self { next_id: 0 }
    }

    fn allocate(&mut self) -> Register {
        let id = self.next_id;
        self.next_id += 1;
        Register(id)
    }
}

pub struct Lowerer<'a> {
    pub(super) source_file: SourceFile<Typed>,
    current_functions: Vec<CurrentFunction>,
    lowered_functions: Vec<IRFunction>,
    symbol_table: &'a mut SymbolTable,
}

impl<'a> Lowerer<'a> {
    pub fn new(source_file: SourceFile<Typed>, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            source_file,
            current_functions: vec![],
            lowered_functions: Default::default(),
            symbol_table,
        }
    }

    pub fn lower(mut self, module: &mut IRModule) -> SourceFile<Lowered> {
        let (expr_id, did_create) = find_or_create_main(&mut self.source_file, self.symbol_table);

        // If we created the main function, we need to set it up
        if did_create {
            // Make sure we have a current function
            self.current_functions
                .push(CurrentFunction::new(IRType::Struct(
                    SymbolID::GENERATED_MAIN,
                    vec![],
                )));

            // Make sure it has a basic block
            let entry = self.new_basic_block();
            self.set_current_block(entry);
        }

        self.lower_function(&expr_id);

        // If we created the main function, we moved all the typed roots into its body
        // so we don't need to lower them again.
        if !did_create {
            let typed_roots = self.source_file.typed_roots().to_owned();
            for root in typed_roots {
                if let Expr::Func { .. } = &root.expr {
                    self.lower_function(&root.id);
                }
            }
        }

        for function in self.lowered_functions {
            module.functions.push(function)
        }

        self.source_file.to_lowered()
    }

    pub fn lower_expr(&mut self, expr_id: &ExprID) -> Option<Register> {
        let Some(typed_expr) = self.source_file.typed_expr(expr_id).clone() else {
            return None;
        };

        match typed_expr.expr {
            Expr::LiteralInt(_)
            | Expr::LiteralFloat(_)
            | Expr::LiteralFalse
            | Expr::LiteralTrue => self.lower_literal(expr_id),
            Expr::Binary(_, _, _) => self.lower_binary_op(expr_id),
            Expr::Assignment(lhs, rhs) => self.lower_assignment(&lhs, &rhs),
            Expr::Variable(name, _) => self.lower_variable(expr_id, &name),
            Expr::If(_, _, _) => self.lower_if(expr_id),
            Expr::Block(_) => self.lower_block(expr_id),
            Expr::Call {
                callee,
                type_args,
                args,
            } => self.lower_call(callee, type_args, args, typed_expr.ty),
            Expr::Func { .. } => self.lower_function(expr_id),
            Expr::Return(rhs) => self.lower_return(expr_id, &rhs),
            Expr::EnumDecl(_, _, _) => None,
            Expr::Member(receiver, name) => {
                let member_ty = self.source_file.typed_expr(expr_id).unwrap().ty.to_ir(self);

                if !matches!(member_ty, IRType::Enum(_)) {
                    let member_ptr_reg = self.lower_member(&receiver, expr_id, &name)?;
                    let loaded_value_reg = self.allocate_register();
                    self.push_instr(Instr::Load {
                        dest: loaded_value_reg,
                        ty: member_ty,
                        addr: member_ptr_reg,
                    });

                    Some(loaded_value_reg)
                } else {
                    self.lower_member(&receiver, expr_id, &name)
                }
            }
            Expr::Match(scrutinee, arms) => self.lower_match(&scrutinee, &arms, &typed_expr.ty),
            Expr::CallArg { value, .. } => self.lower_expr(&value),
            Expr::Struct(Name::Resolved(struct_id, _), _, _) => {
                self.lower_struct(expr_id, struct_id)
            } // Nothing to be done here.
            Expr::Init(symbol_id, func_id) => self.lower_init(&symbol_id.unwrap(), &func_id),
            Expr::TypeRepr(_, _, _) => None, // these are just for the type system
            expr => {
                self.source_file.diagnostics.insert(Diagnostic::lowering(
                    *expr_id,
                    IRError::Unknown(format!("Cannot lower {:?}", expr)),
                ));

                None
            }
        }
    }

    fn lower_struct(&mut self, expr_id: &ExprID, struct_id: SymbolID) -> Option<Register> {
        let Some(TypeDef::Struct(struct_def)) = self.source_file.type_def(&struct_id).cloned()
        else {
            self.source_file.diagnostics.insert(Diagnostic::lowering(
                *expr_id,
                IRError::Unknown(format!(
                    "Could not resolve struct for symbol: {struct_id:?}"
                )),
            ));
            return None;
        };

        for initializer in &struct_def.initializers {
            self.lower_expr(initializer);

            // TODO this is awkward
            if let Some(init_func) = self.lowered_functions.last() {
                let cfg = ControlFlowGraph::new(init_func);
                let pass = DefiniteInitizationPass::new(struct_def.clone());
                match pass.run(init_func, &cfg) {
                    Ok(_) => (),
                    Err(e) => {
                        self.source_file
                            .diagnostics
                            .insert(Diagnostic::lowering(*initializer, e));
                    }
                }
            }
        }

        self.current_func_mut()
            .register_symbol(struct_id, SymbolValue::Struct(struct_def));

        None
    }

    fn lower_init(&mut self, symbol_id: &SymbolID, func_id: &ExprID) -> Option<Register> {
        let Some(TypeDef::Struct(struct_def)) = self.source_file.type_def(symbol_id).cloned()
        else {
            unreachable!()
        };
        let typed_func = self.source_file.typed_expr(func_id).unwrap();
        let Expr::Func { params, body, .. } = typed_func.expr else {
            unreachable!()
        };

        let struct_ty = IRType::Struct(
            *symbol_id,
            struct_def
                .properties
                .values()
                .map(|p| p.ty.to_ir(self))
                .collect(),
        );

        self.current_functions
            .push(CurrentFunction::new(struct_ty.clone()));
        let block_id = self.new_basic_block();
        self.set_current_block(block_id);

        // Define our env
        let env = self.allocate_register();
        self.current_func_mut()
            .register_symbol(*symbol_id, SymbolValue::Register(env));

        for param in params {
            let Expr::Parameter(Name::Resolved(symbol, _), _) =
                self.source_file.get(&param).unwrap().clone()
            else {
                self.push_err("Did not get parameter", param);
                return None;
            };

            let register = self.allocate_register();
            self.current_func_mut()
                .register_symbol(symbol, SymbolValue::Register(register));
        }

        self.lower_block(&body);

        let loaded_reg = self.allocate_register();
        self.push_instr(Instr::Load {
            dest: loaded_reg,
            ty: struct_ty.clone(),
            addr: env,
        });

        self.push_instr(Instr::Ret(struct_ty.clone(), Some(loaded_reg)));

        let Ty::Func(params, _ret, generics) = typed_func.ty else {
            return None;
        };

        // Override func type for init to always return the struct
        let init_func_ty = Ty::Func(
            params,
            Ty::Struct(
                *symbol_id,
                struct_def
                    .properties
                    .values()
                    .map(|p| p.ty.clone())
                    .collect(),
            )
            .into(),
            generics,
        );

        let name_str = struct_def.name_str.clone();
        let func = IRFunction {
            ty: init_func_ty.to_ir(self),
            name: Name::Resolved(*symbol_id, format!("{name_str}_init")).mangled(&init_func_ty),
            blocks: self.current_func_mut().blocks.clone(),
            env_ty: struct_ty,
            env_reg: env,
        };

        self.lowered_functions.push(func.clone());
        self.current_functions.pop();

        Some(loaded_reg)

        // Some(Register(1))
    }

    fn lower_function(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self
            .source_file
            .typed_expr(expr_id)
            .expect("Did not get typed expr");

        let Expr::Func {
            ref name,
            ref params,
            ref body,
            ref captures,
            ..
        } = typed_expr.expr
        else {
            panic!(
                "Attempted to lower non-function: {:?}",
                self.source_file.get(expr_id)
            );
        };

        let closure_ptr = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: closure_ptr,
            count: None,
            ty: IRType::closure(),
        });

        if let Some(Name::Resolved(symbol, _)) = name {
            self.current_func_mut()
                .register_symbol(*symbol, SymbolValue::Register(closure_ptr));
        }

        let (capture_types, capture_registers) = if let Ty::Closure {
            captures: capture_types,
            ..
        } = &typed_expr.ty
        {
            let Name::Resolved(self_symbol, _) = self.resolve_name(name.clone()) else {
                self.push_err(&format!("no symbol: {name:?}"), *expr_id);
                return None;
            };

            // Define an environment object for our captures. If there aren't any captures we don't care,
            // we're going to do it anyway. Maybe we can optimize it out later? I don't know if we'll have time.
            let mut capture_registers = vec![];
            let mut captured_ir_types = vec![];
            for (i, capture) in captures.iter().enumerate() {
                //     // It's recursive so we just need to pass the pointer
                //     capture_registers.push(closure_ptr);

                //     continue;
                // }

                let SymbolValue::Register(register) = self
                    .lookup_register(capture)
                    .expect("could not find register for capture")
                else {
                    todo!("don't know how to handle captured captures yet")
                };
                capture_registers.push(*register);

                if *capture == self_symbol {
                    captured_ir_types.push(IRType::Pointer);
                } else {
                    captured_ir_types.push(capture_types[i].to_ir(self));
                }
            }

            (captured_ir_types, capture_registers)
        } else {
            (vec![], vec![])
        };

        let environment_type = IRType::Struct(SymbolID::ENV, capture_types.clone());

        self.current_functions
            .push(CurrentFunction::new(environment_type));

        // Now that we're in the block, register the captures
        for (i, capture) in captures.iter().enumerate() {
            self.current_func_mut()
                .register_symbol(*capture, SymbolValue::Capture(i, capture_types[i].clone()));
        }

        let name = self.resolve_name(name.clone());

        log::trace!("lowering {name:?}");

        let Some(Expr::Block(body_exprs)) = self.source_file.get(body).cloned() else {
            panic!("did not get body")
        };

        let id = self.new_basic_block();
        self.set_current_block(id);

        let env_reg = self.allocate_register(); // Set aside our env register

        for param in params {
            let Expr::Parameter(Name::Resolved(symbol, _), _) =
                self.source_file.get(param).unwrap().clone()
            else {
                panic!("didn't get parameter")
            };

            let register = self.current_func_mut().registers.allocate();
            self.current_func_mut()
                .register_symbol(symbol, SymbolValue::Register(register));
        }

        for (i, id) in body_exprs.iter().enumerate() {
            let ret = if let Some(reg) = self.lower_expr(id) {
                let ty = self.source_file.typed_expr(id).unwrap().ty.to_ir(self);
                (ty, Some(reg))
            } else {
                (IRType::Void, None)
            };

            if i == body_exprs.len() - 1 {
                // we don't pass around functions, we pass around pointers (closures)
                let ty = if matches!(ret.0, IRType::Func(_, _)) {
                    IRType::Pointer
                } else {
                    ret.0
                };

                self.current_block_mut().push_instr(Instr::Ret(ty, ret.1));
            }
        }

        let func = IRFunction {
            ty: typed_expr.ty.to_ir(self),
            name: name.mangled(&typed_expr.ty),
            blocks: self.current_func_mut().blocks.clone(),
            env_ty: self.current_func().env_ty.clone(),
            env_reg,
        };
        self.lowered_functions.push(func.clone());
        self.current_functions.pop();

        let Name::Resolved(symbol, _) = name else {
            panic!("no symbol")
        };

        self.fill_closure(
            closure_ptr,
            RefKind::Func(name.mangled(&typed_expr.ty)),
            typed_expr.ty.to_ir(self),
            capture_types,
            capture_registers,
        );

        self.current_func_mut()
            .register_symbol(symbol, SymbolValue::Register(closure_ptr));

        Some(closure_ptr)
    }

    fn lower_match(&mut self, scrutinee: &ExprID, arms: &[ExprID], ty: &Ty) -> Option<Register> {
        let scrutinee_reg = self.lower_expr(scrutinee).unwrap();
        let merge_block_id = self.new_basic_block();

        // Pre-allocate all the blocks where we will check the condition for each arm.
        let arm_cond_blocks: Vec<_> = (0..arms.len()).map(|_| self.new_basic_block()).collect();

        // Jump to the first condition
        self.current_block_mut()
            .push_instr(Instr::Jump(arm_cond_blocks[0]));

        let fail_block_id = self.new_basic_block();
        self.set_current_block(fail_block_id);
        self.push_instr(Instr::Unreachable);

        let mut predecessors = vec![];
        for (i, arm) in arms.iter().enumerate() {
            predecessors.push(self.lower_match_arm(
                arm,
                &scrutinee_reg,
                merge_block_id,
                arm_cond_blocks[i],
                arm_cond_blocks.get(i + 1).cloned().unwrap_or(fail_block_id),
            ));
        }

        self.set_current_block(merge_block_id);

        let phi_reg = self.allocate_register();
        self.push_instr(Instr::Phi(
            phi_reg,
            ty.to_ir(self),
            PhiPredecessors(predecessors),
        ));

        Some(phi_reg)
    }

    fn lower_match_arm(
        &mut self,
        expr_id: &ExprID,
        scrutinee: &Register,
        merge_block_id: BasicBlockID,
        cond_block_id: BasicBlockID,
        else_block_id: BasicBlockID,
    ) -> (Register, BasicBlockID) {
        let typed_arm = self.source_file.typed_expr(expr_id).unwrap();
        let Expr::MatchArm(pattern_id, body_id) = typed_arm.expr else {
            panic!("Didn't get match arm: {typed_arm:?}");
        };

        let then_block_id = self.new_basic_block();

        self.lower_pattern_and_bind(
            &pattern_id,
            scrutinee,
            cond_block_id,
            then_block_id,
            else_block_id,
        );
        self.set_current_block(then_block_id);
        let body_ret_reg = self.lower_expr(&body_id).unwrap();

        // After evaluating body, jump to the merge
        self.push_instr(Instr::Jump(merge_block_id));

        (body_ret_reg, then_block_id)
    }

    fn lower_pattern_and_bind(
        &mut self,
        pattern_id: &ExprID,
        scrutinee_reg: &Register,
        cond_block_id: BasicBlockID,
        then_block_id: BasicBlockID,
        else_block_id: BasicBlockID,
    ) {
        let pattern_typed_expr = self.source_file.typed_expr(pattern_id).unwrap();
        let Expr::Pattern(pattern) = pattern_typed_expr.expr else {
            panic!("Expected a pattern expression");
        };

        self.set_current_block(cond_block_id);
        match pattern {
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                // 1. Get the tag for this variant from the enum definition.
                let Ty::Enum(enum_id, enum_generics) = &pattern_typed_expr.ty else {
                    panic!("did not get enum")
                };

                let TypeDef::Enum(type_def) = self.source_file.type_def(enum_id).cloned().unwrap()
                else {
                    unreachable!()
                };

                /* ... find variant by name in type_def ... */
                let (tag, variant_def) = type_def.tag_with_variant_for(&variant_name);

                // 2. Get the tag of the scrutinee.
                let tag_reg = self.allocate_register();
                self.push_instr(Instr::GetEnumTag(tag_reg, *scrutinee_reg));

                // 3. Compare with the expected tag.
                let expected_tag_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(expected_tag_reg, tag as i64));
                let tags_match_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    tags_match_reg,
                    IRType::Int,
                    tag_reg,
                    expected_tag_reg,
                ));

                // 4. If tags match, jump to a new block to extract values.
                self.push_instr(Instr::Branch {
                    cond: tags_match_reg,
                    true_target: then_block_id,
                    false_target: else_block_id,
                });

                self.set_current_block(then_block_id);

                // 5. Extract values and bind them.
                for (i, field_pattern_id) in fields.iter().enumerate() {
                    if let Expr::Pattern(Pattern::Bind(Name::Resolved(symbol_id, _))) =
                        self.source_file.get(field_pattern_id).unwrap().clone()
                    {
                        let value_reg = self.allocate_register();

                        // We need to figure out the type of the value. This feels clumsy.
                        let ty = match variant_def.values[i].clone() {
                            Ty::TypeVar(var) => {
                                let Some(generic_pos) = type_def
                                    .type_parameters
                                    .iter()
                                    .filter_map(|t| {
                                        if let Ty::TypeVar(var_id) = t {
                                            Some(var_id)
                                        } else {
                                            None
                                        }
                                    })
                                    .position(|t| t == &var)
                                // t == var.0)
                                else {
                                    panic!("unable to determine enum generic: {var:?}")
                                };

                                enum_generics[generic_pos].clone()
                            }
                            other => other,
                        };

                        self.push_instr(Instr::GetEnumValue(
                            value_reg,
                            ty.to_ir(self),
                            *scrutinee_reg,
                            tag,
                            i as u16,
                        ));
                        self.current_func_mut()
                            .register_symbol(symbol_id, SymbolValue::Register(value_reg));
                    }
                    // Handle nested patterns recursively here.
                }
            }
            Pattern::LiteralInt(val) => {
                let literal_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(literal_reg, val.parse().unwrap()));
                let is_eq_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    is_eq_reg,
                    IRType::Int,
                    *scrutinee_reg,
                    literal_reg,
                ));

                self.push_instr(Instr::Branch {
                    cond: is_eq_reg,
                    true_target: then_block_id,
                    false_target: else_block_id,
                });
            }
            Pattern::LiteralFloat(_) => todo!(),
            Pattern::LiteralTrue => todo!(),
            Pattern::LiteralFalse => todo!(),
            Pattern::Bind(_name) => todo!(),
            Pattern::Wildcard => todo!(),
        }
    }

    fn _lower_pattern(&mut self, pattern_id: &ExprID) -> Register {
        let pattern_typed_expr = self.source_file.typed_expr(pattern_id).unwrap();
        let Expr::Pattern(pattern) = pattern_typed_expr.expr else {
            panic!("Didn't get pattern for match arm: {pattern_typed_expr:?}")
        };

        match pattern {
            Pattern::Bind(_) => todo!(),
            Pattern::LiteralInt(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(reg, str::parse(&val).unwrap()));
                reg
            }
            Pattern::LiteralFloat(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantFloat(reg, str::parse(&val).unwrap()));
                reg
            }
            Pattern::LiteralTrue => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, true));
                reg
            }
            Pattern::LiteralFalse => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, false));
                reg
            }
            Pattern::Wildcard => todo!(),
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Ty::Enum(enum_id, _) = pattern_typed_expr.ty else {
                    panic!("didn't get pattern type: {:?}", pattern_typed_expr.ty)
                };
                let Some(TypeDef::Enum(type_def)) = self.source_file.type_def(&enum_id).cloned()
                else {
                    panic!("didn't get type def for {enum_id:?}");
                };

                let tag = type_def
                    .variants
                    .iter()
                    .position(|v| v.name == variant_name)
                    .unwrap() as u16;

                let dest = self.allocate_register();
                let args = RegisterList(fields.iter().map(|f| self._lower_pattern(f)).collect());
                self.push_instr(Instr::TagVariant(
                    dest,
                    pattern_typed_expr.ty.to_ir(self),
                    tag,
                    args,
                ));

                dest
            } // _ => todo!("{:?}", pattern),
        }
    }

    fn lower_member(
        &mut self,
        receiver_id: &Option<ExprID>,
        expr_id: &ExprID,
        name: &str,
    ) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap();

        if let Ty::Enum(sym, _generics) = &typed_expr.ty {
            // Since we got called directly from lower_expr, this is variant that doesn't
            // have any attached values.
            return self.lower_enum_construction(*sym, name, &typed_expr.ty, &[]);
        }

        if let Some(receiver_id) = receiver_id {
            let Some(receiver) = self.lower_expr(receiver_id) else {
                self.push_err(
                    &format!("did not get receiver register: {:?}", typed_expr.expr),
                    *receiver_id,
                );
                return None;
            };

            let Some(receiver_typed) = self.source_file.typed_expr(receiver_id) else {
                unreachable!()
            };

            if let Some(index) = self.property_index(name, receiver_typed.ty.to_ir(self)) {
                let member_reg = self.allocate_register();

                self.push_instr(Instr::GetElementPointer {
                    dest: member_reg,
                    base: receiver,
                    ty: receiver_typed.ty.to_ir(self).clone(),
                    index: index,
                });

                Some(member_reg)
            } else {
                None
            }
        } else {
            todo!("wtf")
        }
    }

    fn lower_enum_construction(
        &mut self,
        enum_id: SymbolID,
        variant_name: &str,
        ty: &Ty,
        args: &[Register],
    ) -> Option<Register> {
        let Some(TypeDef::Enum(type_def)) = self.source_file.type_def(&enum_id).cloned() else {
            panic!("didn't get type def for {enum_id:?}");
        };

        let mut tag: Option<u16> = None;

        for (i, var) in type_def.variants.iter().enumerate() {
            if var.name != variant_name {
                continue;
            }

            tag = Some(i as u16);
        }

        let Some(tag) = tag else {
            panic!("did not find variant for tag")
        };

        let dest = self.allocate_register();
        self.push_instr(Instr::TagVariant(
            dest,
            ty.to_ir(self),
            tag,
            args.to_vec().into(),
        ));

        Some(dest)
    }

    fn lower_return(&mut self, expr_id: &ExprID, rhs: &Option<ExprID>) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap();

        if let Some(rhs) = rhs {
            let register = self.lower_expr(rhs)?;
            let ir_type = typed_expr.ty.to_ir(self);
            self.current_block_mut()
                .push_instr(Instr::Ret(ir_type, Some(register)));
            Some(register)
        } else {
            self.current_block_mut()
                .push_instr(Instr::Ret(IRType::Void, None));
            None
        }
    }

    fn lower_literal(&mut self, expr_id: &ExprID) -> Option<Register> {
        let register = self.allocate_register();
        match self.source_file.get(expr_id).unwrap().clone() {
            Expr::LiteralInt(val) => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantInt(register, str::parse(&val).unwrap()));
                Some(register)
            }
            Expr::LiteralFloat(val) => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantFloat(register, str::parse(&val).unwrap()));
                Some(register)
            }
            Expr::LiteralFalse => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantBool(register, false));
                Some(register)
            }
            Expr::LiteralTrue => {
                self.current_block_mut()
                    .push_instr(Instr::ConstantBool(register, true));
                Some(register)
            }
            _ => None,
        }
    }

    fn lower_binary_op(&mut self, expr_id: &ExprID) -> Option<Register> {
        let Some(typed_expr) = self.source_file.typed_expr(expr_id) else {
            return None;
        };

        let Expr::Binary(lhs, op, rhs) = typed_expr.expr else {
            panic!("Did not get binary expr");
        };

        let operand_ty = self.source_file.type_for(lhs);

        let operand_1 = self.lower_expr(&lhs).unwrap();
        let operand_2 = self.lower_expr(&rhs).unwrap();
        let return_reg = self.allocate_register();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Minus => Instr::Sub(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Star => Instr::Mul(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Slash => Instr::Div(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            BangEquals => Instr::Ne(return_reg, operand_ty.to_ir(self), operand_1, operand_2),
            EqualsEquals => Instr::Eq(return_reg, operand_ty.to_ir(self), operand_1, operand_2),

            Less => Instr::LessThan(return_reg, operand_ty.to_ir(self), operand_1, operand_2),
            LessEquals => {
                Instr::LessThanEq(return_reg, operand_ty.to_ir(self), operand_1, operand_2)
            }
            Greater => Instr::GreaterThan(return_reg, operand_ty.to_ir(self), operand_1, operand_2),
            GreaterEquals => {
                Instr::GreaterThanEq(return_reg, operand_ty.to_ir(self), operand_1, operand_2)
            }
            _ => panic!("Cannot lower binary operation: {op:?}"),
        };

        self.current_block_mut().push_instr(instr);

        Some(return_reg)
    }

    fn lower_assignment(&mut self, lhs_id: &ExprID, rhs_id: &ExprID) -> Option<Register> {
        let Some(rhs) = self.lower_expr(rhs_id) else {
            return None;
        };

        let lhs = self.source_file.typed_expr(lhs_id).unwrap().clone();

        match &lhs.expr {
            Expr::Let(Name::Resolved(symbol_id, _), _) => {
                self.current_func_mut()
                    .register_symbol(*symbol_id, rhs.into());
                Some(rhs)
            }
            Expr::Variable(Name::Resolved(symbol, _), _) => {
                let value = self
                    .lookup_register(symbol)
                    .expect("didn't get lhs for assignment")
                    .clone();

                match value {
                    SymbolValue::Register(_reg) => {
                        let new_reg = self.allocate_register();
                        self.push_instr(Instr::StoreLocal(
                            new_reg,
                            self.source_file.type_for(*rhs_id).to_ir(self),
                            rhs,
                        ));
                        self.current_func_mut()
                            .register_symbol(*symbol, new_reg.into());
                        None
                    }
                    SymbolValue::Capture(idx, ty) => {
                        let capture_ptr = self.allocate_register();
                        let env_ty = self.current_func().env_ty.clone();
                        self.push_instr(Instr::GetElementPointer {
                            dest: capture_ptr,
                            base: Register(0),
                            ty: env_ty,
                            index: idx,
                        });
                        self.push_instr(Instr::Store {
                            ty: ty.clone(),
                            val: rhs,
                            location: capture_ptr,
                        });

                        Some(rhs)
                    }
                    SymbolValue::Struct(struct_def) => {
                        unreachable!("Cannot assign to struct: {:?}", struct_def)
                    }
                }
            }
            Expr::Member(Some(receiver_id), name) => {
                if let Some(dest) = self.lower_member(&Some(*receiver_id), lhs_id, name) {
                    self.push_instr(Instr::Store {
                        ty: lhs.ty.to_ir(self),
                        val: rhs,
                        location: dest,
                    });
                    Some(rhs)
                } else {
                    None
                }
            }
            _ => todo!("don't know how to lower: {:?}", lhs),
        }
    }

    fn lower_block(&mut self, block_id: &ExprID) -> Option<Register> {
        let Expr::Block(exprs) = self.source_file.get(block_id).unwrap().clone() else {
            unreachable!()
        };

        if exprs.is_empty() {
            return None;
        }

        for (i, id) in exprs.iter().enumerate() {
            let reg = self.lower_expr(id);
            if i == exprs.len() - 1 {
                return reg;
            }
        }

        None
    }

    fn lower_variable(&mut self, expr_id: &ExprID, name: &Name) -> Option<Register> {
        let (Name::Resolved(symbol_id, _) | Name::_Self(symbol_id)) = name else {
            let expr = self.source_file.get(expr_id).unwrap();

            panic!("Unresolved variable: {name:?} {expr:?}")
        };

        let Some(value) = self.lookup_register(symbol_id) else {
            return None;
        };

        match value.clone() {
            SymbolValue::Register(reg) => Some(reg),
            SymbolValue::Capture(idx, ty) => {
                let env_ptr = self.allocate_register();
                self.push_instr(Instr::GetElementPointer {
                    dest: env_ptr,
                    base: Register(0),
                    ty: IRType::closure(),
                    index: idx,
                });

                let reg = self.allocate_register();
                self.push_instr(Instr::Load {
                    dest: reg,
                    ty: ty.clone(),
                    addr: env_ptr,
                });

                Some(reg)
            }
            _ => todo!(),
        }
    }

    fn lower_if(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id).unwrap();
        let Expr::If(cond, conseq, alt) = typed_expr.expr else {
            unreachable!()
        };

        let cond_reg = self
            .lower_expr(&cond)
            .expect("Condition for if expression did not produce a value");

        let then_id = self.new_basic_block();

        let mut else_reg: Option<Register> = None;
        let else_id: Option<BasicBlockID> = if alt.is_some() {
            Some(self.new_basic_block())
        } else {
            None
        };
        let merge_id = self.new_basic_block(); // All paths merge here

        self.current_block_mut().push_instr(Instr::Branch {
            cond: cond_reg,
            true_target: then_id,
            false_target: else_id.unwrap_or(merge_id),
        });

        self.set_current_block(then_id);
        let then_reg = self.lower_expr(&conseq).unwrap();
        self.current_block_mut().push_instr(Instr::Jump(merge_id));

        if let Some(alt) = alt {
            self.set_current_block(else_id.unwrap());
            else_reg = self.lower_expr(&alt);
            self.current_block_mut().push_instr(Instr::Jump(merge_id));
        }

        self.current_func_mut().set_current_block(merge_id);

        let phi_dest_reg = self.allocate_register();
        let ir_type = typed_expr.ty.to_ir(self);
        let predecessors = if let Some(else_reg) = else_reg
            && let Some(else_id) = else_id
        {
            vec![(then_reg, then_id), (else_reg, else_id)]
        } else {
            vec![(then_reg, then_id)]
        };

        self.current_block_mut().push_instr(Instr::Phi(
            phi_dest_reg,
            ir_type,
            PhiPredecessors(predecessors),
        ));

        Some(phi_dest_reg)
    }

    fn lower_call(
        &mut self,
        callee: ExprID,
        _type_args: Vec<ExprID>,
        args: Vec<ExprID>,
        ty: Ty,
    ) -> Option<Register> {
        // Handle builtins
        if let Some(Expr::Variable(Name::Resolved(symbol, _), _)) =
            self.source_file.get(&callee).cloned()
        {
            let callee_typed_expr = self.source_file.typed_expr(&callee).unwrap();
            if crate::builtins::is_builtin_func(&symbol) {
                return match super::builtins::lower_builtin(
                    &symbol,
                    &callee_typed_expr,
                    &args,
                    self,
                ) {
                    Ok(res) => return res,
                    Err(e) => {
                        self.push_err(e.message().as_str(), callee);
                        None
                    }
                };
            }
        }

        let mut arg_registers = vec![];
        for arg in &args {
            if let Some(arg_reg) = self.lower_expr(arg) {
                arg_registers.push(arg_reg);
            } else {
                self.push_err("Argument expression did not produce a value for call", *arg);
            }
        }

        let callee_typed_expr = self.source_file.typed_expr(&callee).unwrap();

        // Handle enum variant construction
        if let Ty::Enum(enum_id, _) = &ty {
            let Expr::Member(_, variant_name) = &callee_typed_expr.expr else {
                panic!("didn't get member expr for enum call")
            };

            return self.lower_enum_construction(*enum_id, variant_name, &ty, &arg_registers);
        }

        // Handle struct construction
        if let Ty::Init(struct_id, params) = &callee_typed_expr.ty {
            let Some(TypeDef::Struct(struct_def)) = self.source_file.type_def(struct_id).cloned()
            else {
                unreachable!()
            };

            let struct_ty = ty.to_ir(self);

            // 1. Allocate memory for the struct
            let struct_instance_reg = self.allocate_register();
            self.push_instr(Instr::Alloc {
                dest: struct_instance_reg,
                ty: struct_ty.clone(),
                count: None,
            });

            // 2. Get a reference to the initializer function
            let init_func_ref_reg = self.allocate_register();
            let init_func_ty = Ty::Func(
                params.clone(),
                Box::new(ty.clone()),
                vec![], // No generics on init
            );
            let init_func_name =
                Name::Resolved(*struct_id, format!("{}_init", struct_def.name_str))
                    .mangled(&init_func_ty);

            self.push_instr(Instr::Ref(
                init_func_ref_reg,
                init_func_ty.to_ir(self),
                RefKind::Func(init_func_name),
            ));

            // The first argument to the init function is the struct instance itself
            let mut call_args = vec![struct_instance_reg];
            call_args.extend(arg_registers);

            // 3. Call the initializer function
            let initialized_struct_reg = self.allocate_register();
            self.push_instr(Instr::Call {
                dest_reg: initialized_struct_reg,
                ty: struct_ty,
                callee: init_func_ref_reg.into(),
                args: RegisterList(call_args),
            });

            return Some(initialized_struct_reg);
        }

        let Some(callee_reg) = self.lower_expr(&callee) else {
            self.push_err(
                &format!("did not get callee: {:?}", self.source_file.get(&callee)),
                callee,
            );
            return None;
        };
        let func_ptr = self.allocate_register();
        let func_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: func_ptr,
            base: callee_reg,
            ty: IRType::closure(),
            index: 0,
        });
        self.push_instr(Instr::Load {
            dest: func_reg,
            ty: callee_typed_expr.ty.to_ir(self),
            addr: func_ptr,
        });

        let env_ptr = self.allocate_register();
        let env_reg = self.allocate_register();

        self.push_instr(Instr::GetElementPointer {
            dest: env_ptr,
            base: callee_reg,
            ty: IRType::closure(),
            index: 1,
        });
        self.push_instr(Instr::Load {
            dest: env_reg,
            ty: IRType::Pointer,
            addr: env_ptr,
        });

        arg_registers.insert(0, env_reg);

        let dest_reg = self.allocate_register();

        let ir_type = ty.to_ir(self);
        self.current_block_mut().push_instr(Instr::Call {
            ty: ir_type,
            dest_reg,
            callee: func_reg.into(),
            args: RegisterList(arg_registers),
        });

        // 5. Return the destination register
        Some(dest_reg)
    }

    /// Fills a pre-allocated closure with the given function reference and captures.
    ///
    /// This assumes `closure_ptr` has already been allocated with Instr::Alloc.
    fn fill_closure(
        &mut self,
        closure_ptr: Register,
        func_ref: RefKind,
        func_type: IRType,
        capture_types: Vec<IRType>,
        capture_registers: Vec<Register>,
    ) {
        // Create the environment struct
        let environment_register = self.allocate_register();
        let environment_type = IRType::Struct(SymbolID(0), capture_types);
        self.push_instr(Instr::MakeStruct {
            dest: environment_register,
            ty: environment_type.clone(),
            values: RegisterList(capture_registers),
        });

        // Allocate space for the environment
        let env_dest_ptr = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: env_dest_ptr,
            count: None,
            ty: environment_type.clone(),
        });

        // Store the environment
        self.push_instr(Instr::Store {
            ty: environment_type,
            val: environment_register,
            location: env_dest_ptr,
        });

        // Get reference to the function
        let func_ref_reg = self.allocate_register();
        self.push_instr(Instr::Ref(func_ref_reg, func_type, func_ref));

        // Get pointers to the closure fields
        let env_ptr = self.allocate_register();
        let fn_ptr = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: env_ptr,
            base: closure_ptr,
            ty: IRType::closure(),
            index: 1,
        });
        self.push_instr(Instr::GetElementPointer {
            dest: fn_ptr,
            base: closure_ptr,
            ty: IRType::closure(),
            index: 0,
        });

        // Store the environment and function pointers
        self.push_instr(Instr::Store {
            ty: IRType::Pointer,
            val: env_dest_ptr,
            location: env_ptr,
        });
        self.push_instr(Instr::Store {
            ty: IRType::Pointer,
            val: func_ref_reg,
            location: fn_ptr,
        });
    }

    pub(super) fn push_instr(&mut self, instr: Instr) {
        self.current_block_mut().push_instr(instr);
    }

    pub(super) fn allocate_register(&mut self) -> Register {
        self.current_func_mut().registers.allocate()
    }

    fn lookup_register(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.current_functions
            .last()
            .unwrap()
            .lookup_symbol(symbol_id)
    }

    fn current_func_mut(&mut self) -> &mut CurrentFunction {
        self.current_functions.last_mut().unwrap()
    }

    fn current_func(&mut self) -> &CurrentFunction {
        self.current_functions.last().unwrap()
    }

    fn current_block_mut(&mut self) -> &mut BasicBlock {
        self.current_func_mut().current_block_mut()
    }

    fn set_current_block(&mut self, id: BasicBlockID) {
        self.current_func_mut().set_current_block(id);
    }

    fn new_basic_block(&mut self) -> BasicBlockID {
        let id = self.current_func_mut().next_block_id();
        let block = BasicBlock {
            id,
            instructions: Vec::new(),
        };

        self.current_func_mut().add_block(block);
        id
    }

    fn resolve_name(&mut self, name: Option<Name>) -> Name {
        match name {
            Some(Name::Resolved(_, _)) => name.unwrap(),
            None => {
                let name_str = format!("fn{}", self.symbol_table.max_id() + 1);
                let symbol = self
                    .symbol_table
                    .add(&name_str, SymbolKind::CustomType, 12345, None);
                Name::Resolved(symbol, name_str)
            }
            _ => todo!(),
        }
    }

    pub fn push_err(&mut self, message: &str, expr_id: ExprID) -> IRError {
        self.source_file.diagnostics.insert(Diagnostic::lowering(
            expr_id,
            IRError::Unknown(message.to_string()),
        ));

        IRError::Unknown(message.to_string())
    }

    pub fn property_index(&self, name: &str, irtype: IRType) -> Option<usize> {
        let IRType::Struct(symbol_id, _) = irtype else {
            unreachable!()
        };

        let Some(TypeDef::Struct(struct_def)) = self.source_file.type_def(&symbol_id) else {
            unreachable!()
        };

        struct_def.properties.keys().position(|k| k == name)
    }
}

fn find_or_create_main(
    source_file: &mut SourceFile<Typed>,
    symbol_table: &mut SymbolTable,
) -> (ExprID, bool) {
    for root in source_file.typed_roots() {
        if let TypedExpr {
            expr:
                Expr::Func {
                    name: Some(Name::Resolved(_, name)),
                    ..
                },
            ..
        } = root
            && name == "main"
        {
            return (root.id, false);
        }
    }

    // We didn't find a main, we have to generate one
    let body = Expr::Block(source_file.root_ids());

    let body_id = source_file.add(
        body,
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
            identifiers: vec![],
        },
    );

    let func_expr = Expr::Func {
        name: Some(Name::Resolved(SymbolID::GENERATED_MAIN, "main".into())),
        generics: vec![],
        params: vec![],
        body: body_id,
        ret: None,
        captures: vec![],
    };

    source_file.set_typed_expr(
        SymbolID::GENERATED_MAIN.0,
        TypedExpr {
            id: SymbolID::GENERATED_MAIN.0,
            expr: func_expr.clone(),
            ty: Ty::Func(vec![], Box::new(Ty::Void), vec![]),
        },
    );

    source_file.add(
        func_expr.clone(),
        ExprMeta {
            start: Token::GENERATED,
            end: Token::GENERATED,
            identifiers: vec![],
        },
    );

    symbol_table.import(
        &SymbolID::GENERATED_MAIN,
        SymbolInfo {
            name: "@main".into(),
            kind: SymbolKind::Func,
            expr_id: SymbolID::GENERATED_MAIN.0,
            is_captured: false,
            definition: None,
        },
    );

    (SymbolID::GENERATED_MAIN.0, true)
}
