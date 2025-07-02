use std::{collections::HashMap, ops::AddAssign, str::FromStr};

use crate::{
    Lowered, SourceFile, SymbolID, SymbolInfo, SymbolKind, SymbolTable, Typed,
    analysis::{
        cfg::ControlFlowGraph, function_analysis::definite_initialization::DefiniteInitizationPass,
        function_analysis_pass::FunctionAnalysisPass,
    },
    compiling::{compilation_session::SharedCompilationSession, driver::DriverConfig},
    diagnostic::Diagnostic,
    environment::Environment,
    expr::{Expr, ExprMeta, Pattern},
    lowering::{
        instr::{Callee, Instr},
        ir_error::IRError,
        ir_function::IRFunction,
        ir_module::{IRConstantData, IRModule},
        ir_type::IRType,
        ir_value::IRValue,
        parsing::parser::ParserError,
        phi_predecessors::PhiPredecessors,
        register::Register,
    },
    name::Name,
    parser::ExprID,
    token::Token,
    token_kind::TokenKind,
    ty::Ty,
    type_checker::Scheme,
    type_constraint::TypeConstraint,
    type_defs::{TypeDef, struct_def::StructDef},
    type_var_id::{TypeVarID, TypeVarKind},
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
            Ty::Pointer => IRType::POINTER,
            Ty::Init(_sym, params) => IRType::Func(
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
            Ty::TypeVar(type_var_id) => IRType::TypeVar(format!("T{}", type_var_id.id)),
            Ty::Enum(symbol_id, generics) => IRType::Enum(
                *symbol_id,
                generics.iter().map(|i| i.to_ir(lowerer)).collect(),
            ),
            Ty::EnumVariant(enum_id, items) => {
                // let enum_def = lowerer.env.lookup_enum(enum_id).unwrap();
                IRType::Enum(*enum_id, items.iter().map(|t| t.to_ir(lowerer)).collect())
            }
            Ty::Closure { func, .. } => func.to_ir(lowerer),
            Ty::Tuple(items) => IRType::Struct(
                SymbolID::TUPLE,
                items.iter().map(|i| i.to_ir(lowerer)).collect(),
                vec![],
            ),
            Ty::Array(el) => IRType::TypedBuffer {
                element: el.to_ir(lowerer).into(),
            },
            Ty::Struct(symbol_id, generics) => {
                let Some(TypeDef::Struct(struct_def)) = lowerer.env.lookup_type(symbol_id) else {
                    log::error!("Unable to determine definition of struct: {symbol_id:?}");
                    return IRType::Void;
                };

                IRType::Struct(
                    *symbol_id,
                    struct_def
                        .properties
                        .iter()
                        .map(|p| p.ty.to_ir(lowerer))
                        .collect(),
                    generics.iter().map(|g| g.to_ir(lowerer)).collect(),
                )
            }
            Ty::Protocol(_, _) => IRType::Void,
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
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "entry" {
            Ok(BasicBlockID(0))
        } else {
            Ok(BasicBlockID(str::parse(&s[1..]).unwrap_or(u32::MAX)))
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
pub struct CurrentBasicBlock {
    pub id: BasicBlockID,
    pub instructions: Vec<InstructionWithExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub id: BasicBlockID,
    pub instructions: Vec<Instr>,
}

impl BasicBlock {
    fn _push_instr(&mut self, instr: Instr) {
        self.instructions.push(instr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedRegister {
    pub ty: IRType,
    pub register: Register,
}

impl TypedRegister {
    pub fn new(ty: IRType, register: Register) -> Self {
        Self { ty, register }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RegisterList(pub Vec<TypedRegister>);

impl RegisterList {
    pub const EMPTY: RegisterList = RegisterList(vec![]);
}

impl std::fmt::Display for RegisterList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, reg) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{} {}", reg.ty, reg.register)?;
        }
        Ok(())
    }
}
impl FromStr for TypedRegister {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let mut parts = s.split_whitespace();

        let Some(ty_str) = parts.next() else {
            return Err(IRError::ParseError);
        };

        let Some(reg_str) = parts.next() else {
            return Err(IRError::ParseError);
        };

        Ok(TypedRegister {
            ty: IRType::from_str(ty_str).map_err(|_| IRError::ParseError)?,
            register: str::parse(reg_str).map_err(|_| IRError::ParseError)?,
        })
    }
}

// Replace the old implementation with this one.
impl FromStr for RegisterList {
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // The input 's' is the content *between* the parentheses, e.g., "%1, %2" or "".
        let s = s.trim();
        if s.is_empty() {
            // Correctly handle the case of zero arguments.
            return Ok(RegisterList(vec![]));
        }

        // For non-empty arguments, split by comma and parse each part.
        s.split(',')
            .map(|part| part.trim().parse::<TypedRegister>())
            .collect::<Result<Vec<TypedRegister>, _>>()
            .map(RegisterList)
            .map_err(|_e| IRError::ParseError)
    }
}

#[derive(Debug, Clone)]
pub enum SymbolValue {
    Register(Register),
    Capture(usize, IRType),
    Struct(StructDef),
    FuncRef(String),
}

impl From<Register> for SymbolValue {
    fn from(value: Register) -> Self {
        Self::Register(value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InstructionWithExpr {
    pub instr: Instr,
    pub expr_id: Option<ExprID>,
}

#[derive(Debug)]
struct CurrentFunction {
    current_block_idx: usize,
    next_block_id: BasicBlockID,
    blocks: Vec<CurrentBasicBlock>,
    env_ty: Option<IRType>,
    pub registers: RegisterAllocator,
    pub symbol_registers: HashMap<SymbolID, SymbolValue>,
}

impl CurrentFunction {
    #[track_caller]
    fn new(env_ty: Option<IRType>) -> Self {
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

    fn add_block(&mut self, block: CurrentBasicBlock) {
        self.blocks.push(block);
    }

    fn current_block_mut(&mut self) -> &mut CurrentBasicBlock {
        &mut self.blocks[self.current_block_idx]
    }

    fn set_current_block(&mut self, id: BasicBlockID) -> Result<(), IRError> {
        let Some(index) = self.blocks.iter().position(|blk| blk.id == id) else {
            return Err(IRError::Unknown(format!(
                "Current function has no block with id {id}"
            )));
        };

        self.current_block_idx = index;

        Ok(())
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

    fn _lookup_symbol(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.symbol_registers.get(symbol_id)
    }

    fn export(
        self,
        ty: IRType,
        name: String,
        env_ty: Option<IRType>,
        env_reg: Option<Register>,
    ) -> IRFunction {
        let mut blocks = vec![];
        let mut debug_info = DebugInfo::default();

        for block in self.blocks.into_iter() {
            let mut instr_expr_ids = HashMap::default();
            let mut instructions = vec![];
            for (i, instruction) in block.instructions.into_iter().enumerate() {
                instructions.push(instruction.instr);
                instr_expr_ids.insert(i, instruction.expr_id);
            }

            debug_info.insert(block.id, instr_expr_ids);

            blocks.push(BasicBlock {
                id: block.id,
                instructions,
            });
        }

        log::warn!("EXPORING FUNC: {} {:?}", name, self.registers);

        IRFunction {
            ty,
            name,
            blocks,
            env_ty,
            env_reg,
            size: self.registers.next_id,
            debug_info,
        }
    }
}

pub type DebugInfo = HashMap<BasicBlockID, HashMap<usize, Option<ExprID>>>;

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
    loop_exits: Vec<BasicBlockID>,
    globals: HashMap<SymbolID, SymbolValue>,
    current_expr_ids: Vec<ExprID>,
    pub env: &'a mut Environment,
    session: SharedCompilationSession,
    constants: Vec<IRConstantData>,
}

impl<'a> Lowerer<'a> {
    pub fn new(
        source_file: SourceFile<Typed>,
        symbol_table: &'a mut SymbolTable,
        env: &'a mut Environment,
        session: SharedCompilationSession,
    ) -> Self {
        Self {
            source_file,
            current_functions: vec![],
            lowered_functions: Default::default(),
            symbol_table,
            globals: HashMap::new(),
            loop_exits: vec![],
            current_expr_ids: vec![],
            env,
            session,
            constants: Default::default(),
        }
    }

    pub fn lower(
        mut self,
        module: &mut IRModule,
        driver_config: &DriverConfig,
    ) -> SourceFile<Lowered> {
        if driver_config.executable {
            let (expr_id, did_create) =
                find_or_create_main(&mut self.source_file, self.symbol_table, self.env);

            // If we created the main function, we need to set it up
            if did_create {
                // Make sure we have a current function
                self.current_functions.push(CurrentFunction::new(None));

                // Make sure it has a basic block
                let entry = self.new_basic_block();
                self.set_current_block(entry);
            }

            self.lower_function(&expr_id);

            // If we created the main function, we moved all the typed roots into its body
            // so we don't need to lower them again.
            if !did_create {
                let typed_roots: Vec<TypedExpr> = self
                    .source_file
                    .root_ids()
                    .iter()
                    .filter_map(|root| self.env.typed_exprs.get(root).cloned())
                    .collect();
                for root in typed_roots {
                    if let Expr::Func { .. } = &root.expr {
                        self.lower_function(&root.id);
                    }
                }
            }
        } else {
            self.current_functions.push(CurrentFunction::new(None));
            let id = self.new_basic_block();
            self.set_current_block(id);

            for root_id in self.source_file.root_ids() {
                self.lower_expr(&root_id);
            }
        }

        for function in self.lowered_functions {
            module.functions.push(function)
        }

        module.constants = self.constants;

        self.source_file.to_lowered()
    }

    pub fn lower_expr(&mut self, expr_id: &ExprID) -> Option<Register> {
        self.current_expr_ids.push(*expr_id);
        let typed_expr = self.source_file.typed_expr(expr_id, self.env).clone()?;

        let res = match typed_expr.expr {
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
            } => self.lower_call(
                callee,
                type_args,
                &typed_expr.ty.to_ir(self),
                args,
                typed_expr.ty,
            ),
            Expr::Func { .. } => self.lower_function(expr_id),
            Expr::Return(rhs) => self.lower_return(expr_id, &rhs),
            Expr::EnumDecl { .. } => None,
            Expr::Member(receiver, name) => self.lower_member(&receiver, expr_id, &name, false),
            Expr::Match(scrutinee, arms) => self.lower_match(&scrutinee, &arms, &typed_expr.ty),
            Expr::CallArg { value, .. } => self.lower_expr(&value),
            Expr::Struct {
                name: Name::Resolved(struct_id, _),
                body,
                ..
            } => self.lower_struct(expr_id, struct_id, &body),
            Expr::Init(symbol_id, func_id) => symbol_id
                .map(|symbol_id| self.lower_init(&symbol_id, &func_id))
                .unwrap_or_else(|| {
                    self.push_err(format!("No symbol for ID {func_id}").as_str(), func_id);

                    None
                }),
            Expr::TypeRepr { .. } => None, // these are just for the type system
            Expr::LiteralArray(items) => self.lower_array(expr_id, typed_expr.ty, items),
            Expr::Loop(cond, body) => self.lower_loop(&cond, &body),
            Expr::Break => {
                let Some(current_loop_exit) = self.loop_exits.last() else {
                    self.add_diagnostic(Diagnostic::lowering(
                        self.source_file.path.clone(),
                        *expr_id,
                        IRError::Unknown("trying to break while not in a loop".into()),
                    ));

                    return None;
                };

                self.push_instr(Instr::Jump(*current_loop_exit));
                None
            }
            Expr::ProtocolDecl {
                ref name,
                ref associated_types,
                ref body,
                ref conformances,
            } => self.lower_protocol(&typed_expr, name, associated_types, body, conformances),
            Expr::Tuple(items) => self.lower_tuple(expr_id, items),
            Expr::LiteralString(string) => self.lower_string(expr_id, string),
            expr => {
                self.add_diagnostic(Diagnostic::lowering(
                    self.source_file.path.clone(),
                    *expr_id,
                    IRError::Unknown(format!("Cannot lower {expr:?}")),
                ));

                None
            }
        };

        self.current_expr_ids.pop();

        res
    }

    fn lower_protocol(
        &mut self,
        _typed_expr: &TypedExpr,
        name: &Name,
        _associated_types: &[ExprID],
        body: &ExprID,
        _conformances: &[ExprID],
    ) -> Option<Register> {
        let Some(Expr::Block(ids)) = self.source_file.get(body).cloned() else {
            unreachable!()
        };

        let Some(protocol_def) = self.env.lookup_protocol(&name.try_symbol_id()).cloned() else {
            self.push_err("No Protocol found", *body);
            return None;
        };

        for id in ids {
            if let Some(TypedExpr {
                expr: Expr::Func { .. },
                ..
            }) = self.source_file.typed_expr(&id, self.env).clone()
            {
                self.lower_method(&name.try_symbol_id(), &id, &name.name_str())?;
            }

            if let Some(TypedExpr {
                expr: Expr::FuncSignature { name, .. },
                ty,
                ..
            }) = self.source_file.typed_expr(&id, self.env).clone()
            {
                self.lower_method_stub(
                    &ty,
                    &Name::Resolved(protocol_def.symbol_id, protocol_def.name_str.clone()),
                    &name,
                )?;
            }
        }

        None
    }

    fn lower_tuple(&mut self, expr_id: &ExprID, items: Vec<ExprID>) -> Option<Register> {
        let Some(typed_expr) = self.source_file.typed_expr(expr_id, self.env) else {
            self.push_err("Did not find typed expr", *expr_id);
            return None;
        };

        let mut member_registers = vec![];
        let mut member_types = vec![];

        for item_id in items {
            let Some(item_expr) = self.source_file.typed_expr(&item_id, self.env) else {
                self.push_err("Did not find typed expr", *expr_id);
                continue;
            };
            if let Some(reg) = self.lower_expr(&item_id) {
                let ir_type = item_expr.ty.to_ir(self);
                member_registers.push(TypedRegister::new(ir_type.clone(), reg));
                member_types.push(ir_type);
            } else {
                self.push_err("Could not lower tuple element", item_id);
                return None;
            }
        }

        // we represent tuples as structs for now
        let dest = self.allocate_register();
        self.push_instr(Instr::MakeStruct {
            dest,
            ty: typed_expr.ty.to_ir(self),
            values: RegisterList(member_registers),
        });

        Some(dest)
    }

    fn lower_loop(&mut self, cond: &Option<ExprID>, body: &ExprID) -> Option<Register> {
        let current_block = self.current_block_mut()?.id;
        let loop_entry = self.new_basic_block();
        let loop_exit = self.new_basic_block();
        let loop_cond = if let Some(cond) = cond {
            let loop_cond = self.new_basic_block();
            self.set_current_block(loop_cond);
            let Some(cond_reg) = self.lower_expr(cond) else {
                self.add_diagnostic(Diagnostic::lowering(
                    self.source_file.path.clone(),
                    *cond,
                    IRError::Unknown(format!("Cannot lower loop condition {cond:?}")),
                ));
                return None;
            };

            self.push_instr(Instr::Branch {
                cond: cond_reg,
                true_target: loop_entry,
                false_target: loop_exit,
            });

            Some(loop_cond)
        } else {
            None
        };

        self.loop_exits.push(loop_exit);

        let jump_target = loop_cond.unwrap_or(loop_entry);
        self.set_current_block(current_block);
        self.push_instr(Instr::Jump(jump_target));
        self.set_current_block(loop_entry);
        self.lower_expr(body);
        self.push_instr(Instr::Jump(jump_target));

        self.loop_exits.pop();
        self.set_current_block(loop_exit);

        None
    }

    fn lower_string(&mut self, _expr_id: &ExprID, string: String) -> Option<Register> {
        // Allocate the storage
        let chars_bytes = string.as_bytes();
        self.push_constant(IRConstantData::RawBuffer(chars_bytes.to_vec()));

        let string_struct_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: string_struct_reg,
            ty: IRType::string(),
            count: None,
        });

        let length_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: length_reg,
            base: string_struct_reg,
            ty: IRType::string(),
            index: IRValue::ImmediateInt(0),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: IRValue::ImmediateInt(chars_bytes.len() as i64),
            location: length_reg,
        });

        let capacity_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: capacity_reg,
            base: string_struct_reg,
            ty: IRType::string(),
            index: IRValue::ImmediateInt(1),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: IRValue::ImmediateInt(chars_bytes.len() as i64),
            location: capacity_reg,
        });

        let storage_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: storage_reg,
            base: string_struct_reg,
            ty: IRType::string(),
            index: IRValue::ImmediateInt(2),
        });
        let static_ptr_reg = self.allocate_register();
        self.push_instr(Instr::Const {
            dest: static_ptr_reg,
            ty: IRType::RawBuffer,
            val: IRValue::ImmediateInt(0),
        });
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: static_ptr_reg.into(),
            location: storage_reg,
        });

        let dest = self.allocate_register();
        self.push_instr(Instr::Load {
            dest,
            ty: IRType::string(),
            addr: string_struct_reg,
        });

        Some(dest)
    }

    fn lower_array(&mut self, expr_id: &ExprID, ty: Ty, items: Vec<ExprID>) -> Option<Register> {
        let Ty::Struct(SymbolID::ARRAY, els) = ty else {
            self.push_err("Invalid array type", *expr_id);
            return None;
        };

        let ty = els.last()?.to_ir(self);

        // Allocate the array
        let array_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: array_reg,
            ty: IRType::array(ty.clone()),
            count: None,
        });

        // Set the array's count
        let count_reg = self.allocate_register();
        self.push_instr(Instr::ConstantInt(count_reg, items.len() as i64));
        let count_ptr_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: count_ptr_reg,
            base: array_reg,
            ty: IRType::array(ty.clone()),
            index: IRValue::ImmediateInt(0),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: count_reg.into(),
            location: count_ptr_reg,
        });

        // Set the array's capacity
        let capacity_reg = self.allocate_register();
        self.push_instr(Instr::ConstantInt(capacity_reg, items.len() as i64));
        let capacity_ptr_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: capacity_ptr_reg,
            base: array_reg,
            ty: IRType::array(ty.clone()),
            index: IRValue::ImmediateInt(1),
        });
        self.push_instr(Instr::Store {
            ty: IRType::Int,
            val: capacity_reg.into(),
            location: capacity_ptr_reg,
        });

        // Alloc the array's storage
        let storage_ptr_reg = self.allocate_register();
        self.push_instr(Instr::GetElementPointer {
            dest: storage_ptr_reg,
            base: array_reg,
            ty: IRType::array(ty.clone()),
            index: IRValue::ImmediateInt(2),
        });
        let storage_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: storage_reg,
            ty: IRType::Int,
            count: Some(IRValue::Register(count_reg)),
        });
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: storage_reg.into(),
            location: storage_ptr_reg,
        });

        if items.is_empty() {
            let loaded = self.allocate_register();
            self.push_instr(Instr::Load {
                dest: loaded,
                ty: IRType::array(ty.clone()),
                addr: array_reg,
            });
            return Some(loaded);
        }

        for (i, item) in items.iter().enumerate() {
            let lowered_item = self.lower_expr(item)?;
            let ty = self
                .source_file
                .type_for(*item, self.env)
                .map(|ty| ty.to_ir(self))?;

            let item_reg = self.allocate_register();
            self.push_instr(Instr::GetElementPointer {
                dest: item_reg,
                base: storage_reg,
                ty: IRType::TypedBuffer {
                    element: ty.clone().into(),
                },
                index: IRValue::ImmediateInt(i as i64),
            });
            self.push_instr(Instr::Store {
                ty,
                val: lowered_item.into(),
                location: item_reg,
            });
        }

        // let loaded = self.allocate_register();
        // self.push_instr(Instr::Load {
        //     dest: loaded,
        //     ty: IRType::array(),
        //     addr: array_reg,
        // });

        Some(array_reg)
    }

    fn lower_struct(
        &mut self,
        expr_id: &ExprID,
        struct_id: SymbolID,
        body_id: &ExprID,
    ) -> Option<Register> {
        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(&struct_id).cloned() else {
            self.add_diagnostic(Diagnostic::lowering(
                self.source_file.path.clone(),
                *expr_id,
                IRError::Unknown(format!(
                    "Could not resolve struct for symbol: {struct_id:?}"
                )),
            ));
            return None;
        };

        for initializer in &struct_def.initializers {
            self.lower_expr(&initializer.expr_id);

            // TODO this is awkward
            if let Some(init_func) = self.lowered_functions.last() {
                let cfg = ControlFlowGraph::new(init_func);
                let pass = DefiniteInitizationPass::new(struct_def.clone());
                match pass.run(init_func, &cfg) {
                    Ok(_) => (),
                    Err(e) => {
                        self.add_diagnostic(Diagnostic::lowering(
                            self.source_file.path.clone(),
                            initializer.expr_id,
                            e,
                        ));
                    }
                }
            }
        }

        let Some(Expr::Block(member_ids)) = self.source_file.get(body_id) else {
            self.add_diagnostic(Diagnostic::lowering(
                self.source_file.path.clone(),
                *body_id,
                IRError::Unknown("Did not get struct body".into()),
            ));
            return None;
        };

        for member_id in member_ids.clone() {
            let Some(typed_member) = self.source_file.typed_expr(&member_id, self.env).clone()
            else {
                // self.source_file.diagnostics.insert(Diagnostic::lowering(
                //     member_id,
                //     IRError::Unknown(format!(
                //         "Did not get struct member `{:?}`",
                //         self.source_file.get(&member_id),
                //     )),
                // ));
                continue;
            };

            match typed_member.expr {
                Expr::Func {
                    name: Some(name), ..
                } => {
                    self.lower_method(&struct_id, &member_id, &name.name_str());
                }
                Expr::Init(..) | Expr::Property { .. } => {
                    // These are handled by the StructDef or the first loop; ignore them here.
                    continue;
                }
                _ => {
                    log::warn!("unhandled struct member: {:?}", typed_member.expr);
                    continue;
                }
            }
        }

        self.register_global(&struct_id, SymbolValue::Struct(struct_def));

        None
    }

    fn setup_self_context(
        &mut self,
        symbol_id: &SymbolID,
        func_id: &ExprID,
    ) -> Option<(IRType, StructDef, TypedExpr, Register, Option<IRValue>)> {
        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(symbol_id).cloned() else {
            unreachable!()
        };

        let Some(typed_func) = self.source_file.typed_expr(func_id, self.env) else {
            unreachable!()
        };

        let Expr::Func { params, body, .. } = &typed_func.expr else {
            unreachable!()
        };

        let struct_ty = IRType::Struct(
            *symbol_id,
            struct_def
                .properties
                .iter()
                .map(|p| p.ty.to_ir(self))
                .collect(),
            struct_def
                .type_parameters
                .iter()
                .map(|t| Ty::TypeVar(t.type_var.clone()).to_ir(self))
                .collect(),
        );

        self.current_functions
            .push(CurrentFunction::new(Some(struct_ty.clone())));
        let block_id = self.new_basic_block();
        self.set_current_block(block_id);

        // Define our env
        let env = self.allocate_register();
        self.current_func_mut()?
            .register_symbol(*symbol_id, SymbolValue::Register(env));

        for param in params {
            let Some(Expr::Parameter(Name::Resolved(symbol, _), _)) =
                self.source_file.get(param).cloned()
            else {
                self.push_err("Did not get parameter", *param);
                return None;
            };

            let register = self.allocate_register();
            self.current_func_mut()?
                .register_symbol(symbol, SymbolValue::Register(register));
        }

        let ret = self.lower_block(body);

        Some((
            struct_ty,
            struct_def,
            typed_func,
            env,
            ret.map(IRValue::Register),
        ))
    }

    fn lower_init(&mut self, symbol_id: &SymbolID, func_id: &ExprID) -> Option<Register> {
        let (struct_ty, struct_def, typed_func, env, _) =
            self.setup_self_context(symbol_id, func_id)?;

        let loaded_reg = self.allocate_register();
        self.push_instr(Instr::Load {
            dest: loaded_reg,
            ty: struct_ty.clone(),
            addr: env,
        });

        self.push_instr(Instr::Ret(struct_ty.clone(), Some(loaded_reg.into())));

        let Ty::Func(params, _ret, generics) = typed_func.ty else {
            return None;
        };

        // Override func type for init to always return the struct
        let init_func_ty = Ty::Func(
            params,
            // Ty::Struct(
            //     *symbol_id,
            //     struct_def.properties.iter().map(|p| p.ty.clone()).collect(),
            // )
            // .into(),
            Ty::Pointer.into(),
            generics,
        );

        let name_str = struct_def.name_str.clone();
        let current_function = self.current_functions.pop()?;

        let func = current_function.export(
            init_func_ty.to_ir(self),
            Name::Resolved(*symbol_id, format!("{name_str}_init")).mangled(&init_func_ty),
            Some(struct_ty),
            Some(env),
        );

        self.lowered_functions.push(func.clone());

        Some(env)
    }

    fn lower_method(
        &mut self,
        symbol_id: &SymbolID,
        func_id: &ExprID,
        name: &str,
    ) -> Option<Register> {
        let (struct_ty, struct_def, typed_func, env, ret) =
            self.setup_self_context(symbol_id, func_id)?;

        let (Ty::Func(_, ret_ty, _)
        | Ty::Closure {
            func: box Ty::Func(_, ret_ty, _),
            ..
        }) = &typed_func.ty
        else {
            self.push_err(
                &format!("Could not get return type for method: {typed_func:?}"),
                *func_id,
            );
            return None;
        };

        self.push_instr(Instr::Ret(ret_ty.to_ir(self), ret));

        let current_function = self.current_functions.pop()?;
        let func = current_function.export(
            typed_func.ty.to_ir(self),
            Name::Resolved(*symbol_id, format!("{}_{name}", struct_def.name_str))
                .mangled(&typed_func.ty),
            Some(struct_ty),
            Some(env),
        );

        self.lowered_functions.push(func.clone());

        None
    }

    fn lower_method_stub(
        &mut self,
        ty: &Ty,
        protocol_name: &Name,
        name: &Name,
    ) -> Option<Register> {
        let Ty::Func(mut params, ret, generics) = ty.clone() else {
            unreachable!()
        };

        let type_var = Ty::TypeVar(TypeVarID::new(
            0,
            TypeVarKind::SelfVar(name.try_symbol_id()),
            vec![],
        ));

        // Insert the self env param
        params.insert(0, type_var.clone());

        let stub_function = IRFunction {
            ty: Ty::Func(params, ret, generics).to_ir(self),
            name: format!(
                "@_{}_{}_{}",
                protocol_name.try_symbol_id().0,
                protocol_name.name_str(),
                name.name_str()
            ),
            blocks: vec![],
            env_ty: Some(type_var.to_ir(self)),
            env_reg: None,
            size: 0,
            debug_info: Default::default(),
        };

        self.lowered_functions.push(stub_function);

        None
    }

    fn lower_function(&mut self, expr_id: &ExprID) -> Option<Register> {
        let Some(typed_expr) = self.env.typed_exprs.get(expr_id).cloned() else {
            self.push_err("Did not get typed expr", *expr_id);
            return None;
        };

        let Expr::Func {
            ref name,
            ref params,
            ref body,
            ref captures,
            ref generics,
            ..
        } = typed_expr.expr
        else {
            self.push_err("Did not get typed expr", *expr_id);
            return None;
        };

        let name = self.resolve_name(name.clone());
        let generics: Vec<IRType> = generics
            .iter()
            .filter_map(|f| {
                self.source_file
                    .type_for(*f, self.env)
                    .map(|t| t.to_ir(self))
            })
            .collect();

        // If the only capture is the func itself, we don't need to allocate a closure

        let ret = if captures.is_empty() {
            let fn_ptr = self.allocate_register();
            self.push_instr(Instr::Ref(
                fn_ptr,
                typed_expr.ty.to_ir(self),
                RefKind::Func(name.mangled(&typed_expr.ty)),
            ));

            self.current_functions.push(CurrentFunction::new(None));
            let id = self.new_basic_block();
            self.set_current_block(id);

            Some(fn_ptr)
        } else {
            let closure_ptr = self.allocate_register();
            self.push_instr(Instr::Alloc {
                dest: closure_ptr,
                count: None,
                ty: IRType::closure(),
            });

            if let Name::Resolved(symbol, _) = name {
                self.current_func_mut()?
                    .register_symbol(symbol, SymbolValue::Register(closure_ptr));
            }

            let (capture_types, capture_registers) = if let Ty::Closure {
                captures: capture_types,
                ..
            } = &typed_expr.ty
            {
                let Name::Resolved(self_symbol, _) = &name else {
                    self.push_err(&format!("no symbol: {name:?}"), *expr_id);
                    return None;
                };

                // Define an environment object for our captures. If there aren't any captures we don't care,
                // we're going to do it anyway. Maybe we can optimize it out later? I don't know if we'll have time.
                let mut capture_registers = vec![];
                let mut captured_ir_types = vec![];
                for (i, capture) in captures.iter().enumerate() {
                    let Some(SymbolValue::Register(register)) = self.lookup_register(capture)
                    else {
                        self.push_err("don't know how to handle captured captures yet", *expr_id);
                        return None;
                    };
                    capture_registers.push(*register);

                    if capture == self_symbol {
                        captured_ir_types.push(IRType::POINTER);
                    } else {
                        let capture_ty = self
                            .env
                            .lookup_symbol(&capture_types[i])
                            .cloned()
                            .unwrap_or_else(|_| {
                                let sym = capture_types[i];
                                let Some(info) = self.symbol_table.get(&sym) else {
                                    return Scheme {
                                        ty: Ty::Void,
                                        unbound_vars: vec![],
                                    };
                                };
                                let Some(typed_expr) =
                                    self.source_file.typed_expr(&info.expr_id, self.env)
                                else {
                                    return Scheme {
                                        ty: Ty::Void,
                                        unbound_vars: vec![],
                                    };
                                };

                                Scheme {
                                    ty: typed_expr.ty,
                                    unbound_vars: vec![],
                                }
                            })
                            .ty;
                        captured_ir_types.push(capture_ty.to_ir(self));
                    }
                }

                (captured_ir_types, capture_registers)
            } else {
                (vec![], vec![])
            };

            let environment_type = IRType::Struct(SymbolID::ENV, capture_types.clone(), vec![]);

            self.fill_closure(
                closure_ptr,
                RefKind::Func(name.mangled(&typed_expr.ty)),
                typed_expr.ty.to_ir(self),
                capture_types.clone(),
                capture_registers,
                generics,
            );

            self.current_functions
                .push(CurrentFunction::new(Some(environment_type)));
            let id = self.new_basic_block();
            self.set_current_block(id);

            // Now that we're in the block, register the captures
            for (i, capture) in captures.iter().enumerate() {
                self.current_func_mut()?
                    .register_symbol(*capture, SymbolValue::Capture(i, capture_types[i].clone()));
            }

            Some(closure_ptr)
        };

        log::trace!("lowering {name:?}");

        let Some(Expr::Block(body_exprs)) = self.source_file.get(body).cloned() else {
            self.push_err("Did not get body", *body);
            return None;
        };

        let env_reg = if captures.is_empty() {
            None
        } else {
            Some(self.allocate_register()) // Set aside our env register
        };

        for param in params {
            let Some(Expr::Parameter(Name::Resolved(symbol, _), _)) =
                self.source_file.get(param).cloned()
            else {
                self.push_err("didn't get parameter", *param);
                return None;
            };

            let register = self.current_func_mut()?.registers.allocate();
            self.current_func_mut()?
                .register_symbol(symbol, SymbolValue::Register(register));
        }

        for (i, id) in body_exprs.iter().enumerate() {
            let ret = if let Some(reg) = self.lower_expr(id)
                && let Some(ty) = self
                    .source_file
                    .typed_expr(id, self.env)
                    .map(|t| t.ty.to_ir(self))
            {
                (ty, Some(reg.into()))
            } else {
                (IRType::Void, None)
            };

            if i == body_exprs.len() - 1 {
                let ty = if matches!(ret.0, IRType::Func(_, _)) {
                    // we don't pass around functions, we pass around pointers (closures)
                    IRType::POINTER
                } else {
                    ret.0
                };

                self.push_instr(Instr::Ret(ty, ret.1));
            }
        }

        let current_function = self.current_functions.pop()?;
        let env_ty = current_function.env_ty.clone();
        let func = current_function.export(
            typed_expr.ty.to_ir(self),
            name.mangled(&typed_expr.ty),
            env_ty,
            env_reg,
        );

        self.lowered_functions.push(func.clone());

        ret
    }

    fn lower_match(&mut self, scrutinee: &ExprID, arms: &[ExprID], ty: &Ty) -> Option<Register> {
        let scrutinee_reg = self.lower_expr(scrutinee)?;
        let merge_block_id = self.new_basic_block();

        // Pre-allocate all the blocks where we will check the condition for each arm.
        let arm_cond_blocks: Vec<_> = (0..arms.len()).map(|_| self.new_basic_block()).collect();

        // Jump to the first condition
        self.push_instr(Instr::Jump(arm_cond_blocks[0]));

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
        let Some(typed_arm) = self.source_file.typed_expr(expr_id, self.env) else {
            self.push_err("Did not get typed arm", *expr_id);
            return (Register(0), BasicBlockID(u32::MAX));
        };

        let Expr::MatchArm(pattern_id, body_id) = typed_arm.expr else {
            self.push_err("Did not get match arm", *expr_id);
            return (Register(0), BasicBlockID(u32::MAX));
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
        let Some(body_ret_reg) = self.lower_expr(&body_id) else {
            self.push_err("Did not get body return", body_id);
            return (Register(0), BasicBlockID(u32::MAX));
        };

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
    ) -> Option<()> {
        let pattern_typed_expr = self.source_file.typed_expr(pattern_id, self.env)?;
        let Expr::Pattern(pattern) = pattern_typed_expr.expr else {
            return None;
        };

        self.set_current_block(cond_block_id);
        match pattern {
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                let (enum_id, enum_generics) = {
                    let mut id = None;
                    let mut generics = None;

                    if let Ty::Enum(enum_id, params) = &pattern_typed_expr.ty {
                        id = Some(enum_id);
                        generics = Some(params);
                    }

                    if let Ty::EnumVariant(enum_id, params) = &pattern_typed_expr.ty {
                        id = Some(enum_id);
                        generics = Some(params);
                    }

                    (id, generics)
                };

                let (Some(enum_id), Some(enum_generics)) = (enum_id, enum_generics) else {
                    self.push_err("Could not determine enum generics", cond_block_id.0 as i32);
                    return None;
                };

                let Some(TypeDef::Enum(type_def)) = self.env.lookup_type(enum_id).cloned() else {
                    self.push_err("Could not determine enum", cond_block_id.0 as i32);
                    return None;
                };

                /* ... find variant by name in type_def ... */
                let Some((tag, variant_def)) = type_def.tag_with_variant_for(&variant_name) else {
                    self.push_err("message", *pattern_id);
                    return None;
                };

                // 2. Get the tag of the scrutinee.
                let tag_reg = self.allocate_register();
                self.push_instr(Instr::GetEnumTag(tag_reg, *scrutinee_reg));

                let expected_tag_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(expected_tag_reg, tag as i64));
                let tags_match_reg = self.allocate_register();
                self.push_instr(Instr::Eq(
                    tags_match_reg,
                    IRType::Int,
                    tag_reg,
                    expected_tag_reg,
                ));

                self.push_instr(Instr::Branch {
                    cond: tags_match_reg,
                    true_target: then_block_id,
                    false_target: else_block_id,
                });

                self.set_current_block(then_block_id);

                for (i, field_pattern_id) in fields.iter().enumerate() {
                    if let Some(Expr::Pattern(Pattern::Bind(Name::Resolved(symbol_id, _)))) =
                        self.source_file.get(field_pattern_id).cloned()
                    {
                        let value_reg = self.allocate_register();

                        // We need to figure out the type of the value. This feels clumsy.
                        let Ty::EnumVariant(_, values) = variant_def.ty.clone() else {
                            unreachable!();
                        };
                        let ty = match values[i].clone() {
                            Ty::TypeVar(var) => {
                                let Some(generic_pos) = type_def
                                    .type_parameters
                                    .iter()
                                    .position(|t| t.type_var == var)
                                // t == var.0)
                                else {
                                    self.push_err(
                                        format!("unable to determine enum generic: {var:?}")
                                            .as_str(),
                                        *field_pattern_id,
                                    );

                                    return None;
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
                        self.current_func_mut()?
                            .register_symbol(symbol_id, SymbolValue::Register(value_reg));
                    }
                    // Handle nested patterns recursively here.
                }
            }
            Pattern::LiteralInt(val) => {
                let literal_reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(literal_reg, val.parse().unwrap_or(0)));
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
            Pattern::LiteralFloat(_) => (),
            Pattern::LiteralTrue => (),
            Pattern::LiteralFalse => (),
            Pattern::Bind(_name) => (),
            Pattern::Wildcard => (),
        }

        Some(())
    }

    fn _lower_pattern(&mut self, pattern_id: &ExprID) -> Option<Register> {
        let pattern_typed_expr = self.source_file.typed_expr(pattern_id, self.env)?;
        let Expr::Pattern(pattern) = pattern_typed_expr.expr else {
            self.push_err(
                "Didn't get pattern for match arm: {pattern_typed_expr:?}",
                *pattern_id,
            );
            return None;
        };

        match pattern {
            Pattern::Bind(_) => None,
            Pattern::LiteralInt(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantInt(reg, str::parse(&val).ok()?));
                Some(reg)
            }
            Pattern::LiteralFloat(val) => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantFloat(reg, str::parse(&val).ok()?));
                Some(reg)
            }
            Pattern::LiteralTrue => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, true));
                Some(reg)
            }
            Pattern::LiteralFalse => {
                let reg = self.allocate_register();
                self.push_instr(Instr::ConstantBool(reg, false));
                Some(reg)
            }
            Pattern::Wildcard => None,
            Pattern::Variant {
                variant_name,
                fields,
                ..
            } => {
                let Ty::Enum(enum_id, _) = pattern_typed_expr.ty else {
                    self.push_err(
                        format!("didn't get pattern type: {:?}", pattern_typed_expr.ty).as_str(),
                        *pattern_id,
                    );
                    return None;
                };
                let Some(TypeDef::Enum(type_def)) = self.env.lookup_type(&enum_id).cloned() else {
                    self.push_err(
                        format!("didn't get type def for {enum_id:?}").as_str(),
                        *pattern_id,
                    );
                    return None;
                };

                let (tag, variant) = type_def.variants.iter().enumerate().find_map(|(i, v)| {
                    if v.name == variant_name {
                        Some((i, v))
                    } else {
                        None
                    }
                })?;

                let dest = self.allocate_register();
                let Ty::EnumVariant(_, values) = &variant.ty else {
                    self.push_err("did not get enum variant values", *pattern_id);
                    return Some(dest);
                };
                let args = RegisterList(
                    fields
                        .iter()
                        .zip(values)
                        .filter_map(|(f, ty)| {
                            Some(TypedRegister {
                                ty: ty.to_ir(self),
                                register: self._lower_pattern(f)?,
                            })
                        })
                        .collect(),
                );
                self.push_instr(Instr::TagVariant(
                    dest,
                    pattern_typed_expr.ty.to_ir(self),
                    tag as u16,
                    args,
                ));

                Some(dest)
            } // _ => todo!("{:?}", pattern),
        }
    }

    fn lower_member(
        &mut self,
        receiver_id: &Option<ExprID>,
        expr_id: &ExprID,
        name: &str,
        is_lvalue: bool,
    ) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id, self.env)?;

        if let Ty::Enum(sym, _generics) = &typed_expr.ty {
            return self.lower_enum_construction(*expr_id, *sym, name, &typed_expr.ty, &[]);
        }

        if let Ty::EnumVariant(sym, _generics) = &typed_expr.ty {
            return self.lower_enum_construction(*expr_id, *sym, name, &typed_expr.ty, &[]);
        }

        let Some(receiver_id) = receiver_id else {
            unreachable!("we should have a receiver since it's not an enum");
        };

        let Some(receiver) = self.lower_expr(receiver_id) else {
            self.push_err(
                &format!(
                    "did not get receiver register: {:?}, typed_expr: {typed_expr:?}",
                    self.source_file.get(receiver_id)
                ),
                *receiver_id,
            );
            return None;
        };

        let Some(receiver_typed) = self.source_file.typed_expr(receiver_id, self.env) else {
            unreachable!()
        };

        match receiver_typed.ty {
            Ty::Struct(struct_id, _) => {
                let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(&struct_id).cloned()
                else {
                    unreachable!("didn't get struct def");
                };

                if let Some(index) = struct_def.properties.iter().position(|p| p.name == name) {
                    let member_reg = self.allocate_register();

                    self.push_instr(Instr::GetElementPointer {
                        dest: member_reg,
                        base: receiver,
                        ty: receiver_typed.ty.to_ir(self).clone(),
                        index: IRValue::ImmediateInt(index as i64),
                    });

                    if is_lvalue {
                        return Some(member_reg);
                    } else {
                        let member_loaded_reg = self.allocate_register();
                        self.push_instr(Instr::Load {
                            dest: member_loaded_reg,
                            addr: member_reg,
                            ty: typed_expr.ty.to_ir(self),
                        });

                        return Some(member_loaded_reg);
                    }
                }

                if let Some(method) = struct_def.methods.iter().find(|m| m.name == name) {
                    let func = self.allocate_register();
                    let name = Name::Resolved(struct_id, format!("{}_{name}", struct_def.name_str))
                        .mangled(&method.ty);
                    self.push_instr(Instr::Ref(
                        func,
                        typed_expr.ty.to_ir(self),
                        RefKind::Func(name),
                    ));
                    return Some(func);
                }

                None
            }
            _ => {
                self.push_err(format!("Member not lowered {name}").as_str(), *expr_id);
                None
            }
        }
    }

    fn lower_enum_construction(
        &mut self,
        expr_id: ExprID,
        enum_id: SymbolID,
        variant_name: &str,
        ty: &Ty,
        args: &[TypedRegister],
    ) -> Option<Register> {
        let Some(TypeDef::Enum(type_def)) = self.env.lookup_type(&enum_id).cloned() else {
            self.push_err(
                format!("didn't get type def for {enum_id:?}").as_str(),
                expr_id,
            );
            return None;
        };

        let mut tag: Option<u16> = None;

        for (i, var) in type_def.variants.iter().enumerate() {
            if var.name != variant_name {
                continue;
            }

            tag = Some(i as u16);
        }

        let Some(tag) = tag else {
            self.push_err("did not find variant for tag", expr_id);
            return None;
        };

        let dest = self.allocate_register();
        self.push_instr(Instr::TagVariant(
            dest,
            ty.to_ir(self),
            tag,
            RegisterList(args.to_vec()),
        ));

        Some(dest)
    }

    fn lower_return(&mut self, expr_id: &ExprID, rhs: &Option<ExprID>) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id, self.env)?;

        if let Some(rhs) = rhs {
            let register = self.lower_expr(rhs)?;
            let ir_type = typed_expr.ty.to_ir(self);
            self.push_instr(Instr::Ret(ir_type, Some(register.into())));
            Some(register)
        } else {
            self.push_instr(Instr::Ret(IRType::Void, None));
            None
        }
    }

    fn lower_literal(&mut self, expr_id: &ExprID) -> Option<Register> {
        let register = self.allocate_register();
        match self.source_file.get(expr_id)?.clone() {
            Expr::LiteralInt(val) => {
                self.push_instr(Instr::ConstantInt(register, str::parse(&val).ok()?));
                Some(register)
            }
            Expr::LiteralFloat(val) => {
                self.push_instr(Instr::ConstantFloat(register, str::parse(&val).ok()?));
                Some(register)
            }
            Expr::LiteralFalse => {
                self.push_instr(Instr::ConstantBool(register, false));
                Some(register)
            }
            Expr::LiteralTrue => {
                self.push_instr(Instr::ConstantBool(register, true));
                Some(register)
            }
            _ => None,
        }
    }

    fn lower_binary_op(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id, self.env)?;

        let Expr::Binary(lhs, op, rhs) = typed_expr.expr else {
            self.push_err("did get binary expr", *expr_id);
            return None;
        };

        let operand_ty = self.source_file.type_for(lhs, self.env);

        let operand_1 = self.lower_expr(&lhs)?;
        let operand_2 = self.lower_expr(&rhs)?;
        let return_reg = self.allocate_register();

        use TokenKind::*;
        let instr = match op {
            Plus => Instr::Add(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Minus => Instr::Sub(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Star => Instr::Mul(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            Slash => Instr::Div(return_reg, typed_expr.ty.to_ir(self), operand_1, operand_2),
            BangEquals => Instr::Ne(
                return_reg,
                operand_ty
                    .map(|ty| ty.to_ir(self))
                    .unwrap_or(Ty::Void.to_ir(self)),
                operand_1,
                operand_2,
            ),
            EqualsEquals => Instr::Eq(
                return_reg,
                operand_ty
                    .map(|ty| ty.to_ir(self))
                    .unwrap_or(Ty::Void.to_ir(self)),
                operand_1,
                operand_2,
            ),

            Less => Instr::LessThan(
                return_reg,
                operand_ty
                    .map(|ty| ty.to_ir(self))
                    .unwrap_or(Ty::Void.to_ir(self)),
                operand_1,
                operand_2,
            ),
            LessEquals => Instr::LessThanEq(
                return_reg,
                operand_ty
                    .map(|ty| ty.to_ir(self))
                    .unwrap_or(Ty::Void.to_ir(self)),
                operand_1,
                operand_2,
            ),
            Greater => Instr::GreaterThan(
                return_reg,
                operand_ty
                    .map(|ty| ty.to_ir(self))
                    .unwrap_or(Ty::Void.to_ir(self)),
                operand_1,
                operand_2,
            ),
            GreaterEquals => Instr::GreaterThanEq(
                return_reg,
                operand_ty
                    .map(|ty| ty.to_ir(self))
                    .unwrap_or(Ty::Void.to_ir(self)),
                operand_1,
                operand_2,
            ),
            _ => {
                self.push_err(
                    format!("Cannot lower binary operation: {op:?}").as_str(),
                    *expr_id,
                );
                return None;
            }
        };

        self.push_instr(instr);

        Some(return_reg)
    }

    fn lower_assignment(&mut self, lhs_id: &ExprID, rhs_id: &ExprID) -> Option<Register> {
        let rhs = self.lower_expr(rhs_id)?;
        let lhs = self.source_file.typed_expr(lhs_id, self.env)?.clone();

        match &lhs.expr {
            Expr::Let(Name::Resolved(symbol_id, _), _) => {
                self.current_func_mut()?
                    .register_symbol(*symbol_id, rhs.into());
                Some(rhs)
            }
            Expr::Variable(Name::Resolved(symbol, _), _) => {
                let value = self.lookup_register(symbol)?.clone();

                match value {
                    SymbolValue::Register(reg) => {
                        let ty = self.source_file.type_for(*rhs_id, self.env)?;
                        self.push_instr(Instr::StoreLocal(reg, ty.to_ir(self), rhs));
                        None
                    }
                    SymbolValue::Capture(idx, ty) => {
                        let capture_ptr = self.allocate_register();
                        let env_ty = self.current_func()?.env_ty.clone();
                        self.push_instr(Instr::GetElementPointer {
                            dest: capture_ptr,
                            base: Register(0),
                            ty: env_ty?,
                            index: IRValue::ImmediateInt(idx as i64),
                        });
                        self.push_instr(Instr::Store {
                            ty: ty.clone(),
                            val: rhs.into(),
                            location: capture_ptr,
                        });

                        Some(rhs)
                    }
                    SymbolValue::Struct(struct_def) => {
                        unreachable!("Cannot assign to struct: {:?}", struct_def)
                    }
                    SymbolValue::FuncRef(name) => {
                        unreachable!("Cannot assign to func: {:?}", name)
                    }
                }
            }
            Expr::Member(Some(receiver_id), name) => {
                if let Some(dest) = self.lower_member(&Some(*receiver_id), lhs_id, name, true) {
                    self.push_instr(Instr::Store {
                        ty: lhs.ty.to_ir(self),
                        val: rhs.into(),
                        location: dest,
                    });
                    Some(rhs)
                } else {
                    None
                }
            }
            _ => {
                self.push_err(
                    format!("don't know how to lower: {lhs:?}").as_str(),
                    *lhs_id,
                );
                None
            }
        }
    }

    fn lower_block(&mut self, block_id: &ExprID) -> Option<Register> {
        let Expr::Block(exprs) = self.source_file.get(block_id)?.clone() else {
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
            let expr = self.source_file.get(expr_id)?;
            self.push_err(
                format!("Unresolved variable: {name:?} {expr:?}").as_str(),
                *expr_id,
            );
            return None;
        };

        let value = self.lookup_register(symbol_id)?;
        match value.clone() {
            SymbolValue::Register(reg) => Some(reg),
            SymbolValue::Capture(idx, ty) => {
                let env_ptr = self.allocate_register();
                self.push_instr(Instr::GetElementPointer {
                    dest: env_ptr,
                    base: Register(0),
                    ty: IRType::closure(),
                    index: IRValue::ImmediateInt(idx as i64),
                });

                let reg = self.allocate_register();
                self.push_instr(Instr::Load {
                    dest: reg,
                    ty: ty.clone(),
                    addr: env_ptr,
                });

                Some(reg)
            }
            _ => {
                self.push_err(format!("unable to lower: {value:?}").as_str(), *expr_id);
                None
            }
        }
    }

    fn lower_if(&mut self, expr_id: &ExprID) -> Option<Register> {
        let typed_expr = self.source_file.typed_expr(expr_id, self.env)?;
        let Expr::If(cond, conseq, alt) = typed_expr.expr else {
            unreachable!()
        };

        let cond_reg = self.lower_expr(&cond)?;

        let then_id = self.new_basic_block();

        let mut else_reg: Option<Register> = None;
        let else_id: Option<BasicBlockID> = if alt.is_some() {
            Some(self.new_basic_block())
        } else {
            None
        };
        let merge_id = self.new_basic_block(); // All paths merge here

        self.push_instr(Instr::Branch {
            cond: cond_reg,
            true_target: then_id,
            false_target: else_id.unwrap_or(merge_id),
        });

        self.set_current_block(then_id);
        let then_reg = self.lower_expr(&conseq);
        self.push_instr(Instr::Jump(merge_id));

        if let Some(alt) = alt {
            self.set_current_block(else_id?);
            else_reg = self.lower_expr(&alt);
            self.push_instr(Instr::Jump(merge_id));
        }

        self.current_func_mut()?.set_current_block(merge_id).ok()?;

        let phi_dest_reg = self.allocate_register();
        let ir_type = typed_expr.ty.to_ir(self);
        let mut predecessors = vec![];

        if let Some(then_reg) = then_reg {
            predecessors.push((then_reg, then_id));
        }

        if let Some(else_reg) = else_reg
            && let Some(else_id) = else_id
        {
            predecessors.push((else_reg, else_id));
        }

        if predecessors.is_empty() {
            None
        } else {
            self.push_instr(Instr::Phi(
                phi_dest_reg,
                ir_type,
                PhiPredecessors(predecessors),
            ));

            Some(phi_dest_reg)
        }
    }

    fn lower_call(
        &mut self,
        callee: ExprID,
        _type_args: Vec<ExprID>,
        ret_ty: &IRType,
        args: Vec<ExprID>,
        ty: Ty,
    ) -> Option<Register> {
        let callee_typed_expr = self.source_file.typed_expr(&callee, self.env)?;

        let (Ty::Func(params, _, _)
        | Ty::Closure {
            func: box Ty::Func(params, _, _),
            ..
        }
        | Ty::Init(_, params)) = &callee_typed_expr.ty
        else {
            log::error!("didn't get callable: {callee_typed_expr:?}");
            return None;
        };

        // Handle builtins
        if let Expr::Variable(Name::Resolved(symbol, _), _) = &callee_typed_expr.expr
            && crate::builtins::is_builtin_func(symbol)
        {
            return match super::builtins::lower_builtin(symbol, &callee_typed_expr, &args, self) {
                Ok(res) => return res,
                Err(e) => {
                    self.push_err(e.message().as_str(), callee);
                    None
                }
            };
        }

        let mut arg_registers = vec![];
        for (i, arg) in args.iter().enumerate() {
            if let Some(arg_reg) = self.lower_expr(arg) {
                arg_registers.push(TypedRegister {
                    ty: params[i].to_ir(self),
                    register: arg_reg,
                });
            } else {
                self.push_err("Argument expression did not produce a value for call", *arg);
                continue;
            }
        }

        // Handle enum variant construction
        if let Ty::Enum(enum_id, _) = &ty {
            let Expr::Member(_, variant_name) = &callee_typed_expr.expr else {
                self.push_err("didn't get member expr for enum call", callee);
                return None;
            };

            return self.lower_enum_construction(
                callee,
                *enum_id,
                variant_name,
                &ty,
                &arg_registers,
            );
        }

        // Handle enum variant construction
        if let Ty::EnumVariant(enum_id, _) = &ty {
            let Expr::Member(_, variant_name) = &callee_typed_expr.expr else {
                self.push_err("didn't get member expr for enum call", callee);
                return None;
            };

            return self.lower_enum_construction(
                callee,
                *enum_id,
                variant_name,
                &ty,
                &arg_registers,
            );
        }

        // Handle struct construction
        if let Ty::Init(struct_id, params) = &callee_typed_expr.ty {
            return self.lower_init_call(struct_id, &ty, arg_registers, params);
        }

        // Handle method calls
        if let Expr::Member(receiver_id, name) = &callee_typed_expr.expr {
            return self.lower_method_call(
                &callee_typed_expr,
                receiver_id,
                ret_ty,
                name,
                arg_registers,
            );
        }

        // Check to see if we can call this function directly (because its SymbolKind is FuncDef). If it is,
        // we can just call by name. Otherwise if it's something like SymbolKind::Local, we'll have to load
        // the callee from the register.
        if let Expr::Variable(name, _) = &callee_typed_expr.expr
            && let Some(name_info) = self.symbol_table.get(&name.try_symbol_id())
            && name_info.kind == SymbolKind::FuncDef
        {
            // Determine the underlying function type, whether it's a direct function or a closure.
            let (func_ty, is_closure) = match &callee_typed_expr.ty {
                Ty::Closure { func, .. } => (func.as_ref(), true),
                ty @ Ty::Func(..) => (ty, false),
                _ => {
                    self.push_err("Callee variable is not a function or closure", callee);
                    return None;
                }
            };

            let callee_name = name.mangled(func_ty);

            if !is_closure {
                // We can skip all the closure environment ceremony
                let dest_reg = self.allocate_register();

                self.push_instr(Instr::Call {
                    dest_reg,
                    ty: ty.to_ir(self),
                    callee: Callee::Name(callee_name),
                    args: RegisterList(arg_registers),
                });

                return Some(dest_reg);
            }

            // First, get the register holding the pointer to the closure object itself.
            let Some(callee_reg) = self.lower_expr(&callee) else {
                self.push_err(
                    &format!(
                        "Could not lower function variable to get its closure object: {:?}",
                        self.source_file.typed_expr(&callee, self.env)
                    ),
                    callee,
                );
                return None;
            };

            // Now, load the environment pointer from the closure object.
            // The environment is the second element (index 1).
            let env_ptr = self.allocate_register();
            // let env_reg = self.allocate_register();
            self.push_instr(Instr::GetElementPointer {
                dest: env_ptr,
                base: callee_reg,
                ty: IRType::closure(),
                index: IRValue::ImmediateInt(1),
            });

            // Prepend the environment register to the argument list.
            arg_registers.insert(
                0,
                TypedRegister {
                    ty: IRType::POINTER,
                    register: env_ptr,
                },
            );

            // Finally, emit the direct call-by-name instruction.
            let dest_reg = self.allocate_register();
            self.push_instr(Instr::Call {
                dest_reg,
                ty: ty.to_ir(self),
                callee: Callee::Name(callee_name),
                args: RegisterList(arg_registers),
            });
            Some(dest_reg)
        } else {
            // Fallback for indirect calls (e.g., `(if c then f else g)()` ).
            // Here, the callee is not a static name, so we must use the original call-by-reference.
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
                index: IRValue::ImmediateInt(0),
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
                index: IRValue::ImmediateInt(1),
            });
            self.push_instr(Instr::Load {
                dest: env_reg,
                ty: IRType::POINTER,
                addr: env_ptr,
            });

            arg_registers.insert(
                0,
                TypedRegister {
                    ty: IRType::POINTER,
                    register: env_reg,
                },
            );

            let dest_reg = self.allocate_register();
            let ir_type = ty.to_ir(self);
            self.push_instr(Instr::Call {
                ty: ir_type,
                dest_reg,
                callee: func_reg.into(),
                args: RegisterList(arg_registers),
            });

            Some(dest_reg)
        }
    }

    fn lower_init_call(
        &mut self,
        struct_id: &SymbolID,
        ty: &Ty,
        mut arg_registers: Vec<TypedRegister>,
        params: &[Ty],
    ) -> Option<Register> {
        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(struct_id).cloned() else {
            unreachable!()
        };

        let struct_ty = ty.to_ir(self);

        let struct_instance_reg = self.allocate_register();
        self.push_instr(Instr::Alloc {
            dest: struct_instance_reg,
            ty: struct_ty.clone(),
            count: None,
        });

        // Add the instance address as the first arg
        arg_registers.insert(
            0,
            TypedRegister {
                ty: IRType::POINTER,
                register: struct_instance_reg,
            },
        );

        let init_func_ty = Ty::Func(
            params.to_vec(),
            Box::new(ty.clone()),
            vec![], // No generics on init
        );
        let init_func_name = Name::Resolved(*struct_id, format!("{}_init", struct_def.name_str))
            .mangled(&init_func_ty);

        // 3. Call the initializer function
        let initialized_struct_reg = self.allocate_register();
        self.push_instr(Instr::Call {
            dest_reg: initialized_struct_reg,
            ty: struct_ty,
            callee: Callee::Name(init_func_name),
            args: RegisterList(arg_registers),
        });

        Some(struct_instance_reg)
    }

    fn lower_method_call(
        &mut self,
        callee_typed_expr: &TypedExpr,
        receiver_id: &Option<ExprID>,
        ret_ty: &IRType,
        name: &str,
        mut arg_registers: Vec<TypedRegister>,
    ) -> Option<Register> {
        let Some(receiver_id) = receiver_id else {
            log::error!("no receiver for member expr");
            return None;
        };

        let Some(receiver_ty) = self.source_file.typed_expr(receiver_id, self.env) else {
            log::error!("could not determine type of receiver");
            return None;
        };

        let Some(receiver) = self.lower_expr(receiver_id) else {
            log::error!("could not lower member receiver: {callee_typed_expr:?}");
            return None;
        };

        let type_var_id = if let IRType::TypeVar(type_var) = &receiver_ty.ty.to_ir(self) {
            Some(type_var.clone())
        } else {
            None
        };

        arg_registers.insert(
            0,
            TypedRegister {
                ty: IRType::Pointer { hint: type_var_id },
                register: receiver,
            },
        );

        let callee_name = match &receiver_ty.ty {
            Ty::Struct(struct_id, _) => {
                let struct_def = self.env.lookup_struct(struct_id)?;
                let method = struct_def.methods.iter().find(|m| m.name == name)?;
                Some(format!(
                    "@_{}_{}_{}",
                    struct_id.0, struct_def.name_str, method.name
                ))
            }
            Ty::TypeVar(type_var) if !type_var.constraints.is_empty() => {
                let mut result = None;
                for constraint in &type_var.constraints {
                    let TypeConstraint::Conforms { protocol_id, .. } = constraint else {
                        continue;
                    };

                    let protocol_def = self.env.lookup_protocol(protocol_id)?;
                    if let Some(method) = protocol_def.methods.iter().find(|m| m.name == name) {
                        result = Some(format!(
                            "@_{}_{}_{}",
                            protocol_def.symbol_id.0, protocol_def.name_str, method.name
                        ));

                        break;
                    } else if let Some(method) = protocol_def
                        .method_requirements
                        .iter()
                        .find(|m| m.name == name)
                    {
                        result = Some(format!(
                            "@_{}_{}_{}",
                            protocol_def.symbol_id.0, protocol_def.name_str, method.name
                        ));

                        break;
                    }
                }

                result
            }
            _ => None,
        };

        let Some(callee_name) = callee_name else {
            self.push_err(
                &format!("Could not determine callee. Receiver: {receiver_ty:?}"),
                *receiver_id,
            );
            return None;
        };

        let result_reg = self.allocate_register();
        self.push_instr(Instr::Call {
            dest_reg: result_reg,
            ty: ret_ty.clone(),
            callee: Callee::Name(callee_name),
            args: RegisterList(arg_registers),
        });

        Some(result_reg)
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
        generics: Vec<IRType>,
    ) {
        // Create the environment struct
        let environment_register = self.allocate_register();
        let environment_type = IRType::Struct(SymbolID(0), capture_types.clone(), generics);
        self.push_instr(Instr::MakeStruct {
            dest: environment_register,
            ty: environment_type.clone(),
            values: RegisterList(
                capture_types
                    .into_iter()
                    .zip(capture_registers)
                    .map(|(ty, register)| TypedRegister { ty, register })
                    .collect(),
            ),
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
            val: environment_register.into(),
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
            index: IRValue::ImmediateInt(1),
        });
        self.push_instr(Instr::GetElementPointer {
            dest: fn_ptr,
            base: closure_ptr,
            ty: IRType::closure(),
            index: IRValue::ImmediateInt(0),
        });

        // Store the environment and function pointers
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: env_dest_ptr.into(),
            location: env_ptr,
        });
        self.push_instr(Instr::Store {
            ty: IRType::POINTER,
            val: func_ref_reg.into(),
            location: fn_ptr,
        });
    }

    fn push_constant(&mut self, constant: IRConstantData) {
        self.constants.push(constant)
    }

    pub(super) fn push_instr(&mut self, instr: Instr) {
        let expr_id = self.current_expr_ids.last().copied();
        #[allow(clippy::unwrap_used)]
        self.current_block_mut()
            .unwrap()
            .instructions
            .push(InstructionWithExpr { instr, expr_id });
    }

    pub(super) fn allocate_register(&mut self) -> Register {
        #[allow(clippy::unwrap_used)]
        self.current_func_mut().unwrap().registers.allocate()
    }

    fn lookup_register(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        self.lookup_symbol(symbol_id)
    }

    fn lookup_symbol(&self, symbol_id: &SymbolID) -> Option<&SymbolValue> {
        if let Some(val) = self
            .current_functions
            .last()
            .and_then(|f| f._lookup_symbol(symbol_id))
        {
            return Some(val);
        }

        self.globals.get(symbol_id)
    }

    fn register_global(&mut self, symbol_id: &SymbolID, value: SymbolValue) {
        self.globals.insert(*symbol_id, value);
    }

    fn current_func_mut(&mut self) -> Option<&mut CurrentFunction> {
        self.current_functions.last_mut()
    }

    fn current_func(&mut self) -> Option<&CurrentFunction> {
        self.current_functions.last()
    }

    fn current_block_mut(&mut self) -> Option<&mut CurrentBasicBlock> {
        Some(self.current_func_mut()?.current_block_mut())
    }

    fn set_current_block(&mut self, id: BasicBlockID) -> Option<()> {
        self.current_func_mut()?.set_current_block(id).ok();

        Some(())
    }

    fn new_basic_block(&mut self) -> BasicBlockID {
        #[allow(clippy::unwrap_used)]
        let id = self.current_func_mut().unwrap().next_block_id();
        let block = CurrentBasicBlock {
            id,
            instructions: Vec::new(),
        };

        #[allow(clippy::unwrap_used)]
        self.current_func_mut().unwrap().add_block(block);
        id
    }

    fn resolve_name(&mut self, name: Option<Name>) -> Name {
        match name {
            Some(name @ Name::Resolved(_, _)) => name,
            None => {
                let name_str = format!("fn{}", self.symbol_table.max_id() + 1);
                let symbol = self
                    .symbol_table
                    .add(&name_str, SymbolKind::CustomType, 12345, None);
                Name::Resolved(symbol, name_str)
            }
            _ => Name::Raw("<undefined>".into()),
        }
    }

    pub fn add_diagnostic(&self, diagnostic: Diagnostic) {
        if let Ok(mut lock) = self.session.lock() {
            lock.add_diagnostic(self.source_file.path.clone(), diagnostic);
        }
    }

    pub fn push_err(&mut self, message: &str, expr_id: ExprID) -> IRError {
        self.add_diagnostic(Diagnostic::lowering(
            self.source_file.path.clone(),
            expr_id,
            IRError::Unknown(message.to_string()),
        ));

        IRError::Unknown(message.to_string())
    }

    pub fn property_index(&self, name: &str, irtype: IRType) -> Option<usize> {
        let IRType::Struct(symbol_id, _, _) = irtype else {
            unreachable!("didn't get property index for {:?}", irtype)
        };

        let Some(TypeDef::Struct(struct_def)) = self.env.lookup_type(&symbol_id) else {
            unreachable!("didn't get typedef for {:?}", irtype)
        };

        struct_def.properties.iter().position(|k| k.name == name)
    }
}

fn find_or_create_main(
    source_file: &mut SourceFile<Typed>,
    symbol_table: &mut SymbolTable,
    env: &mut Environment,
) -> (ExprID, bool) {
    for root in source_file.typed_roots(env) {
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
        env.next_id(),
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
        env,
    );

    source_file.add(
        env.next_id(),
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
            kind: SymbolKind::FuncDef,
            expr_id: SymbolID::GENERATED_MAIN.0,
            is_captured: false,
            definition: None,
        },
    );

    (SymbolID::GENERATED_MAIN.0, true)
}
