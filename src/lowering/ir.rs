use crate::{
    Typed,
    expr::{Expr, FuncName},
    lexing::token_kind::TokenKind,
    parser::ExprID,
    parsing::name::Name,
    source_file::SourceFile,
    symbol_table::SymbolID,
    type_checker::Ty,
    typed_expr::TypedExpr,
};
use std::collections::HashMap;

/// A minimal IR for our language
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum Instr {
    // Load constants
    LoadInt(i64),
    LoadFloat(f64),
    LoadBool(bool),

    // Variable/Local access
    LoadLocal(u32),  // push value of local slot (u32 index)
    StoreLocal(u32), // pop and store into local slot (u32 index)

    // Function operations
    Call(SymbolID, usize), // call function SymbolID with arg count
    Return,

    // Arithmetic and logical operations (assuming stack-based evaluation)
    Add,
    Subtract,
    Multiply,
    Divide,
    Negate, // For unary minus
    Not,    // For unary boolean not

    // Comparison operations
    Equals,          // ==
    NotEquals,       // !=
    LessThan,        // <
    LessThanOrEqual, // <=
    GreaterThan,     // >
    GreaterThanOrEqual, // >=
                     // Pop, // Useful if expressions have values that are not used.
}

/// Lowers AST expressions into IR
#[allow(dead_code)]
pub struct Lowerer<'a> {
    source_file: &'a SourceFile<Typed>,
    function_irs: HashMap<SymbolID, Vec<Instr>>, // Stores IR for all functions
    current_instrs: Vec<Instr>,                  // IR for the function currently being lowered
    local_slots: HashMap<SymbolID, u32>,         // Maps SymbolID to stack slot index
    next_slot_index: u32,                        // Next available slot index for locals/params
    current_function_id: Option<SymbolID>,       // ID of the function being processed
}

#[allow(dead_code)]
impl<'a> Lowerer<'a> {
    pub fn new(source_file: &'a SourceFile<Typed>) -> Self {
        Self {
            source_file,
            function_irs: HashMap::new(),
            current_instrs: Vec::new(),
            local_slots: HashMap::new(),
            next_slot_index: 0,
            current_function_id: None,
        }
    }

    /// Main public method to lower the entire source file into a map of function IRs.
    pub fn lower_module(mut self) -> HashMap<SymbolID, Vec<Instr>> {
        let roots = self.source_file.typed_roots().to_vec(); // Clone to avoid borrow issues

        for typed_expr_root in roots {
            if let TypedExpr {
                expr: Expr::Func(Some(func_name_resolved), _, ref params, body_id, _),
                ..
            } = typed_expr_root
            {
                let func_symbol_id = match func_name_resolved {
                    FuncName::Resolved(id) => id,
                    FuncName::Main => self
                        .source_file
                        .symbol_table()
                        .lookup("main") // Assuming "main" is the string name
                        .expect("Main function symbol not found in symbol table"),
                    _ => {
                        // Skip anonymous functions or those not properly resolved at the root
                        // Or handle them if your language supports top-level anonymous func expressions
                        eprintln!(
                            "Skipping unhandled root function name: {:?}",
                            func_name_resolved
                        );
                        continue;
                    }
                };
                self.lower_function(func_symbol_id, params, body_id);
            }
        }
        self.function_irs
    }

    /// Lowers a single function.
    fn lower_function(&mut self, func_id: SymbolID, params: &[ExprID], body_id: ExprID) {
        log::trace!("Lowering function {:?}, {:?} {}", func_id, params, body_id);
        self.current_instrs.clear();
        self.local_slots.clear();
        self.next_slot_index = 0;
        self.current_function_id = Some(func_id);

        // Allocate slots for parameters first.
        // Parameters are like local variables, assigned values at the start of the call.
        // The actual loading of argument values into these slots is part of the calling convention,
        // often handled by the Call instruction or prologue. Here, we just reserve slots.
        for param_expr_id in params {
            if let Some(typed_param_expr) = self.source_file.types().get(param_expr_id) {
                log::debug!(
                    "Lowerer: For param ExprID {}, found TypedExpr.expr: {:?}",
                    param_expr_id,
                    typed_param_expr.expr
                );
                if let Expr::Parameter(Name::Resolved(param_symbol_id, _), _) =
                    &typed_param_expr.expr
                {
                    self.alloc_slot_for_local(*param_symbol_id);
                }
            } else {
                log::error!("No TypedExpr for {}", param_expr_id);
            }
        }

        self.lower_expr(body_id);

        // Ensure functions (especially non-void ones) have their return value on stack
        // and end with a Return instruction if one isn't already the last.
        let function_type = self
            .source_file
            .type_from_symbol(&func_id)
            .expect("Function type not found during lowering");

        let is_void_function = match function_type {
            Ty::Func(_, ret_ty) => matches!(*ret_ty, Ty::Void),
            _ => false, // Should not happen for a function symbol
        };

        if self
            .current_instrs
            .last()
            .map_or(true, |instr| !matches!(instr, Instr::Return))
        {
            if is_void_function && body_id == -1 { // Special case for empty main generated by old code
                // If it's an empty void function (e.g. placeholder main), just return.
            } else {
                // If the body_id is valid, its value should be on the stack.
                // All Talk functions return a value; if no explicit return, last expr is the value.
            }
            self.current_instrs.push(Instr::Return);
        }

        self.function_irs
            .insert(func_id, self.current_instrs.clone());
    }

    /// Allocates a new stack slot for a local variable or parameter.
    fn alloc_slot_for_local(&mut self, symbol_id: SymbolID) -> u32 {
        *self.local_slots.entry(symbol_id).or_insert_with(|| {
            let slot = self.next_slot_index;
            self.next_slot_index += 1;
            slot
        })
    }

    /// Gets the slot for a local. Panics if not found (should be allocated by `Let` or params).
    fn get_local_slot(&self, symbol_id: &SymbolID) -> u32 {
        *self
            .local_slots
            .get(symbol_id)
            .unwrap_or_else(|| panic!("Local variable slot not found for {:?}", symbol_id))
    }

    /// Recursively lowers an expression AST node into IR instructions.
    fn lower_expr(&mut self, expr_id: ExprID) {
        let typed_expr = match self.source_file.types().get(&expr_id) {
            Some(te) => te.clone(),
            None => {
                eprintln!(
                    "Lowerer Error: TypedExpr not found for ExprID {:?}",
                    expr_id
                );
                return;
            }
        };

        match &typed_expr.expr {
            Expr::LiteralInt(val_str) => {
                if let Ok(val) = val_str.parse::<i64>() {
                    self.current_instrs.push(Instr::LoadInt(val));
                } else {
                    eprintln!("Error parsing int literal: {}", val_str);
                }
            }
            Expr::LiteralFloat(val_str) => {
                if let Ok(val) = val_str.parse::<f64>() {
                    self.current_instrs.push(Instr::LoadFloat(val));
                } else {
                    eprintln!("Error parsing float literal: {}", val_str);
                }
            }
            Expr::LiteralTrue => self.current_instrs.push(Instr::LoadBool(true)),
            Expr::LiteralFalse => self.current_instrs.push(Instr::LoadBool(false)),

            Expr::Variable(Name::Resolved(symbol_id, _), _) => {
                let slot = self.get_local_slot(symbol_id);
                self.current_instrs.push(Instr::LoadLocal(slot));
            }

            Expr::Let(Name::Resolved(symbol_id, _), _) => {
                // This is just a declaration like `let x;`. Slot allocation is primary.
                // If it was `let x = val;`, it's an Assignment node.
                self.alloc_slot_for_local(*symbol_id);
                // No instruction is emitted for just a declaration unless it implies default initialization.
                // If default init to e.g. 0 or null is needed, push Load then StoreLocal here.
                // For now, just ensures slot exists.
            }

            Expr::Assignment(lhs_expr_id, rhs_expr_id) => {
                // Evaluate RHS, its value will be on the stack
                self.lower_expr(*rhs_expr_id);

                // Determine the LHS variable's slot
                let lhs_typed_expr = self
                    .source_file
                    .types()
                    .get(lhs_expr_id)
                    .expect("LHS of assignment not found");

                let symbol_id_to_store = match &lhs_typed_expr.expr {
                    Expr::Let(Name::Resolved(id, _), _) => *id,
                    Expr::Variable(Name::Resolved(id, _), _) => *id, // Re-assignment
                    _ => {
                        eprintln!(
                            "LHS of assignment is not a storable variable: {:?}",
                            lhs_typed_expr.expr
                        );
                        return;
                    }
                };
                let slot = self.alloc_slot_for_local(symbol_id_to_store); // Ensure allocated if it's a `let name =`
                self.current_instrs.push(Instr::StoreLocal(slot));
            }

            Expr::Block(item_ids) => {
                for item_id in item_ids.iter() {
                    self.lower_expr(*item_id);
                    // If it's not the last expression in the block, and if the IR had a Pop instruction,
                    // and the expression type is not Void, we might pop its result.
                    // Current IR: value of non-last expressions are left on stack and implicitly consumed or become dead.
                    // The value of the block is the value of its last expression, which is left on stack.
                }
            }

            Expr::Call(callee_expr_id, arg_ids) => {
                // Evaluate arguments and push them onto the stack (left-to-right assumed)
                for arg_id in arg_ids {
                    self.lower_expr(*arg_id);
                }

                let callee_typed_expr = self
                    .source_file
                    .types()
                    .get(callee_expr_id)
                    .expect("Callee expression not found");

                match &callee_typed_expr.expr {
                    Expr::Variable(Name::Resolved(func_symbol_id, _), _) => {
                        // Direct function call
                        self.current_instrs
                            .push(Instr::Call(*func_symbol_id, arg_ids.len()));
                    }
                    Expr::Member(_receiver_opt_expr_id, member_name_str) => {
                        // This could be an enum constructor (e.g. Option.some) or a method call.
                        // For enum constructors, the type checker should have resolved this `Member`
                        // expression to have a function type, and ideally, its `SymbolID` (of the constructor function)
                        // should be discoverable.
                        // If the `TypedExpr` for this `Member` node IS the constructor function itself...
                        // This part often needs the `SymbolID` of the *constructor function* not just the enum/variant name.
                        // The `TypeChecker` or `ConstraintSolver` should associate the `Expr::Member` node (`callee_expr_id`)
                        // with the actual callable `SymbolID`.

                        // A simplification: Assume the type of the Member node IS the function,
                        // and its SymbolID is somehow available or encoded.
                        // This is a placeholder: A robust solution would get the concrete SymbolID of the constructor.
                        // For now, we try to see if the node ID itself corresponds to a known function SymbolID
                        // (e.g. if the Member node was replaced or annotated).
                        // This needs deeper integration with how member resolution provides callable SymbolIDs.

                        // Attempt to get a SymbolID if the member resolved to a "variable-like" entity (the function itself)
                        // This is highly dependent on how `Expr::Member` is typed and resolved.
                        // If the type checker stores the resolved SymbolID of the function/method in the TypedExpr for the Member.
                        // Let's assume for now that the `callee_expr_id` for `Expr::Member` (that is a function)
                        // has a `SymbolID` retrievable via the symbol table using `callee_expr_id`.
                        // This is often not direct. The `SymbolID` should ideally be part of the `TypedExpr` or `Expr::Member` itself after resolution.
                        if let Some(symbol) = self.source_file.get_direct_callable(callee_expr_id) {
                            self.current_instrs.push(Instr::Call(symbol, arg_ids.len()));
                        } else {
                            // Fallback: if the callee_expr_id's *type* is a function, it might be an indirect call,
                            // or it could be that `member_name_str` needs lookup in a type's method table.
                            // This is where it gets complex.
                            eprintln!(
                                "Lowering for direct member call of '{}' is not fully resolved to SymbolID.",
                                member_name_str
                            );
                            // You might need to evaluate the receiver first if it's a method call `obj.method()`.
                            // if let Some(receiver_id) = receiver_opt_expr_id {
                            //    self.lower_expr(*receiver_id); // Receiver on stack
                            //    // Then call method (Instr::MethodCall(method_id, num_args_incl_receiver))
                            // }
                        }
                    }
                    _ => {
                        // Callee is a complex expression (e.g., a function returned from another function).
                        // This requires an indirect call instruction (e.g., CallIndirect) which our IR lacks.
                        self.lower_expr(*callee_expr_id); // The function address/value is now on stack
                        eprintln!(
                            "Indirect function calls not supported by current IR for: {:?}",
                            callee_typed_expr.expr
                        );
                        // self.current_instrs.push(Instr::CallIndirect(arg_ids.len())); // If we had it
                    }
                }
            }

            Expr::Unary(op_kind, operand_expr_id) => {
                self.lower_expr(*operand_expr_id); // Operand's value on stack
                match op_kind {
                    TokenKind::Minus => self.current_instrs.push(Instr::Negate),
                    TokenKind::Bang => self.current_instrs.push(Instr::Not),
                    _ => eprintln!("Unsupported unary operator: {:?}", op_kind),
                }
            }

            Expr::Binary(lhs_expr_id, op_kind, rhs_expr_id) => {
                self.lower_expr(*lhs_expr_id); // LHS value on stack
                self.lower_expr(*rhs_expr_id); // RHS value on stack (LHS below RHS)
                match op_kind {
                    TokenKind::Plus => self.current_instrs.push(Instr::Add),
                    TokenKind::Minus => self.current_instrs.push(Instr::Subtract),
                    TokenKind::Star => self.current_instrs.push(Instr::Multiply),
                    TokenKind::Slash => self.current_instrs.push(Instr::Divide),
                    TokenKind::Less => self.current_instrs.push(Instr::LessThan),
                    TokenKind::LessEquals => self.current_instrs.push(Instr::LessThanOrEqual),
                    TokenKind::Greater => self.current_instrs.push(Instr::GreaterThan),
                    TokenKind::GreaterEquals => self.current_instrs.push(Instr::GreaterThanOrEqual),
                    TokenKind::EqualsEquals => self.current_instrs.push(Instr::Equals),
                    TokenKind::BangEquals => {
                        // Implement as Equals then Not
                        self.current_instrs.push(Instr::Equals);
                        self.current_instrs.push(Instr::Not);
                    }
                    _ => eprintln!("Unsupported binary operator: {:?}", op_kind),
                }
            }

            Expr::If(cond_id, _then_id, _else_id_opt) => {
                // Full if/else requires jump instructions (e.g., JumpIfFalse, Jump).
                // Our current IR (Instr enum) lacks these.
                // For a simple IR, you might:
                // 1. Only support `if` for side effects if blocks don't return values.
                // 2. Disallow `if` expressions that return values unless they can be transformed
                //    (e.g. into something like C's ternary `cond ? then_val : else_val` which
                //    might map to specific CPU instructions like CMOV if available and targeted).
                // 3. For now, we can lower the condition as its side effects might matter.
                self.lower_expr(*cond_id); // Condition value is on stack
                // ... but we can't act on it with current IR for branching.
                eprintln!(
                    "If/Else expression lowering is limited due to lack of jump instructions in IR."
                );
                // To make this "work" somewhat, if the `if` has a value, one might attempt to
                // lower both branches and then use a (non-existent) conditional select instruction.
                // Or, if it's just for side effects and the language allows, conditionally execute.
                // This is a significant limitation of the current IR.
            }

            Expr::Loop(opt_cond_id, body_id) => {
                eprintln!(
                    "Loop expression lowering requires jump instructions, not supported by current IR."
                );
                // A loop `loop { body }` would be:
                // L_START:
                //   lower(body)
                //   Jump L_START
                // A loop `loop cond { body }` would be:
                // L_START:
                //   lower(cond)
                //   JumpIfFalse L_END
                //   lower(body)
                //   Jump L_START
                // L_END:
                // These are not possible now.
                // If condition exists, we can lower it for its side-effects:
                if let Some(cond_id) = opt_cond_id {
                    self.lower_expr(*cond_id);
                    // self.current_instrs.push(Instr::Pop); // if cond has value not used by branching
                }
                // We can lower the body once for its side-effects, but cannot loop.
                self.lower_expr(*body_id);
            }

            // Declarations and Type Representations: These don't typically generate executable code directly.
            // Their information is used during type checking, name resolution, and to inform lowering of other expressions.
            Expr::Func(_, _, _, _, _) => { /* Function definitions are handled by lower_function */
            }
            Expr::EnumDecl(_, _, _) => { /* Enum declarations are compile-time info */ }
            Expr::EnumVariant(_, _) => { /* Enum variants are part of EnumDecl */ }
            Expr::Parameter(_, _) => { /* Parameters are handled in lower_function context */ }
            Expr::TypeRepr(_, _, _) | Expr::FuncTypeRepr(_, _, _) | Expr::TupleTypeRepr(_, _) => {
                /* Type representations are compile-time info */
            }

            // Match Expressions: Highly complex without jumps and conditional logic.
            Expr::Match(scrutinee_id, _arm_ids) => {
                self.lower_expr(*scrutinee_id); // Scrutinee value on stack
                eprintln!(
                    "Match expression lowering is highly complex and not supported by current IR (needs jumps, pattern matching ops)."
                );
                // For each arm:
                //   - Match pattern against scrutinee (complex)
                //   - If match, execute arm body
                //   - Jump to end
                // This needs specialized IR instructions or complex jump sequences.
            }
            Expr::MatchArm(_, _) | Expr::Pattern(_) | Expr::PatternVariant(_, _, _) => {
                eprintln!(
                    "Match arm/pattern lowering part of Match, not directly lowered in this pass."
                );
            }

            Expr::Tuple(item_ids) => {
                // How tuples are represented depends on the target / calling convention.
                // Option 1: They are heap-allocated objects created by a runtime call.
                //    for item_id in item_ids { self.lower_expr(*item_id); }
                //    self.current_instrs.push(Instr::Call(RUNTIME_TUPLE_NEW_ID, item_ids.len()));
                // Option 2: Small tuples might be passed in multiple registers or stack slots.
                //    This simple IR doesn't have a direct tuple type or constructor.
                // For now, we'll just evaluate items; their values will be on stack.
                for item_id in item_ids {
                    self.lower_expr(*item_id);
                }
                eprintln!(
                    "Tuple expression lowering: items evaluated on stack. Specific tuple construction IR is missing."
                );
            }

            Expr::Member(receiver_opt_expr_id, member_name_str) => {
                // This is for field access, e.g., `obj.field`.
                // If it's a callable (method/constructor), `Expr::Call` handles it.
                // If it's data access:
                //   1. Lower receiver if present: `self.lower_expr(*receiver_id);`
                //   2. Need to know offset of `member_name_str` within the object/struct.
                //   3. Add instruction like `LoadField(offset)` or `LoadStructMember(type_id, member_id)`.
                // This IR lacks such instructions.
                if let Some(receiver_id) = receiver_opt_expr_id {
                    self.lower_expr(*receiver_id); // Receiver on stack
                }
                eprintln!(
                    "Member field access lowering for '{}' is not supported by current IR.",
                    member_name_str
                );
            }

            Expr::Variable(Name::Raw(r), _) => {
                eprintln!(
                    "Lowerer Error: Encountered unresolved raw variable name: {}",
                    r
                );
            }

            _ => panic!("Unhandled expr: {:?}", expr_id),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        constraint_solver::ConstraintSolver, name_resolver::NameResolver, parser::parse,
        type_checker::TypeChecker,
    };

    // Helper to create a SourceFile<Typed> from code string for testing
    fn get_typed_sourcefile(code: &str) -> SourceFile<Typed> {
        let parsed = parse(code).expect("Parse failed");
        let resolver = NameResolver::default(); // Use default for simple tests
        let resolved = resolver.resolve(parsed);
        let checker = TypeChecker;
        let mut inferred = checker
            .infer(resolved) // Use infer which imports prelude
            .expect("Type inference failed");
        let mut solver = ConstraintSolver::new(&mut inferred);
        solver.solve().expect("Constraint solving failed");
        inferred
    }

    #[test]
    fn lowers_simple_main_with_int_literal() {
        let code = "func main() { 123 }";
        let typed_sf = get_typed_sourcefile(code);
        let lowerer = Lowerer::new(&typed_sf);
        let all_irs = lowerer.lower_module();

        let main_sym_id = typed_sf
            .symbol_table()
            .lookup("main")
            .expect("main symbol not found");

        assert!(all_irs.contains_key(&main_sym_id));
        let main_ir = &all_irs[&main_sym_id];
        assert_eq!(main_ir, &vec![Instr::LoadInt(123), Instr::Return]);
    }

    #[test]
    fn lowers_let_and_variable() {
        let code = "func main() { let x = 42\n x }";
        let typed_sf = get_typed_sourcefile(code);
        let lowerer = Lowerer::new(&typed_sf);
        let all_irs = lowerer.lower_module();
        let main_sym_id = typed_sf.symbol_table().lookup("main").unwrap();
        let main_ir = &all_irs[&main_sym_id];

        // Expected: Load 42, StoreLocal 0 (for x), LoadLocal 0 (for x), Return
        assert_eq!(main_ir.len(), 4);
        assert_eq!(main_ir[0], Instr::LoadInt(42));
        assert!(matches!(main_ir[1], Instr::StoreLocal(0))); // Slot 0 for x
        assert!(matches!(main_ir[2], Instr::LoadLocal(0))); // Slot 0 for x
        assert_eq!(main_ir[3], Instr::Return);
    }

    #[test]
    fn lowers_binary_addition() {
        let code = "func main() { 1 + 2 }";
        let typed_sf = get_typed_sourcefile(code);
        let lowerer = Lowerer::new(&typed_sf);
        let all_irs = lowerer.lower_module();
        let main_sym_id = typed_sf.symbol_table().lookup("main").unwrap();
        let main_ir = &all_irs[&main_sym_id];

        assert_eq!(
            main_ir,
            &vec![
                Instr::LoadInt(1),
                Instr::LoadInt(2),
                Instr::Add,
                Instr::Return
            ]
        );
    }

    #[test]
    fn lowers_function_call_no_args() {
        let code = "func foo() { 7 } func main() { foo() }";
        let typed_sf = get_typed_sourcefile(code);
        let lowerer = Lowerer::new(&typed_sf);
        let all_irs = lowerer.lower_module();

        let main_sym_id = typed_sf.symbol_table().lookup("main").unwrap();
        let foo_sym_id = typed_sf.symbol_table().lookup("foo").unwrap();

        let main_ir = &all_irs[&main_sym_id];
        assert_eq!(main_ir, &vec![Instr::Call(foo_sym_id, 0), Instr::Return]);

        let foo_ir = &all_irs[&foo_sym_id];
        assert_eq!(foo_ir, &vec![Instr::LoadInt(7), Instr::Return]);
    }

    #[test]
    fn lowers_function_call_with_args_and_params() {
        let code = "func add(a: Int, b: Int) { a + b } func main() { add(3, 4) }";
        let typed_sf = get_typed_sourcefile(code);
        let lowerer = Lowerer::new(&typed_sf);
        let all_irs = lowerer.lower_module();

        let main_sym_id = typed_sf.symbol_table().lookup("main").unwrap();
        let add_sym_id = typed_sf.symbol_table().lookup("add").unwrap();

        let main_ir = &all_irs[&main_sym_id];
        // Load 3, Load 4, Call add_sym_id with 2 args, Return
        assert_eq!(
            main_ir,
            &vec![
                Instr::LoadInt(3),
                Instr::LoadInt(4),
                Instr::Call(add_sym_id, 2),
                Instr::Return
            ]
        );

        let add_ir = &all_irs[&add_sym_id];
        // Params 'a' and 'b' will be in slots 0 and 1
        // LoadLocal 0 (a), LoadLocal 1 (b), Add, Return
        assert_eq!(
            add_ir,
            &vec![
                Instr::LoadLocal(0),
                Instr::LoadLocal(1),
                Instr::Add,
                Instr::Return
            ]
        );
    }

    // TODO: Add more tests for other expressions:
    // - Unary operations
    // - More complex blocks
    // - (Limited) If/Loop/Match noting their current output due to IR constraints
    // - Multiple functions
}
