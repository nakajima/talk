#[cfg(test)]
mod optional_tests {
    use talk::{expr::Expr, parser::parse};

    #[test]
    fn gets_parsed() {
        let parsed = parse("let a: Int?", "-".into());
        let Expr::Let(_, Some(ty)) = parsed.roots()[0].unwrap() else {
            panic!("didn't get let expr");
        };

        assert_eq!(
            *parsed.get(ty).unwrap(),
            Expr::TypeRepr("Optional".into(), vec![0], false)
        );

        assert_eq!(
            *parsed.get(&0).unwrap(),
            Expr::TypeRepr("Int".into(), vec![], false)
        );
    }
}

#[cfg(test)]
mod array_tests {
    use talk::{
        SymbolID,
        compiling::driver::Driver,
        expr::Expr,
        lowering::{
            instr::Instr,
            ir_module::IRModule,
            ir_type::IRType,
            lowerer::{BasicBlock, BasicBlockID, IRFunction},
            register::Register,
        },
        parser::parse,
        type_checker::Ty,
    };

    #[test]
    fn gets_parsed() {
        let parsed = parse("[1,2,3]", "-".into());
        assert_eq!(
            *parsed.roots()[0].unwrap(),
            Expr::LiteralArray(vec![0, 1, 2])
        );

        assert_eq!(*parsed.get(&0).unwrap(), Expr::LiteralInt("1".into()));
        assert_eq!(*parsed.get(&1).unwrap(), Expr::LiteralInt("2".into()));
        assert_eq!(*parsed.get(&2).unwrap(), Expr::LiteralInt("3".into()));
    }

    #[test]
    fn gets_typed() {
        let checked = talk::type_checking::check("[1,2,3]").unwrap();
        assert_eq!(
            checked.type_for(checked.root_ids()[0]).unwrap(),
            Ty::Struct(SymbolID::ARRAY, vec![Ty::Int])
        );
    }

    #[test]
    fn gets_count() {
        let checked = talk::type_checking::check("[1,2,3].count").unwrap();
        assert_eq!(checked.type_for(checked.root_ids()[0]).unwrap(), Ty::Int);
    }

    #[test]
    fn lowers_literal() {
        let mut driver = Driver::with_str("[1,2,3].count");
        let module = driver.lower().into_iter().next().unwrap().module();

        talk::assert_lowered_functions!(
            module,
            vec![IRFunction {
                ty: IRType::Func(vec![], IRType::Void.into()).clone(),
                name: "@main".into(),
                blocks: vec![BasicBlock {
                    id: BasicBlockID(0),
                    instructions: vec![
                        Instr::Alloc {
                            dest: Register(1),
                            ty: IRType::array(),
                            count: None
                        },
                        // Set the array's count
                        Instr::ConstantInt(Register(2), 3),
                        Instr::GetElementPointer {
                            dest: Register(3),
                            base: Register(1),
                            ty: IRType::array(),
                            index: 0
                        },
                        Instr::Store {
                            location: Register(3),
                            ty: IRType::Int,
                            val: Register(2)
                        },
                        // Set the array's capacity
                        Instr::ConstantInt(Register(4), 3),
                        Instr::GetElementPointer {
                            dest: Register(5),
                            base: Register(1),
                            ty: IRType::array(),
                            index: 1
                        },
                        Instr::Store {
                            location: Register(5),
                            ty: IRType::Int,
                            val: Register(4)
                        },
                        // Get array's storage pointer
                        Instr::GetElementPointer {
                            dest: Register(6),
                            base: Register(1),
                            ty: IRType::array(),
                            index: 2
                        },
                        // Alloc space for the items
                        Instr::Alloc {
                            dest: Register(7),
                            ty: IRType::Int,
                            count: Some(Register(2))
                        },
                        Instr::Store {
                            ty: IRType::Pointer,
                            val: Register(7),
                            location: Register(6)
                        },
                        // Store first element
                        Instr::ConstantInt(Register(8), 1),
                        Instr::GetElementPointer {
                            dest: Register(9),
                            base: Register(7),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: 0
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(8),
                            location: Register(9)
                        },
                        // Store second element
                        Instr::ConstantInt(Register(10), 2),
                        Instr::GetElementPointer {
                            dest: Register(11),
                            base: Register(7),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: 1
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(10),
                            location: Register(11)
                        },
                        // Store third element
                        Instr::ConstantInt(Register(12), 3),
                        Instr::GetElementPointer {
                            dest: Register(13),
                            base: Register(7),
                            ty: IRType::Array {
                                element: IRType::Int.into()
                            },
                            index: 2
                        },
                        Instr::Store {
                            ty: IRType::Int,
                            val: Register(12),
                            location: Register(13)
                        },
                        Instr::Load {
                            dest: Register(14),
                            ty: IRType::array(),
                            addr: Register(1),
                        },
                        // Get .count
                        Instr::GetElementPointer {
                            dest: Register(15),
                            base: Register(14),
                            ty: IRType::array(),
                            index: 0
                        },
                        Instr::Load {
                            dest: Register(16),
                            ty: IRType::Int,
                            addr: Register(15)
                        },
                        Instr::Ret(IRType::Int, Some(Register(16)))
                    ],
                }],
                env_ty: IRType::Struct(SymbolID::ENV, vec![]),
                env_reg: Register(0)
            }]
        )
    }
}
