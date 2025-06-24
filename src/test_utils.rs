#[macro_export]
macro_rules! assert_match_capture {
    ($expr:expr, $pattern:pat, $capture_block:block) => {{
        let value = $expr;
        match value {
            $pattern => $capture_block,
            _ => panic!(
                "assertion failed: value `{:?}` did not match pattern `{}`",
                value,
                stringify!($pattern)
            ),
        }
    }};
}

#[macro_export]
macro_rules! assert_lowered_functions {
    ($left:expr, $right:expr $(,)?) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                use $crate::lowering::ir_module::IRModule;

                if !right_val.iter().all(|f| left_val.functions.contains(f)) {
                    let right_program = IRModule {
                        functions: right_val.clone(),
                    };

                    use crate::lowering::ir_printer::print;
                    use prettydiff::{diff_chars, diff_lines};
                    println!(
                        "{}",
                        diff_chars(
                            &format!("{:?}", &left_val.functions),
                            &format!("{:?}", right_val)
                        )
                    );

                    panic!(
                        "{}\n{}",
                        diff_lines("Actual", "Expected"),
                        diff_lines(print(left_val).as_ref(), print(&right_program).as_ref())
                    )
                }
            }
        }
    };
}

// Check that two functions are the same. Ignores debug info.
#[macro_export]
macro_rules! assert_lowered_function {
    ($module:expr, $function_name:expr, $expected_function:expr $(,)?) => {
        match (&$module, &$function_name, $expected_function) {
            (module, function_name, expected_function) => {
                let function = module
                    .functions
                    .iter()
                    .find(|f| &f.name == function_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "did not find function in compiled ir: {} in {:?}",
                            function_name,
                            module
                                .functions
                                .iter()
                                .map(|f| f.name.clone())
                                .collect::<Vec<String>>()
                        )
                    });

                let mut function = function.clone();
                let mut expected_function = expected_function.clone();
                function.debug_info = Default::default();
                expected_function.debug_info = Default::default();

                if function != expected_function {
                    use prettydiff::{diff_chars, diff_lines};
                    use $crate::lowering::ir_printer::format_func;
                    println!(
                        "{}",
                        diff_chars(
                            &format!("{:?}", &function),
                            &format!("{:?}", expected_function)
                        )
                    );

                    panic!(
                        "{}\n{}",
                        diff_lines("Actual", "Expected"),
                        diff_lines(
                            format_func(&function).as_ref(),
                            format_func(&expected_function).as_ref()
                        )
                    )
                }
            }
        }
    };
}
