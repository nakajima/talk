#[cfg(test)]
mod tests {
    use crate::type_checking::check;

    #[test]
    fn test_improved_member_access_error() {
        let code = r#"
            let x = 42
            x.foo
        "#;
        
        let result = check(code);
        assert!(result.is_ok());
        
        let check_result = result.unwrap();
        let diagnostics = check_result.diagnostics();
        
        // Should have one error for member access on Int
        assert_eq!(diagnostics.len(), 1);
        
        // Check that the error message is informative
        let error_msg = diagnostics[0].message();
        assert!(error_msg.contains("Cannot find member"));
        assert!(error_msg.contains("foo"));
        assert!(error_msg.contains("Int"));
    }

    #[test]
    fn test_unification_failed_error() {
        let code = r#"
            func foo[T]() -> T { 42 }
            let x: String = foo()
        "#;
        
        let result = check(code);
        assert!(result.is_ok());
        
        let check_result = result.unwrap();
        let diagnostics = check_result.diagnostics();
        
        // Should have type mismatch error
        assert!(!diagnostics.is_empty());
        
        // Check for improved error message
        let error_msg = diagnostics[0].message();
        println!("Error message: {}", error_msg);
    }

    #[test]
    fn test_row_constraint_error() {
        let code = r#"
            func take_record(r: { x: Int, y: String }) -> Int { r.x }
            let obj = { x: 10 }
            take_record(obj)
        "#;
        
        let result = check(code);
        assert!(result.is_ok());
        
        let check_result = result.unwrap();
        let diagnostics = check_result.diagnostics();
        
        // Should have row constraint error for missing field
        assert!(!diagnostics.is_empty());
        
        let error_msg = diagnostics[0].message();
        println!("Row constraint error: {}", error_msg);
    }
}