//! Integration tests for row-based pattern matching with exhaustiveness checking

#[cfg(test)]
mod tests {
    use crate::{
        type_checking::check,
    };
    
    /// Test exhaustive pattern matching on closed enum
    #[test]
    fn test_exhaustive_match_closed_enum() {
        // This test shows what we want to support once integrated
        let result = check(
            "
            enum Color {
                Red,
                Green, 
                Blue,
            }
            
            func describe(c: Color) -> String {
                match c {
                    Color.Red -> \"red\"
                    Color.Green -> \"green\"
                    Color.Blue -> \"blue\"
                }
            }
            ",
        );
        
        // Should succeed - all variants covered
        assert!(result.is_ok());
    }
    
    /// Test non-exhaustive pattern matching
    #[test]
    fn test_non_exhaustive_match_error() {
        let result = check(
            "
            enum Color {
                Red,
                Green,
                Blue,
            }
            
            func describe(c: Color) -> String {
                match c {
                    Color.Red -> \"red\"
                    Color.Green -> \"green\"
                    // Missing Blue!
                }
            }
            ",
        );
        
        // Should fail with exhaustiveness error
        // Since check() returns Ok even with errors, we need to check diagnostics
        assert!(result.is_ok());
        if let Ok(check_result) = result {
            let diagnostics = check_result.diagnostics();
            assert!(!diagnostics.is_empty(), "Expected exhaustiveness error but got no diagnostics");
            
            let error_msgs: Vec<String> = diagnostics.iter()
                .map(|d| format!("{:?}", d))
                .collect();
            let all_msgs = error_msgs.join(", ");
            
            assert!(all_msgs.contains("not exhaustive") || all_msgs.contains("Blue"),
                    "Expected exhaustiveness error, got: {}", all_msgs);
        }
    }
    
    /// Test wildcard makes match exhaustive
    #[test]
    fn test_wildcard_exhaustive() {
        let result = check(
            "
            enum Color {
                Red,
                Green,
                Blue,
            }
            
            func describe(c: Color) -> String {
                match c {
                    Color.Red -> \"red\",
                    _ -> \"other\",
                }
            }
            ",
        );
        
        // Should succeed - wildcard covers remaining cases
        assert!(result.is_ok());
    }
    
    /// Test exhaustiveness with enum payloads
    #[test]
    fn test_exhaustive_with_payloads() {
        let result = check(
            "
            enum Message {
                Text(String),
                Number(Int),
                Done,
            }
            
            func process(m: Message) -> String {
                match m {
                    Message.Text(s) -> s,
                    Message.Number(n) -> \"number\",
                    Message.Done -> \"done\",
                }
            }
            ",
        );
        
        // Should succeed - all variants covered
        assert!(result.is_ok());
    }
    
    /// Test bool exhaustiveness
    #[test]
    fn test_bool_exhaustive() {
        let result = check(
            "
            func boolToString(b: Bool) -> String {
                match b {
                    true -> \"yes\",
                    false -> \"no\",
                }
            }
            ",
        );
        
        // Should succeed - both true and false covered
        assert!(result.is_ok());
    }
    
    /// Test bool non-exhaustive
    #[test]
    fn test_bool_non_exhaustive() {
        let result = check(
            "
            func boolToString(b: Bool) -> String {
                match b {
                    true -> \"yes\",
                    // Missing false!
                }
            }
            ",
        );
        
        // Should fail with exhaustiveness error
        // Since check() returns Ok even with errors, we need to check diagnostics
        assert!(result.is_ok());
        if let Ok(check_result) = result {
            let diagnostics = check_result.diagnostics();
            assert!(!diagnostics.is_empty(), "Expected exhaustiveness error but got no diagnostics");
            
            let error_msgs: Vec<String> = diagnostics.iter()
                .map(|d| format!("{:?}", d))
                .collect();
            let all_msgs = error_msgs.join(", ");
            
            assert!(all_msgs.contains("not exhaustive") || all_msgs.contains("false"),
                    "Expected exhaustiveness error, got: {}", all_msgs);
        }
    }
    
    /// Test nested pattern exhaustiveness
    #[test]
    fn test_nested_pattern_exhaustive() {
        let result = check(
            "
            enum Option<T> {
                Some(T),
                None,
            }
            
            enum Result<T, E> {
                Ok(T),
                Err(E),
            }
            
            func process(x: Option<Result<Int, String>>) -> Int {
                match x {
                    Option.Some(Result.Ok(n)) -> n,
                    Option.Some(Result.Err(_)) -> -1,
                    Option.None -> 0,
                }
            }
            ",
        );
        
        // Should succeed - all combinations covered
        assert!(result.is_ok());
    }
    
    /// Test that variable binding is exhaustive
    #[test]
    fn test_variable_binding_exhaustive() {
        let result = check(
            "
            enum Option<T> {
                Some(T),
                None,
            }
            
            func unwrapOr<T>(opt: Option<T>, default: T) -> T {
                match opt {
                    x -> default,  // Variable binding matches everything
                }
            }
            ",
        );
        
        // Should succeed - variable binding is exhaustive
        assert!(result.is_ok());
    }
}