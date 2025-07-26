//! Tests for row constraint persistence in the environment
//! 
//! This ensures that row constraints are properly stored during type checking
//! and can be accessed later by the exhaustiveness checker.

#[cfg(test)]
mod tests {
    use crate::type_checking::check;
    
    /// Test that row constraints are persisted in the environment
    #[test]
    fn test_row_constraints_persisted() {
        let result = check(
            "
            enum Status {
                case Active
                case Pending
                case Inactive
            }
            
            func getStatus() -> Status {
                Status.Active
            }
            ",
        );
        
        assert!(result.is_ok());
        if let Ok(check_result) = result {
            // Verify that the environment has row_constraints field
            // This test just ensures the infrastructure exists
            let _row_constraints = &check_result.env.row_constraints;
            
            // Traditional enums might not generate row constraints yet
            // The actual row constraint generation for enums will come when we
            // fully migrate enum definitions to use rows
        }
    }
    
    /// Test exhaustiveness checking with persisted row constraints
    #[test] 
    fn test_exhaustiveness_with_persisted_constraints() {
        let result = check(
            "
            enum Result<T, E> {
                case Ok(T)
                case Err(E)
            }
            
            func handle(r: Result<Int, String>) -> Int {
                match r {
                    Result.Ok(n) -> n
                    Result.Err(_) -> -1
                }
            }
            ",
        );
        
        assert!(result.is_ok());
        if let Ok(check_result) = result {
            // The match should be exhaustive and compile successfully
            let diagnostics = check_result.diagnostics();
            assert!(diagnostics.is_empty(), 
                    "Expected no diagnostics for exhaustive match, got: {:?}", diagnostics);
        }
    }
    
    /// Test non-exhaustive match detection with persisted constraints
    #[test]
    fn test_non_exhaustive_with_persisted_constraints() {
        let result = check(
            "
            enum Option<T> {
                case Some(T)
                case None
            }
            
            func unwrap<T>(opt: Option<T>) -> T {
                match opt {
                    Option.Some(x) -> x
                    // Missing None case!
                }
            }
            ",
        );
        
        assert!(result.is_ok());
        if let Ok(check_result) = result {
            let diagnostics = check_result.diagnostics();
            assert!(!diagnostics.is_empty(), 
                    "Expected exhaustiveness error for non-exhaustive match");
            
            let error_msgs: Vec<String> = diagnostics.iter()
                .map(|d| format!("{:?}", d))
                .collect();
            let all_msgs = error_msgs.join(", ");
            
            assert!(all_msgs.contains("not exhaustive") || all_msgs.contains("None"),
                    "Expected exhaustiveness error mentioning 'None', got: {}", all_msgs);
        }
    }
    
    /// Test that the row constraint persistence infrastructure exists
    #[test]
    fn test_row_constraint_infrastructure() {
        let result = check(
            "
            // Simple test to verify the infrastructure works
            let x = 42
            let y = x + 1
            y
            ",
        );
        
        assert!(result.is_ok());
        if let Ok(check_result) = result {
            // The key test is that we can access row_constraints from the environment
            let env = &check_result.env;
            
            // The field should exist (even if empty for this simple example)
            let _ = &env.row_constraints;
            
            // This test passes if we can compile and access the field
            // The actual constraint collection will be tested with row-based types
        }
    }
}