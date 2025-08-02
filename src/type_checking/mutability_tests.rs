#[cfg(test)]
mod tests {
    use crate::check;

    #[test]
    fn test_immutable_variable_assignment_fails() {
        let result = check(
            r#"
            let foo = "hello"
            foo = "world"
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_mutable_variable_assignment_succeeds() {
        let result = check(
            r#"
            let mut bar = "hello"
            bar = "world"
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_immutable_struct_field_assignment_fails() {
        let result = check(
            r#"
            struct Person {
                let age: Int
                let bday: Int
            }

            let person = Person(age: 123, bday: 12345678)
            person.bday = 456
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_mutable_struct_field_assignment_succeeds() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int
                let bday: Int
            }

            let mut person = Person(age: 123, bday: 12345678)
            person.age = 456
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_immutable_struct_field_assignment_fails_even_with_mut_var() {
        let result = check(
            r#"
            struct Person {
                let age: Int
                let bday: Int
            }

            let mut person = Person(age: 123, bday: 12345678)
            person.age = 456
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_struct_init_can_set_immutable_fields() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int
                let bday: Int

                init(age: Int, bday: Int) {
                    self.age = age
                    self.bday = bday
                }
            }

            Person(age: 123, bday: 12345678)
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_non_mut_method_cannot_assign_to_mutable_field() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int
                let bday: Int

                func changeAgeNope(newAge: Int) {
                    self.age = newAge
                }
            }
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_mut_method_can_assign_to_mutable_field() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int
                let bday: Int

                mut func changeAge(newAge: Int) {
                    self.age = newAge
                }
            }
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_mut_method_cannot_assign_to_immutable_field() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int
                let bday: Int

                mut func changeBdayNope(newBday: Int) {
                    self.bday = newBday
                }
            }
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_mutable_parameter_requirement() {
        let result = check(
            r#"
            func increment(mut x: Int) {
                x = x + 1
            }

            let mut y = 123
            increment(x: y)
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_immutable_parameter_fails_with_mutation() {
        let result = check(
            r#"
            func increment(mut x: Int) {
                x = x + 1
            }

            let z = 123
            increment(x: z)
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_method_call_on_immutable_receiver() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int

                mut func changeAge(newAge: Int) {
                    self.age = newAge
                }
            }

            let person = Person(age: 123)
            person.changeAge(newAge: 456)
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_method_call_on_mutable_receiver() {
        let result = check(
            r#"
            struct Person {
                let mut age: Int

                mut func changeAge(newAge: Int) {
                    self.age = newAge
                }
            }

            let mut person = Person(age: 123)
            person.changeAge(newAge: 456)
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_non_mut_method_on_immutable_receiver() {
        let result = check(
            r#"
            struct Person {
                let age: Int

                func getAge() -> Int {
                    self.age
                }
            }

            let person = Person(age: 123)
            person.getAge()
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_array_mutability() {
        let result = check(
            r#"
            let mut arr = [1, 2, 3]
            arr[0] = 5
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_immutable_array_index_assignment_fails() {
        let result = check(
            r#"
            let arr = [1, 2, 3]
            arr[0] = 5
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }

    #[test]
    fn test_nested_mutability() {
        let result = check(
            r#"
            struct Inner {
                let mut value: Int
            }

            struct Outer {
                let mut inner: Inner
            }

            let mut outer = Outer(inner: Inner(value: 42))
            outer.inner.value = 100
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(checked.diagnostics().is_empty());
    }

    #[test]
    fn test_nested_immutability_blocks_mutation() {
        let result = check(
            r#"
            struct Inner {
                let mut value: Int
            }

            struct Outer {
                let inner: Inner  // inner is immutable
            }

            let mut outer = Outer(inner: Inner(value: 42))
            outer.inner.value = 100
            "#,
        );

        assert!(result.is_ok());
        let checked = result.unwrap();
        assert!(!checked.diagnostics().is_empty());
    }
}
