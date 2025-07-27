fn main() {
    use talk::check;
    
    let src = r#"
        let arr = [1, 2, 3]
        arr.get(0)
    "#;
    
    match check(src) {
        Ok(checked) => {
            println!("Success!");
            println!("Diagnostics: {:?}", checked.diagnostics());
            
            // Check Array type
            if let Some(array_symbol) = checked.symbols.find_by_name("Array") {
                println!("Found Array symbol: {:?}", array_symbol);
                if let Some(array_def) = checked.env.lookup_type(array_symbol) {
                    println!("Array members: {:?}", array_def.members.keys().collect::<Vec<_>>());
                    println!("Array row_var: {:?}", array_def.row_var);
                }
            } else {
                println!("Array symbol not found!");
            }
        }
        Err(e) => {
            println!("Error: {:?}", e);
        }
    }
}