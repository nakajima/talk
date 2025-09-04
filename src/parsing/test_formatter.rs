use talk::parsing::{
    ast::{AST, Parsed},
    formatter::format,
    lexer::Lexer,
    parser::Parser,
    id_generator::IDGenerator,
};

fn parse(code: &str) -> AST<Parsed> {
    let lexer = Lexer::new(code);
    let ids = &mut IDGenerator::default();
    let parser = Parser::new("-", ids, lexer);
    parser.parse().unwrap()
}

fn main() {
    // Test simple literals
    let ast = parse("123");
    println!("Input: 123");
    println!("Output: {}", format(&ast, 80));
    println!();

    // Test simple function
    let ast = parse("func foo() { 123 }");
    println!("Input: func foo() {{ 123 }}");
    println!("Output: {}", format(&ast, 80));
    println!();

    // Test match expression with simpler syntax
    let ast = parse("match x { .some(val) -> { val } .none -> { 0 } }");
    println!("Input: match x {{ .some(val) -> {{ val }} .none -> {{ 0 }} }}");
    println!("Output: {}", format(&ast, 80));
}