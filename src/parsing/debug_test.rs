use talk::parsing::{
    ast::Parsed,
    lexer::Lexer,
    parser::Parser,
    id_generator::IDGenerator,
};

fn main() {
    let code = "func foo() {1+1 2+2}()";
    let lexer = Lexer::new(code);
    let ids = &mut IDGenerator::default();
    let parser = Parser::new("-", ids, lexer);
    let ast = parser.parse().unwrap();
    
    println!("Number of roots: {}", ast.roots.len());
    for (i, root) in ast.roots.iter().enumerate() {
        println!("Root {}: {:?}", i, root);
        if let Some(meta) = ast.meta.get(&match root {
            talk::parsing::node::Node::Expr(e) => e.id.clone(),
            talk::parsing::node::Node::Decl(d) => d.id.clone(),
            _ => panic!("unexpected node type")
        }) {
            println!("  Line: {}", meta.start.line);
        }
    }
}