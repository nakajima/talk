use talk_rs::{parse_tree::ParseTree, parser::parse, visitor::Visitor};

struct DebugPrinter {}

fn indent(string: &str, spaces: usize) -> String {
    let mut prefix = String::with_capacity(spaces);
    for _ in 0..spaces {
        prefix.push_str("  ");
    }

    string
        .split('\n')
        .map(|line| format!("{}{}", prefix, line))
        .collect::<Vec<String>>()
        .join("\n")
}

impl Visitor<String, usize> for DebugPrinter {
    fn visit_literal_int(&self, literal: &'static str, context: usize, _: &ParseTree) -> String {
        indent(&format!("int: {}", literal), context)
    }

    fn visit_literal_float(&self, literal: &'static str, context: usize, _: &ParseTree) -> String {
        indent(&format!("float: {}", literal), context)
    }

    fn visit_binary_expr(
        &self,
        lhs: &talk_rs::expr::Expr,
        rhs: &talk_rs::expr::Expr,
        op: talk_rs::token_kind::TokenKind,
        context: usize,
        parse_tree: &ParseTree,
    ) -> String {
        format!(
            "{}binop ({})\n{}\n{}",
            "  ".repeat(context),
            op,
            parse_tree.accept(lhs, self, context + 1),
            parse_tree.accept(rhs, self, context + 1)
        )
    }

    fn visit_unary_expr(
        &self,
        rhs: &talk_rs::expr::Expr,
        op: talk_rs::token_kind::TokenKind,
        context: usize,
        parse_tree: &ParseTree,
    ) -> String {
        format!(
            "{}unary ({})\n{}",
            "  ".repeat(context),
            op,
            parse_tree.accept(rhs, self, context + 1)
        )
    }

    fn visit_variable(&self, name: &'static str, context: usize, _: &ParseTree) -> String {
        indent(&format!("${}", name), context)
    }
}

fn main() {
    let code = "(1 + 2) * (-3 / (buzz - fizz))";
    println!("Parsing: {}", code);
    let parse_tree = parse(code).unwrap();
    let mut visitor = DebugPrinter {};

    let context = 0;
    println!(
        "{}",
        parse_tree.accept(parse_tree.root().unwrap(), &mut visitor, context)
    );
}
