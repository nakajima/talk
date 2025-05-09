use talk_rs::{
    parse_tree::ParseTree,
    parser::{NodeID, parse},
    visitor::Visitor,
};

struct DebugPrinter {}

fn indent(string: &str, spaces: &usize) -> String {
    let mut prefix = String::with_capacity(*spaces);
    for _ in 0..*spaces {
        prefix.push_str("  ");
    }

    string
        .split('\n')
        .map(|line| format!("{}{}", prefix, line))
        .collect::<Vec<String>>()
        .join("\n")
}

impl Visitor<String, usize> for DebugPrinter {
    fn visit_literal_int(&self, literal: &'static str, context: &usize, _: &ParseTree) -> String {
        indent(&format!("int: {}", literal), context)
    }

    fn visit_literal_float(&self, literal: &'static str, context: &usize, _: &ParseTree) -> String {
        indent(&format!("float: {}", literal), context)
    }

    fn visit_binary_expr(
        &self,
        lhs: &talk_rs::expr::Expr,
        rhs: &talk_rs::expr::Expr,
        op: talk_rs::token_kind::TokenKind,
        context: &usize,
        parse_tree: &ParseTree,
    ) -> String {
        format!(
            "{}binop ({})\n{}\n{}",
            "  ".repeat(*context),
            op,
            parse_tree.accept(lhs, self, &(context + 1)),
            parse_tree.accept(rhs, self, &(context + 1))
        )
    }

    fn visit_unary_expr(
        &self,
        rhs: &talk_rs::expr::Expr,
        op: talk_rs::token_kind::TokenKind,
        context: &usize,
        parse_tree: &ParseTree,
    ) -> String {
        format!(
            "{}unary ({})\n{}",
            "  ".repeat(*context),
            op,
            parse_tree.accept(rhs, self, &(context + 1))
        )
    }

    fn visit_variable(&self, name: &'static str, context: &usize, _: &ParseTree) -> String {
        indent(&format!("${}", name), context)
    }

    fn visit_tuple(&self, items: Vec<NodeID>, context: &usize, parse_tree: &ParseTree) -> String {
        indent(
            &format!(
                "({:?})",
                items
                    .into_iter()
                    .map(|i| parse_tree.accept(parse_tree.get(i).unwrap(), self, &0))
                    .collect::<Vec<String>>()
            ),
            context,
        )
    }

    fn visit_func(
        &self,
        name: &Option<talk_rs::token::Token>,
        params: NodeID,
        body: NodeID,
        context: &usize,
        parse_tree: &ParseTree,
    ) -> String {
        format!(
            "{}\n{}\n{}",
            indent(&format!("func {:?}", name), context),
            indent(
                &format!(
                    "{:?}",
                    parse_tree.accept(parse_tree.get(params).unwrap(), self, context)
                ),
                &(context + 1)
            ),
            indent(
                &format!(
                    "{:?}",
                    parse_tree.accept(parse_tree.get(body).unwrap(), self, context)
                ),
                &(context + 1)
            )
        )
    }
}

fn main() {
    let code = "
    (1 + 2) * (-3 / (buzz - fizz)) * (1, 2, foo)
    func fizz() {}
    ";

    println!("Parsing: {}", code);

    let parse_tree = parse(code).unwrap();
    let visitor = DebugPrinter {};

    let context = 0;
    for root in parse_tree.visit(&visitor, &context) {
        println!("{}", root);
    }
}
