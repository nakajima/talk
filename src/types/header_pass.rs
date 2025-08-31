use crate::node_kinds::func::Func;
use derive_visitor::Visitor;

#[derive(Debug, Visitor)]
#[visitor(Func(enter))]
pub struct HeaderPass {}

impl HeaderPass {
    fn enter_func(&mut self, func: &Func) {}
}

#[cfg(test)]
mod tests {
    use crate::name_resolution::name_resolver_tests::tests::resolve;

    #[test]
    fn types_func_sig() {
        let resolved = resolve(
            "
        func fizz() -> Int {
            123
        }
        ",
        );
    }
}
