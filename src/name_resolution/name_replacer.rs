use crate::{name::Name, name_resolution::symbol::Symbol, node::NodeType, traversal::fold::Fold};

#[derive(Debug)]
pub struct NameReplacer {
    name: String,
    symbol: Symbol,
}

impl NameReplacer {
    pub fn replace<T: NodeType>(name: String, symbol: Symbol, node: T) -> T {
        let mut replacer = Self { name, symbol };
        replacer.fold_node(node.into()).into()
    }
}

impl Fold for NameReplacer {
    fn fold_name(&mut self, name: Name) -> Name {
        println!("fold_name: {name:?}");
        if name == Name::Raw(self.name.clone()) {
            Name::Resolved(self.symbol, name.name_str())
        } else {
            name
        }
    }
}
