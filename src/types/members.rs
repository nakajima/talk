use indexmap::IndexMap;

use crate::label::Label;

#[derive(Clone, PartialEq, Debug)]
pub enum MemberKind {
    Initializer,
    Variant,
    Property,
    InstanceMethod,
    StaticMethod,
    MethodRequirement,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Members<T> {
    pub initializers: IndexMap<Label, T>,
    pub variants: IndexMap<Label, T>,
    pub properties: IndexMap<Label, T>,
    pub methods: IndexMap<Label, T>,
    pub static_methods: IndexMap<Label, T>,
}

impl<T> Members<T> {
    pub fn extend(&mut self, other: Members<T>) {
        self.initializers.extend(other.initializers);
        self.variants.extend(other.variants);
        self.properties.extend(other.properties);
        self.methods.extend(other.methods);
        self.static_methods.extend(other.static_methods);
    }

    pub fn map<U>(self, mut map: impl FnMut(MemberKind, T) -> U) -> Members<U> {
        Members {
            initializers: self
                .initializers
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::Initializer, v)))
                .collect(),
            variants: self
                .variants
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::Variant, v)))
                .collect(),
            properties: self
                .properties
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::Property, v)))
                .collect(),
            methods: self
                .methods
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::InstanceMethod, v)))
                .collect(),
            static_methods: self
                .static_methods
                .into_iter()
                .map(|(l, v)| (l, map(MemberKind::StaticMethod, v)))
                .collect(),
        }
    }
}

impl<T> Default for Members<T> {
    fn default() -> Self {
        Members {
            initializers: Default::default(),
            variants: Default::default(),
            properties: Default::default(),
            methods: Default::default(),
            static_methods: Default::default(),
        }
    }
}
