use std::{collections::HashMap, path::PathBuf};

use crate::{node_id::NodeID, node_meta::NodeMeta, span::Span};

#[derive(Default, Debug, PartialEq, Eq, Clone)]
pub struct NodeMetaStorage {
    pub path: PathBuf,
    storage: HashMap<NodeID, NodeMeta>,
}

impl From<Span> for (usize, usize) {
    fn from(value: Span) -> Self {
        (value.start as usize, value.end as usize)
    }
}

impl NodeMetaStorage {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            storage: Default::default(),
        }
    }

    pub fn get(&self, id: &NodeID) -> Option<&NodeMeta> {
        self.storage.get(id)
    }

    pub fn merge(&mut self, other: &NodeMetaStorage) {
        self.storage.extend(other.storage.clone());
    }

    pub fn insert(&mut self, id: NodeID, meta: NodeMeta) {
        self.storage.insert(id, meta);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&NodeID, &NodeMeta)> {
        self.storage.iter()
    }
}
