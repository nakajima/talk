use std::{collections::HashMap, hash::DefaultHasher, path::PathBuf};

pub type FileID = usize;

#[derive(Clone)]
pub struct FileStore {
    pub files: HashMap<FileID, PathBuf>,
    lookup: HashMap<PathBuf, FileID>,
}

impl FileStore {
    pub fn new(files: Vec<PathBuf>) -> Self {
        let mut store = Self {
            files: Default::default(),
            lookup: Default::default(),
        };

        for file in files {
            store.add(&file);
        }

        store
    }

    pub fn add(&mut self, file: &PathBuf) -> FileID {
        if let Some(existing) = self.lookup.get(file) {
            *existing
        } else {
            let id = calculate_hash(file);
            self.files.insert(id, file.clone());
            self.lookup.insert(file.clone(), id);
            id
        }
    }

    pub fn id(&self, file: &PathBuf) -> Option<FileID> {
        self.lookup.get(file).cloned()
    }

    pub fn lookup(&self, id: &FileID) -> Option<&PathBuf> {
        self.files.get(id)
    }
}

use std::hash::Hasher;
fn calculate_hash<T: std::hash::Hash>(t: &T) -> usize {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish() as usize
}
