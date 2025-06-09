use std::{collections::HashMap, path::PathBuf};

pub type FileID = usize;

pub struct FileStore {
    pub files: Vec<PathBuf>,
    lookup: HashMap<PathBuf, FileID>,
}

impl FileStore {
    pub fn add(&mut self, file: &PathBuf) -> FileID {
        if let Some(existing) = self.lookup.get(file) {
            *existing
        } else {
            let id = self.files.len();
            self.files.push(file.clone());
            self.lookup.insert(file.clone(), id);
            id
        }
    }

    pub fn id(&self, file: &PathBuf) -> FileID {
        *self
            .lookup
            .get(file)
            .unwrap_or_else(|| panic!("File not found: {:?}", file))
    }

    pub fn lookup(&self, id: FileID) -> &PathBuf {
        &self.files[id]
    }
}
