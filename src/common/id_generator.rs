#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct IDGenerator {
    last: u32,
}

impl IDGenerator {
    pub fn next_id<T: From<u32>>(&mut self) -> T {
        self.last += 1;
        self.last.into()
    }
}
