#[derive(Default, Debug, Clone)]
pub struct IDGenerator {
    last: u32,
}

impl IDGenerator {
    pub fn next_id(&mut self) -> u32 {
        self.last += 1;
        self.last
    }
}
