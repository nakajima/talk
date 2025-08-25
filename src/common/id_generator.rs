#[derive(Default, Debug, Clone)]
pub struct IDGenerator {
    last: i32,
}

impl IDGenerator {
    pub fn next_id(&mut self) -> i32 {
        self.last += 1;
        self.last
    }
}
