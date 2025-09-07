#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct IDGenerator {
    last: u32,
}

impl IDGenerator {
    pub fn next_id<T: From<u32>>(&mut self) -> T {
        self.last += 1;
        self.last.into()
    }

    pub fn next_n_ids<T: From<u32>>(&mut self, n: usize) -> Vec<T> {
        let mut result = vec![];
        for _ in 0..n {
            result.push(self.next_id::<T>().into())
        }
        result
    }
}
