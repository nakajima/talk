use std::error::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic<E: Error> {
    pub path: String,
    pub location: (u32, u32),
    pub kind: E,
}
