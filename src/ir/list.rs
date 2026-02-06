use std::str::FromStr;

use crate::ir::ir_error::IRError;

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(bound(
    serialize = "T: serde::Serialize",
    deserialize = "T: serde::de::DeserializeOwned"
))]
pub struct List<T: std::fmt::Debug + Clone + PartialEq + FromStr> {
    pub items: Vec<T>,
}

impl<T: std::fmt::Debug + Clone + PartialEq + FromStr> Default for List<T> {
    fn default() -> Self {
        List {
            items: Default::default(),
        }
    }
}

impl<T: std::fmt::Debug + Clone + PartialEq + FromStr> From<Vec<T>> for List<T> {
    fn from(value: Vec<T>) -> Self {
        List { items: value }
    }
}

impl<T> FromStr for List<T>
where
    T: std::fmt::Debug + Clone + PartialEq + FromStr,
    <T as FromStr>::Err: std::fmt::Display,
{
    type Err = IRError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Trim and strip optional wrappers
        let s = s.trim();
        if s.is_empty() {
            return Ok(List { items: Vec::new() });
        }
        let s = s
            .trim_start_matches(['[', '(', '{'])
            .trim_end_matches([']', ')', '}']);

        let mut items = Vec::new();
        for tok in s
            .split(|c: char| c == ',' || c == ';' || c.is_whitespace())
            .filter(|t| !t.is_empty())
        {
            items.push(tok.parse::<T>().map_err(|e| {
                IRError::CouldNotParse(format!("failed to parse list item `{tok}`: {e}"))
            })?);
        }
        Ok(List { items })
    }
}

impl<T> std::fmt::Display for List<T>
where
    T: std::fmt::Debug + Clone + PartialEq + FromStr + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parts = self
            .items
            .iter()
            .map(|i| format!("{i}"))
            .collect::<Vec<_>>();
        write!(f, "({})", parts.join(", "))
    }
}
