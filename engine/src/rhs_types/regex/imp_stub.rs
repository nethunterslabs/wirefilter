use thiserror::Error;

use crate::rhs_types::bytes::StrType;

/// Dummy regex error.
#[derive(Debug, PartialEq, Error)]
pub enum Error {}

/// Dummy regex wrapper that can only store a pattern
/// but not actually be used for matching.
#[derive(Clone)]
pub struct Regex {
    /// Regex value.
    value: String,
    /// Type of string literal.
    ty: StrType,
}

impl Regex {
    /// Parses a regex from a string.
    pub fn parse_str(s: &str) -> Result<Self, Error> {
        Ok(Regex {
            value: s.to_owned(),
            ty: StrType::Escaped,
        })
    }

    /// Not implemented and will panic if called.
    pub fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }

    /// Returns the original string of this dummy regex wrapper.
    pub fn as_str(&self) -> &str {
        self.value.as_str()
    }
}
