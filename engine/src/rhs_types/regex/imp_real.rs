pub use regex::Error;

use crate::rhs_types::bytes::StrType;

/// Wrapper around [`regex::bytes::Regex`]
#[derive(Clone)]
pub struct Regex {
    /// Regex value.
    value: regex::bytes::Regex,
    /// Type of string literal.
    pub(crate) ty: StrType,
}

impl Regex {
    /// Parses a regex from a string with a given string type.
    pub fn parse_str_with_str_type(s: &str, ty: StrType) -> Result<Self, Error> {
        ::regex::bytes::RegexBuilder::new(s)
            .unicode(false)
            .build()
            .map(|value| Self { value, ty })
    }

    /// Parses a regex from a string.
    pub fn parse_str(s: &str) -> Result<Self, Error> {
        Self::parse_str_with_str_type(s, StrType::Escaped)
    }

    /// Returns true if and only if the regex matches the string given.
    pub fn is_match(&self, text: &[u8]) -> bool {
        self.value.is_match(text)
    }

    /// Returns the original string of this regex.
    pub fn as_str(&self) -> &str {
        self.value.as_str()
    }

    /// Returns the type of string literal.
    pub fn ty(&self) -> StrType {
        self.ty
    }
}
