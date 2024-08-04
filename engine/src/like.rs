use std::cmp::Ordering;

use serde::{Deserialize, Serialize};
use wildmatch::WildMatch;

use crate::{
    lex::{Lex, LexResult, LexWith},
    rhs_types::{Bytes, StrType},
    strict_partial_ord::StrictPartialOrd,
};

/// A like pattern. This is a wrapper around a `WildMatch` pattern.
/// It is used to match strings against a pattern with wildcards (`*` and `?`)
/// and optionally case insensitively.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Like {
    matcher: WildMatch,
    /// Type of string literal.
    #[serde(skip, default = "default_str_type")]
    pub(crate) ty: StrType,
}

impl Like {
    /// Parses a like pattern from a string with a given string type.
    pub fn parse_str_with_str_type(s: &str, ty: StrType) -> Self {
        Self {
            matcher: WildMatch::new(s),
            ty,
        }
    }

    /// Parses a case-insensitive like pattern from a string with a given string type.
    pub fn parse_str_with_str_type_case_insensitive(s: &str, ty: StrType) -> Self {
        Self {
            matcher: WildMatch::new_case_insensitive(s),
            ty,
        }
    }

    /// Parses a like pattern from a string.
    pub fn parse_str(s: &str) -> Self {
        Self::parse_str_with_str_type(s, StrType::Escaped)
    }

    /// Parses a case-insensitive like pattern from a string.
    pub fn parse_str_case_insensitive(s: &str) -> Self {
        Self::parse_str_with_str_type_case_insensitive(s, StrType::Escaped)
    }

    /// Returns true if and only if the like pattern matches the string given.
    pub fn is_match(&self, text: &[u8]) -> bool {
        match std::str::from_utf8(text) {
            Ok(text) => self.matcher.matches(text),
            Err(_) => false,
        }
    }

    /// Returns the original string of this like pattern.
    pub fn pattern(&self) -> String {
        self.matcher.pattern()
    }

    /// Returns if the like pattern is case insensitive.
    pub fn is_case_insensitive(&self) -> bool {
        self.matcher.is_case_insensitive()
    }

    /// Returns the type of string literal.
    pub fn ty(&self) -> StrType {
        self.ty
    }
}

impl Eq for Like {}

impl PartialOrd for Like {
    fn partial_cmp(&self, other: &Like) -> Option<std::cmp::Ordering> {
        self.matcher.partial_cmp(&other.matcher)
    }
}

impl std::hash::Hash for Like {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.matcher.pattern().hash(state);
    }
}

impl<'i> LexWith<'i, bool> for Like {
    fn lex_with(input: &str, case_insensitive: bool) -> LexResult<'_, Self> {
        let (bytes, rest) = Bytes::lex_with(input, false)?;
        let (pattern, ty) = if let Bytes::Str { value, ty } = bytes {
            (value, ty)
        } else {
            unreachable!()
        };

        Ok((
            if case_insensitive {
                Self::parse_str_with_str_type_case_insensitive(pattern.as_ref(), ty)
            } else {
                Self::parse_str_with_str_type(pattern.as_ref(), ty)
            },
            rest,
        ))
    }
}

fn default_str_type() -> StrType {
    StrType::Escaped
}

/// [Uninhabited / empty type](https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types)
/// for `Like` with traits we need for RHS values.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Serialize, Deserialize)]
pub enum UninhabitedLike {}

impl PartialEq<UninhabitedLike> for Like {
    fn eq(&self, other: &UninhabitedLike) -> bool {
        match *other {}
    }
}

impl PartialOrd<UninhabitedLike> for Like {
    fn partial_cmp(&self, other: &UninhabitedLike) -> Option<Ordering> {
        match *other {}
    }
}

impl StrictPartialOrd<UninhabitedLike> for Like {}

impl StrictPartialOrd<UninhabitedLike> for UninhabitedLike {}

impl StrictPartialOrd<Like> for Like {}

impl<'i> Lex<'i> for UninhabitedLike {
    fn lex(_input: &str) -> LexResult<'_, Self> {
        unreachable!()
    }
}
