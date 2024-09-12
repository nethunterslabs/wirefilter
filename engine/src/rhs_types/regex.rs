use super::StrType;
use crate::{
    lex::{expect, span, Lex, LexErrorKind, LexResult},
    scheme::FieldIndex,
    strict_partial_ord::StrictPartialOrd,
};
pub use regex::{bytes::Captures, Error};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{
    cmp::Ordering,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
};

/// Wrapper around [`regex::bytes::Regex`]
#[derive(Clone)]
pub struct Regex {
    /// Regex value.
    value: regex::bytes::Regex,
    /// Capture Groups
    pub(crate) capture_names: Vec<FieldIndex>,
    /// Type of string literal.
    pub(crate) ty: StrType,
}

impl Regex {
    /// Parses a regex from a string with a given string type.
    pub fn parse_str_with_str_type(s: &str, ty: StrType) -> Result<Self, Error> {
        ::regex::bytes::RegexBuilder::new(s)
            .unicode(false)
            .build()
            .map(|value| {
                let mut capture_names = Vec::new();

                for name in value.capture_names() {
                    if let Some(name) = name {
                        capture_names.push(FieldIndex::MapKey(name.to_string()));
                    } else {
                        capture_names.push(FieldIndex::ArrayIndex(capture_names.len() as u32));
                    }
                }

                Self {
                    value,
                    ty,
                    capture_names,
                }
            })
    }

    /// Parses a regex from a string.
    pub fn parse_str(s: &str) -> Result<Self, Error> {
        Self::parse_str_with_str_type(s, StrType::Escaped)
    }

    /// Returns true if and only if the regex matches the string given.
    pub fn is_match(&self, text: &[u8]) -> bool {
        self.value.is_match(text)
    }

    /// Returns an iterator of all non-overlapping matches of the regex in the text.
    pub fn captures<'h>(&self, haystack: &'h [u8]) -> Option<Captures<'h>> {
        self.value.captures(haystack)
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

impl PartialEq for Regex {
    fn eq(&self, other: &Regex) -> bool {
        self.as_str() == other.as_str()
    }
}

impl PartialOrd for Regex {
    fn partial_cmp(&self, other: &Regex) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl Eq for Regex {}

impl Hash for Regex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl Debug for Regex {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl<'i> Lex<'i> for Regex {
    fn lex(input: &str) -> LexResult<'_, Self> {
        match expect(input, "\"") {
            Ok(input) => {
                let mut regex_buf = String::new();
                let mut in_char_class = false;
                let (regex_str, input) = {
                    let mut iter = input.chars();
                    loop {
                        let before_char = iter.as_str();
                        match iter
                            .next()
                            .ok_or_else(|| (LexErrorKind::MissingEndingQuote, input))?
                        {
                            '\\' => {
                                if let Some(c) = iter.next() {
                                    if in_char_class || c != '"' {
                                        regex_buf.push('\\');
                                    }
                                    regex_buf.push(c);
                                }
                            }
                            '"' if !in_char_class => {
                                break (span(input, before_char), iter.as_str());
                            }
                            '[' if !in_char_class => {
                                in_char_class = true;
                                regex_buf.push('[');
                            }
                            ']' if in_char_class => {
                                in_char_class = false;
                                regex_buf.push(']');
                            }
                            c => {
                                regex_buf.push(c);
                            }
                        };
                    }
                };
                match Regex::parse_str_with_str_type(&regex_buf, StrType::Escaped) {
                    Ok(regex) => Ok((regex, input)),
                    Err(err) => Err((LexErrorKind::ParseRegex(err), regex_str)),
                }
            }
            Err(e) => {
                if let Ok(mut input) = expect(input, "r") {
                    let full_input = input;
                    let mut start_hash_count = 0;
                    while let Ok(new_input) = expect(input, "#") {
                        start_hash_count += 1;

                        if start_hash_count > 255 {
                            return Err((LexErrorKind::TooManyHashes, input));
                        }

                        input = new_input;
                    }

                    if let Ok(mut input) = expect(input, "\"") {
                        let mut raw_string = String::new();
                        loop {
                            if let Ok(mut rest) = expect(input, "\"") {
                                let mut end_hash_count = 0;

                                while let Ok(new_rest) = expect(rest, "#") {
                                    end_hash_count += 1;

                                    if end_hash_count > 255 {
                                        return Err((LexErrorKind::TooManyHashes, rest));
                                    }

                                    rest = new_rest;
                                }

                                #[allow(clippy::comparison_chain)]
                                if end_hash_count == start_hash_count {
                                    match Regex::parse_str_with_str_type(
                                        &raw_string,
                                        StrType::Raw {
                                            hash_count: start_hash_count,
                                        },
                                    ) {
                                        Ok(regex) => return Ok((regex, rest)),
                                        Err(err) => {
                                            return Err((LexErrorKind::ParseRegex(err), full_input))
                                        }
                                    }
                                } else if end_hash_count > start_hash_count {
                                    return Err((
                                        LexErrorKind::CountMismatch {
                                            name: "#",
                                            actual: end_hash_count,
                                            expected: start_hash_count,
                                        },
                                        full_input,
                                    ));
                                } else {
                                    raw_string.push('"');
                                    raw_string.push_str("#".repeat(end_hash_count).as_str());
                                    input = rest;
                                }
                            } else if let Some((c, rest)) =
                                input.chars().next().map(|c| (c, &input[c.len_utf8()..]))
                            {
                                raw_string.push(c);
                                input = rest;
                            } else {
                                return Err((LexErrorKind::MissingEndingQuote, full_input));
                            }
                        }
                    } else {
                        Err((LexErrorKind::MissingStartingQuote, input))
                    }
                } else {
                    Err(e)
                }
            }
        }
    }
}

impl Serialize for Regex {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.as_str().serialize(ser)
    }
}

impl<'de> Deserialize<'de> for Regex {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Self::parse_str(&s).map_err(serde::de::Error::custom)
    }
}

/// [Uninhabited / empty type](https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types)
/// for `Regex` with traits we need for RHS values.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Serialize, Deserialize)]
pub enum UninhabitedRegex {}

impl PartialEq<UninhabitedRegex> for Regex {
    fn eq(&self, other: &UninhabitedRegex) -> bool {
        match *other {}
    }
}

impl PartialOrd<UninhabitedRegex> for Regex {
    fn partial_cmp(&self, other: &UninhabitedRegex) -> Option<Ordering> {
        match *other {}
    }
}

impl StrictPartialOrd<UninhabitedRegex> for Regex {}

impl StrictPartialOrd<UninhabitedRegex> for UninhabitedRegex {}

impl StrictPartialOrd<Regex> for Regex {}

impl<'i> Lex<'i> for UninhabitedRegex {
    fn lex(_input: &str) -> LexResult<'_, Self> {
        unreachable!()
    }
}

#[test]
fn test() {
    let expr = assert_ok!(
        Regex::lex(r#""[a-z"\]]+\d{1,10}\"";"#),
        Regex::parse_str_with_str_type(r#"[a-z"\]]+\d{1,10}""#, StrType::Escaped).unwrap(),
        ";"
    );

    assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

    let expr = assert_ok!(
        Regex::lex(r##"r#"[a-z"\]]+\d{1,10}""#;"##),
        Regex::parse_str_with_str_type(r#"[a-z"\]]+\d{1,10}""#, StrType::Escaped).unwrap(),
        ";"
    );

    assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

    assert_err!(
        Regex::lex(r#""abcd\"#),
        LexErrorKind::MissingEndingQuote,
        "abcd\\"
    );

    assert_ok!(
        Regex::lex(r#""[\"'\xb4\xe2\x80\x98\xe2\x80\x99`<>]{1,3}""#),
        Regex::parse_str_with_str_type(
            r#"[\"'\xb4\xe2\x80\x98\xe2\x80\x99`<>]{1,3}"#,
            StrType::Escaped
        )
        .unwrap(),
        ""
    );
}
