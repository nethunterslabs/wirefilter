use crate::{
    lex::{expect, take, Lex, LexErrorKind, LexResult},
    strict_partial_ord::StrictPartialOrd,
};
use serde::Serialize;
use std::{
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    ops::Deref,
    str,
};

/// Type of string literal.
#[derive(Clone, Copy)]
pub enum StrType {
    /// Raw string literal.
    Raw {
        /// Number of `#` characters in the opening and closing delimiter.
        hash_count: usize,
    },
    /// Escaped string literal.
    Escaped,
}

/// Bytes literal represented either by a string or raw bytes.
#[derive(Clone)]
pub enum Bytes {
    /// String representation of bytes
    Str {
        /// String value.
        value: Box<str>,
        /// Type of string literal.
        ty: StrType,
    },
    /// Raw representation of bytes.
    Raw {
        /// Raw bytes.
        value: Box<[u8]>,
        /// Separator between bytes.
        separator: ByteSeparator,
    },
}

impl Serialize for Bytes {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Bytes::Str { value, .. } => serializer.serialize_str(value),
            Bytes::Raw { value, .. } => serializer.serialize_bytes(value),
        }
    }
}

impl PartialEq for Bytes {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Bytes::Str { value: a, .. }, Bytes::Str { value: b, .. }) => a == b,
            (Bytes::Raw { value: a, .. }, Bytes::Raw { value: b, .. }) => a == b,
            (Bytes::Str { value: a, .. }, Bytes::Raw { value: b, .. }) => {
                a.as_bytes() == b.as_ref()
            }
            (Bytes::Raw { value: a, .. }, Bytes::Str { value: b, .. }) => {
                a.as_ref() == b.as_bytes()
            }
        }
    }
}

impl Eq for Bytes {}

// We need custom `Hash` consistent with `Borrow` invariants.
// We can get away with `Eq` invariant though because we do want
// `Bytes == Bytes` to check enum tags but `Bytes == &[u8]` to ignore them, and
// consistency of the latter is all that matters for `Borrow` consumers.
#[allow(clippy::derived_hash_with_manual_eq)]
impl Hash for Bytes {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (self as &[u8]).hash(h);
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(src: Vec<u8>) -> Self {
        Bytes::Raw {
            value: src.into_boxed_slice(),
            separator: ByteSeparator::Colon(0),
        }
    }
}

impl From<String> for Bytes {
    fn from(src: String) -> Self {
        Bytes::Str {
            value: src.into_boxed_str(),
            ty: StrType::Escaped,
        }
    }
}

impl From<Bytes> for Box<[u8]> {
    fn from(bytes: Bytes) -> Self {
        match bytes {
            Bytes::Str { value, .. } => value.into_boxed_bytes(),
            Bytes::Raw { value, .. } => value,
        }
    }
}

impl From<Bytes> for Vec<u8> {
    fn from(bytes: Bytes) -> Self {
        match bytes {
            Bytes::Str { value, .. } => value.into_boxed_bytes().into_vec(),
            Bytes::Raw { value, .. } => value.into_vec(),
        }
    }
}

impl Bytes {
    /// Converts into a `Box<[u8]>` without copying or allocating.
    pub fn into_boxed_bytes(self) -> Box<[u8]> {
        match self {
            Bytes::Str { value, .. } => value.into_boxed_bytes(),
            Bytes::Raw { value, .. } => value,
        }
    }
}

impl Debug for Bytes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Bytes::Str { value, .. } => Debug::fmt(&value, f),
            Bytes::Raw { value, separator } => {
                for (i, b) in value.iter().cloned().enumerate() {
                    if i != 0 {
                        write!(f, "{}", separator.as_char())?;
                    }
                    write!(f, "{:02X}", b)?;
                }
                Ok(())
            }
        }
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match self {
            Bytes::Str { value, .. } => value.as_bytes(),
            Bytes::Raw { value, .. } => value,
        }
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

fn fixed_byte(input: &str, digits: usize, radix: u32, limit: Option<u8>) -> LexResult<'_, u8> {
    let (digits, rest) = take(input, digits)?;
    match u8::from_str_radix(digits, radix) {
        Ok(b) => {
            if let Some(limit) = limit {
                if b > limit {
                    return Err((LexErrorKind::InvalidCharacterEscape, digits));
                }
            }
            Ok((b, rest))
        }
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, digits)),
    }
}

fn hex_byte(input: &str, ascii_only: bool) -> LexResult<'_, u8> {
    fixed_byte(input, 2, 16, if ascii_only { Some(0x7F) } else { None })
}

fn oct_byte(input: &str) -> LexResult<'_, u8> {
    fixed_byte(input, 3, 8, None)
}

lex_enum!(ByteSeparator {
    ":" => Colon,
    "-" => Dash,
    "." => Dot,
});

impl ByteSeparator {
    pub(crate) fn as_char(&self) -> char {
        match self {
            ByteSeparator::Colon(_) => ':',
            ByteSeparator::Dash(_) => '-',
            ByteSeparator::Dot(_) => '.',
        }
    }
}

impl<'i> Lex<'i> for Bytes {
    fn lex(mut input: &str) -> LexResult<'_, Self> {
        if let Ok(input) = expect(input, "\"") {
            let full_input = input;
            let mut res = String::new();
            let mut iter = input.chars();
            loop {
                match iter
                    .next()
                    .ok_or_else(|| (LexErrorKind::MissingEndingQuote, full_input))?
                {
                    '\\' => {
                        let input = iter.as_str();

                        let c = iter
                            .next()
                            .ok_or_else(|| (LexErrorKind::MissingEndingQuote, full_input))?;

                        res.push(match c {
                            '"' | '\\' => c,
                            'x' => {
                                let (b, input) = hex_byte(iter.as_str(), true)?;
                                iter = input.chars();
                                b as char
                            }
                            '0'..='7' => {
                                let (b, input) = oct_byte(input)?;
                                iter = input.chars();
                                b as char
                            }
                            'n' => '\n',
                            'r' => '\r',
                            't' => '\t',
                            _ => {
                                return Err((
                                    LexErrorKind::InvalidCharacterEscape,
                                    &input[..c.len_utf8()],
                                ));
                            }
                        });
                    }
                    '"' => {
                        return Ok((
                            Self::Str {
                                value: res.into(),
                                ty: StrType::Escaped,
                            },
                            iter.as_str(),
                        ))
                    }
                    c => res.push(c),
                };
            }
        } else if let Ok(mut input) = expect(input, "r") {
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
                            return Ok((
                                Self::Str {
                                    value: raw_string.into_boxed_str(),
                                    ty: StrType::Raw {
                                        hash_count: start_hash_count,
                                    },
                                },
                                rest,
                            ));
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
                return Err((LexErrorKind::MissingStartingQuote, input));
            }
        } else {
            let mut res = Vec::new();
            let mut separator = ByteSeparator::Colon(0);
            loop {
                let (b, rest) = hex_byte(input, false)?;
                res.push(b);
                input = rest;
                if let Ok((bytes_separator, rest)) = ByteSeparator::lex(input) {
                    input = rest;
                    separator = bytes_separator;
                } else {
                    return Ok((
                        Bytes::Raw {
                            value: res.into(),
                            separator,
                        },
                        input,
                    ));
                }
            }
        }
    }
}

impl StrictPartialOrd for [u8] {}

#[test]
fn test() {
    assert_ok!(
        Bytes::lex("01:2e:f3-77.12;"),
        Bytes::from(vec![0x01, 0x2E, 0xF3, 0x77, 0x12]),
        ";"
    );

    assert_ok!(
        Bytes::lex(r#""s\\a\t\r\"r\n\000t""#),
        Bytes::from("s\\a\t\r\"r\n\0t".to_owned())
    );

    assert_err!(
        Bytes::lex("01:4x;"),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("4x", 16).unwrap_err(),
            radix: 16,
        },
        "4x"
    );

    assert_ok!(Bytes::lex("01;"), Bytes::from(vec![0x01]), ";");

    assert_ok!(Bytes::lex("01:2f-34"), Bytes::from(vec![0x01, 0x2F, 0x34]));

    assert_err!(Bytes::lex("\"1"), LexErrorKind::MissingEndingQuote, "1");

    assert_err!(
        Bytes::lex(r#""\a""#),
        LexErrorKind::InvalidCharacterEscape,
        "a"
    );

    assert_err!(
        Bytes::lex(r#""\xff""#),
        LexErrorKind::InvalidCharacterEscape,
        "ff"
    );

    assert_err!(
        Bytes::lex(r#""abcd\"#),
        LexErrorKind::MissingEndingQuote,
        "abcd\\"
    );

    assert_err!(
        Bytes::lex(r#""\01😢""#),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("01😢", 8).unwrap_err(),
            radix: 8,
        },
        "01😢"
    );

    assert_err!(
        Bytes::lex(r#""\x3😢""#),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("3😢", 16).unwrap_err(),
            radix: 16,
        },
        "3😢"
    );

    assert_err!(
        Bytes::lex("12:3😢"),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("3😢", 16).unwrap_err(),
            radix: 16,
        },
        "3😢"
    );

    assert_ok!(Bytes::lex(r#"r"ab""#), Bytes::from("ab".to_owned()));

    assert_ok!(
        Bytes::lex(r##"r#"a"b\x51"#"##),
        Bytes::from("a\"b\\x51".to_owned())
    );

    assert_ok!(
        Bytes::lex(r###"r##"foo #"# bar"##"###),
        Bytes::from("foo #\"# bar".to_owned())
    );

    assert_err!(
        Bytes::lex(r#"r"ab"#),
        LexErrorKind::MissingEndingQuote,
        r#""ab"#
    );

    assert_err!(
        Bytes::lex(r#"r#"ab"#),
        LexErrorKind::MissingEndingQuote,
        r#"#"ab"#
    );

    assert_err!(
        Bytes::lex(r###"r#"ab"##"###),
        LexErrorKind::CountMismatch {
            name: "#",
            actual: 2,
            expected: 1
        },
        r###"#"ab"##"###
    );
}
