use crate::lex::{expect, span, Lex, LexErrorKind, LexResult};
use cfg_if::cfg_if;
use serde::{Serialize, Serializer};
use std::{
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
};

use super::StrType;

cfg_if! {
    if #[cfg(feature = "regex")] {
        mod imp_real;
        pub use self::imp_real::*;
    } else {
        mod imp_stub;
        pub use self::imp_stub::*;
    }
}

impl PartialEq for Regex {
    fn eq(&self, other: &Regex) -> bool {
        self.as_str() == other.as_str()
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
                match Regex::parse_str(&regex_buf, StrType::Escaped) {
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
                                    match Regex::parse_str(
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

#[test]
fn test() {
    let expr = assert_ok!(
        Regex::lex(r#""[a-z"\]]+\d{1,10}\"";"#),
        Regex::parse_str(r#"[a-z"\]]+\d{1,10}""#, StrType::Escaped).unwrap(),
        ";"
    );

    assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

    let expr = assert_ok!(
        Regex::lex(r##"r#"[a-z"\]]+\d{1,10}""#;"##),
        Regex::parse_str(r#"[a-z"\]]+\d{1,10}""#, StrType::Escaped).unwrap(),
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
        Regex::parse_str(
            r#"[\"'\xb4\xe2\x80\x98\xe2\x80\x99`<>]{1,3}"#,
            StrType::Escaped
        )
        .unwrap(),
        ""
    );
}
