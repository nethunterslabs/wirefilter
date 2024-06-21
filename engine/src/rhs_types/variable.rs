use crate::lex::{expect, Lex, LexErrorKind, LexResult};
use serde::Serialize;
use std::str;

#[derive(PartialEq, Eq, Clone, Serialize, Hash, Debug)]
pub struct VariableName(pub(crate) Box<str>);

impl VariableName {
    pub fn take_inner(self) -> Box<str> {
        self.0
    }
}

impl From<VariableName> for String {
    fn from(src: VariableName) -> Self {
        src.0.into()
    }
}

impl From<String> for VariableName {
    fn from(src: String) -> Self {
        VariableName(src.into_boxed_str())
    }
}

impl<'i> Lex<'i> for VariableName {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let mut res = String::new();
        let mut rest;
        let mut iter;
        let input = expect(input, "$")?;
        iter = input.chars();
        loop {
            rest = iter.as_str();
            match iter.next() {
                Some(c) => {
                    if res.is_empty() {
                        match c {
                            'a'..='z' => res.push(c),
                            _ => {
                                return Err((
                                    LexErrorKind::InvalidVariableName {
                                        name: c.to_string(),
                                    },
                                    input,
                                ));
                            }
                        }
                    } else {
                        match c {
                            'a'..='z' | '0'..='9' | '-' | '_' => res.push(c),
                            _ => {
                                if res.is_empty() {
                                    return Err((
                                        LexErrorKind::InvalidVariableName {
                                            name: c.to_string(),
                                        },
                                        input,
                                    ));
                                } else {
                                    break;
                                }
                            }
                        }
                    }
                }
                None => {
                    if res.is_empty() {
                        return Err((LexErrorKind::InvalidVariableName { name: res }, input));
                    } else {
                        break;
                    }
                }
            }
        }
        Ok((res.into(), rest))
    }
}

impl VariableName {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn valid() {
        assert_ok!(
            VariableName::lex("$hello;"),
            VariableName::from("hello".to_string()),
            ";"
        );

        assert_ok!(
            VariableName::lex("$hello_world;"),
            VariableName::from("hello_world".to_string()),
            ";"
        );

        assert_ok!(
            VariableName::lex("$hello1234567890;"),
            VariableName::from("hello1234567890".to_string()),
            ";"
        );

        assert_ok!(
            VariableName::lex("$hello"),
            VariableName::from("hello".to_string()),
            ""
        );
    }

    #[test]
    fn invalid_leading_char() {
        assert_err!(
            VariableName::lex("$1abc"),
            LexErrorKind::InvalidVariableName {
                name: "1".to_string(),
            },
            "1abc"
        );
    }

    #[test]
    fn invalid_char() {
        assert_err!(
            VariableName::lex("$;"),
            LexErrorKind::InvalidVariableName {
                name: ";".to_string(),
            },
            ";"
        );
    }

    #[test]
    fn eof_after_dollar() {
        assert_err!(
            VariableName::lex("$"),
            LexErrorKind::InvalidVariableName {
                name: "".to_string(),
            },
            ""
        );
    }

    #[test]
    fn no_dollar() {
        assert_err!(
            VariableName::lex("abc"),
            LexErrorKind::ExpectedLiteral("$"),
            "abc"
        );
    }
}
