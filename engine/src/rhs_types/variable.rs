use crate::{
    lex::{expect, Lex, LexErrorKind, LexResult},
    types::{Type, VariableType},
};
use serde::Serialize;
use std::str;

/// Represents a variable in the filter expression.
#[derive(PartialEq, Eq, Clone, Serialize, Hash, Debug)]
pub struct Variable {
    pub(crate) name: Box<str>,
    pub(crate) ty: Option<VariableType>,
}

impl Variable {
    /// Creates a new variable with the given name.
    pub fn new(name: String) -> Self {
        Self {
            name: name.into_boxed_str(),
            ty: None,
        }
    }

    /// Creates a new variable with the given name and type.
    pub fn new_with_type(name: String, ty: VariableType) -> Self {
        Self {
            name: name.into_boxed_str(),
            ty: Some(ty),
        }
    }

    /// Takes the inner string of the variable.
    pub fn take_name(self) -> Box<str> {
        self.name
    }

    /// Returns the name of the variable.
    pub fn name_as_str(&self) -> &str {
        &self.name
    }

    /// Sets the type of the variable.
    pub fn set_type(&mut self, ty: VariableType) {
        self.ty = Some(ty);
    }

    /// Returns the type of the variable.
    pub fn get_variable_type(&self) -> Option<VariableType> {
        self.ty
    }

    /// Returns the type of the variable.
    pub fn get_type(&self) -> Option<Type> {
        if let Some(ty) = self.ty {
            ty.get_type()
        } else {
            None
        }
    }
}

impl From<Variable> for String {
    fn from(src: Variable) -> Self {
        src.name.into()
    }
}

impl<'i> Lex<'i> for Variable {
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
        Ok((Variable::new(res), rest))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn valid() {
        assert_ok!(
            Variable::lex("$hello;"),
            Variable::new("hello".to_string()),
            ";"
        );

        assert_ok!(
            Variable::lex("$hello_world;"),
            Variable::new("hello_world".to_string()),
            ";"
        );

        assert_ok!(
            Variable::lex("$hello1234567890;"),
            Variable::new("hello1234567890".to_string()),
            ";"
        );

        assert_ok!(
            Variable::lex("$hello"),
            Variable::new("hello".to_string()),
            ""
        );
    }

    #[test]
    fn invalid_leading_char() {
        assert_err!(
            Variable::lex("$1abc"),
            LexErrorKind::InvalidVariableName {
                name: "1".to_string(),
            },
            "1abc"
        );
    }

    #[test]
    fn invalid_char() {
        assert_err!(
            Variable::lex("$;"),
            LexErrorKind::InvalidVariableName {
                name: ";".to_string(),
            },
            ";"
        );
    }

    #[test]
    fn eof_after_dollar() {
        assert_err!(
            Variable::lex("$"),
            LexErrorKind::InvalidVariableName {
                name: "".to_string(),
            },
            ""
        );
    }

    #[test]
    fn no_dollar() {
        assert_err!(
            Variable::lex("abc"),
            LexErrorKind::ExpectedLiteral("$"),
            "abc"
        );
    }
}
