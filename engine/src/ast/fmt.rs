use super::{FilterAst, SingleValueExprAst};
use thiserror::Error;

/// Error formatting, mismatched AST.
#[derive(Debug, PartialEq, Error)]
#[error("format error")]
pub enum FormatError {
    /// Error formatting, mismatched AST.
    #[error("format error")]
    MismatchedAst,
    /// Parse error.
    #[error("{0}")]
    ParseError(String),
}

impl<'s> SingleValueExprAst<'s> {
    /// Format a [`SingleValueExprAst`] in an opinionated way.
    pub fn fmt(&self) -> Result<String, FormatError> {
        let formatted = self.op.to_string();
        let formatted_ast = self
            .scheme
            .parse_single_value_expr(&formatted)
            .map_err(|e| FormatError::ParseError(e.to_string()))?;
        if self == &formatted_ast {
            Ok(formatted)
        } else {
            Err(FormatError::MismatchedAst)
        }
    }
}

impl<'s> FilterAst<'s> {
    /// Format a [`FilterAst`] in an opinionated way.
    pub fn fmt(&self) -> Result<String, FormatError> {
        let formatted = self.op.fmt(0);
        let formatted_ast = self
            .scheme
            .parse(&formatted)
            .map_err(|e| FormatError::ParseError(e.to_string()))?;
        if self == &formatted_ast {
            Ok(formatted)
        } else {
            Err(FormatError::MismatchedAst)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Array, FunctionArgKind, FunctionArgs, GetType, LhsValue, Scheme, SimpleFunctionDefinition,
        SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam, State, Type,
    };
    use std::convert::TryFrom;

    #[test]
    fn test_fmt() {
        fn any_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            match args.next()? {
                Ok(v) => Some(LhsValue::Bool(
                    Array::try_from(v)
                        .unwrap()
                        .into_iter()
                        .any(|lhs| bool::try_from(lhs).unwrap()),
                )),
                Err(Type::Array(ref arr)) if arr.get_type() == Type::Bool => None,
                _ => unreachable!(),
            }
        }

        fn lower_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            use std::borrow::Cow;

            match args.next()? {
                Ok(LhsValue::Bytes(mut b)) => {
                    let mut text: Vec<u8> = b.to_mut().to_vec();
                    text.make_ascii_lowercase();
                    Some(LhsValue::Bytes(Cow::Owned(text)))
                }
                Err(Type::Bytes) => None,
                _ => unreachable!(),
            }
        }

        fn upper_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            use std::borrow::Cow;

            match args.next()? {
                Ok(LhsValue::Bytes(mut b)) => {
                    let mut text: Vec<u8> = b.to_mut().to_vec();
                    text.make_ascii_uppercase();
                    Some(LhsValue::Bytes(Cow::Owned(text)))
                }
                Err(Type::Bytes) => None,
                _ => unreachable!(),
            }
        }

        fn echo_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            args.next()?.ok()
        }

        fn len_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            match args.next()? {
                Ok(LhsValue::Bytes(bytes)) => {
                    Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap()))
                }
                Err(Type::Bytes) => None,
                _ => unreachable!(),
            }
        }

        let mut scheme = Scheme! {
            http.request.headers: Map(Array(Bytes)),
            http.host: Bytes,
            http.request.headers.names: Array(Bytes),
            http.request.headers.values: Array(Bytes),
            http.request.headers.is_empty: Array(Bool),
            ip.addr: Ip,
            ssl: Bool,
            tcp.port: Int,
        };
        scheme
            .add_function(
                "any".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Array(Box::new(Type::Bool)),
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Bool,
                    implementation: SimpleFunctionImpl::new(any_function),
                },
            )
            .unwrap();
        scheme
            .add_function(
                "echo".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(vec![
                        SimpleFunctionOptParam {
                            arg_kind: FunctionArgKind::Literal,
                            default_value: LhsValue::Int(10),
                        },
                        SimpleFunctionOptParam {
                            arg_kind: FunctionArgKind::Literal,
                            default_value: LhsValue::Int(1),
                        },
                        SimpleFunctionOptParam {
                            arg_kind: FunctionArgKind::Literal,
                            default_value: LhsValue::Bytes(b"test".into()),
                        },
                    ]),
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(echo_function),
                },
            )
            .unwrap();
        scheme
            .add_function(
                "lower".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(lower_function),
                },
            )
            .unwrap();
        scheme
            .add_function(
                "upper".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Any,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(upper_function),
                },
            )
            .unwrap();
        scheme
            .add_function(
                "len".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(len_function),
                },
            )
            .unwrap();

        let ast = scheme
            .parse(r#" http.host  ==   "example.com"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == 65:78:61:6d:70:6c:65:2e:63:6f:6d"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == 65:78:61:6D:70:6C:65:2E:63:6F:6D"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == 65.78.61.6d.70.6c.65.2e.63.6f.6d"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == 65.78.61.6D.70.6C.65.2E.63.6F.6D"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == 65-78-61-6d-70-6c-65-2e-63-6f-6d"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == 65-78-61-6D-70-6C-65-2E-63-6F-6D"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == "example.com" && http.request.headers["content-type"][0] == "application/json""#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com"
&& http.request.headers["content-type"][0] == "application/json""#
                .to_string()),
            "Unable to format logical expression"
        );

        let ast = scheme
            .parse(r#"http.host == r"example.com" && http.request.headers["content-type"][0] == "application/json""#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == r"example.com"
&& http.request.headers["content-type"][0] == "application/json""#
                .to_string()),
            "Unable to format logical expression with raw string"
        );

        let ast = scheme
            .parse(r##"http.host == r#"example.com"# && http.request.headers["content-type"][0] == "application/json""##)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r##"http.host == r#"example.com"#
&& http.request.headers["content-type"][0] == "application/json""##
                .to_string()),
            "Unable to format logical expression with raw string"
        );

        let ast = scheme
            .parse(r#"http.host == "example.com" && lower(http.request.headers["content-type"][0]) == "application/json""#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com"
&& lower(http.request.headers["content-type"][0]) == "application/json""#
                .to_string()),
            "Unable to format logical expression with function"
        );

        let ast = scheme.parse(r#"(http.host == "example.com")"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( http.host == "example.com" )"#.to_string()),
            "Unable to format logical expression in parentheses with function"
        );

        let ast = scheme
            .parse(r#"(http.host == "example.com" && upper(http.request.headers["content-type"][0]) == "APPLICATION/JSON")"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"(
  http.host == "example.com"
  && upper(http.request.headers["content-type"][0]) == "APPLICATION/JSON"
)"#
            .to_string()),
            "Unable to format logical expression in parentheses with function"
        );

        let ast = scheme
            .parse(r#"http.host == "example.com" && len(http.request.headers["content-type"][0]) == 16"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com"
&& len(http.request.headers["content-type"][0]) == 16"#
                .to_string()),
            "Unable to format logical expression with function returning int"
        );

        let ast = scheme
            .parse(r#"((http.host == "example.com") && (echo(http.request.headers["content-type"][0]) == "application/json"))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"(
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0]) == "application/json" )
)"#
            .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0]) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0]) == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && any(http.request.headers["content-type"][*] == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && any(http.request.headers["content-type"][*] == "application/json")
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with map index"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && any((http.request.headers["content-type"][*] == "application/json"))))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && any(( http.request.headers["content-type"][*] == "application/json" ))
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with map index"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0], 100) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100) == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,"teeeeeeest"    ) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, "teeeeeeest") == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,r"teeeeeeest"    ) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, r"teeeeeeest") == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,74:65:65:65:65:65:65:65:73:74    ) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, 74:65:65:65:65:65:65:65:73:74) == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );
    }
}
