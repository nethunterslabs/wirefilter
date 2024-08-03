//! This crate provides a builder for WireFilter ASTs.
//!
//! The AST builder is a set of functions that allow you to build a WireFilter AST.
//! The builder can then create a `FilterAst` or `SingleValueExprAst` from the AST.
#![warn(missing_docs)]

use thiserror::Error;
use wirefilter::{Type, UnknownFieldError, UnknownFunctionError, UnknownVariableError};

pub mod ast;
pub mod build;

pub use ast::{
    ByteSeparatorBuilder, BytesBuilder, CasePatternValueBuilder, CombiningExprBuilder,
    ComparisonExprBuilder, ComparisonOpExprBuilder, ExplicitIpRangeBuilder, FieldBuilder,
    FieldIndexBuilder, FilterAstBuilder, FunctionBuilder, FunctionCallArgExprBuilder,
    FunctionCallExprBuilder, IndexExprBuilder, IntOpBuilder, IpCidrBuilder, IpRangeBuilder,
    LhsFieldExprBuilder, LogicalExprBuilder, LogicalOpBuilder, OrderingOpBuilder, RegexBuilder,
    RhsValueBuilder, RhsValuesBuilder, SimpleExprBuilder, SingleIndexExprBuilder,
    SingleValueExprAstBuilder, StrTypeBuilder, TypeBuilder, UnaryExprBuilder, UnaryOpBuilder,
    VariableBuilder,
};
pub use build::AstBuilder;

/// Result type for the builder.
pub type Result<T> = std::result::Result<T, BuilderError>;

/// Error type for the builder.
#[derive(Debug, Error)]
pub enum BuilderError {
    /// Error when a field is not found in the scheme.
    #[error("Field not found: {0}")]
    FieldNotFound(#[from] UnknownFieldError),
    /// Error when a function is not found in the scheme.
    #[error("Function not found: {0}")]
    FunctionNotFound(#[from] UnknownFunctionError),
    /// Error when a variable is not found in the scheme.
    #[error("Variable not found: {0}")]
    VariableNotFound(#[from] UnknownVariableError),
    /// Error when parsing a regex.
    #[error("Invalid regex: {0}")]
    InvalidRegex(#[from] regex::Error),
    /// Error when parsing an IP CIDR.
    #[error("Invalid IP CIDR: {0}")]
    InvalidIpCidr(#[from] cidr::errors::NetworkParseError),
    /// Unsupported RhsValue.
    #[error("Unsupported RhsValue: {0:?}")]
    UnsupportedRhsValue(Type),
    /// Unsupported Type.
    #[error("Unsupported Type: {0:?}")]
    UnsupportedType(Type),
    /// Unsupported UnaryExpr.
    #[error("Unsupported UnaryExpr: {0:?}")]
    UnsupportedUnaryExpr(Type),
    /// Unsupported CasePatternValue Type.
    #[error("Unsupported CasePatternValue Type: {0:?}")]
    UnsupportedCasePatternValue(Type),
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::net::{IpAddr, Ipv4Addr};
    use std::process::Command;
    use std::sync::Once;

    use lazy_static::lazy_static;
    use wirefilter::{
        FunctionArgKind, FunctionArgs, LhsValue, OrderedFloat, Scheme, SimpleFunctionDefinition,
        SimpleFunctionImpl, SimpleFunctionParam, State, Type, Variables,
    };

    static INIT: Once = Once::new();

    pub fn initialize() {
        INIT.call_once(|| {
            let output = Command::new("poetry")
                .arg("run")
                .arg("python3")
                .arg("python_ast_builder/generate_tests.py")
                .current_dir("../python-ast-builder")
                .output()
                .expect("Failed to run python script");

            if !output.status.success() {
                panic!(
                    "Python script failed with: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        });
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
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

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.request.headers: Map(Array(Bytes)),
                http.host: Bytes,
                http.request.headers.names: Array(Bytes),
                http.request.headers.values: Array(Bytes),
                http.request.headers.is_empty: Array(Bool),
                http.version: Float,
                ip.addr: Ip,
                ssl: Bool,
                ssl.version: Float,
                tcp.port: Int,
            };

            scheme
                .add_function(
                    "lower".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Complex,
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
                            arg_kind: FunctionArgKind::Complex,
                            val_type: Type::Bytes,
                        }],
                        opt_params: Some(vec![]),
                        return_type: Type::Int,
                        implementation: SimpleFunctionImpl::new(len_function),
                    },
                )
                .unwrap();
            scheme
        };
        static ref VARIABLES: Variables = {
            let mut variables = Variables::new();

            variables.add(
                "in_var".to_string(),
                vec![b"example.com".to_vec(), b"example.org".to_vec()].into(),
            );
            variables.add(
                "has_any_var".to_string(),
                vec![b".com".to_vec(), b".org".to_vec()].into(),
            );
            variables.add(
                "has_all_var".to_string(),
                vec![b"exam".to_vec(), b"ple".to_vec()].into(),
            );
            variables.add(
                "regex_var".to_string(),
                wirefilter::Regex::parse_str(r"^\d{3}$").unwrap().into(),
            );
            variables.add("bool_var".to_string(), true.into());
            variables.add("bytes_var".to_string(), b"example.com".to_vec().into());
            variables.add("bytes_var2".to_string(), b"example.org".to_vec().into());
            variables.add("int_var".to_string(), 80.into());
            variables.add("float_var".to_string(), OrderedFloat(80.0).into());
            variables.add(
                "ip_var".to_string(),
                "127.0.0.1".parse::<IpAddr>().unwrap().into(),
            );

            variables
        };
    }

    fn read_json_ast_file(file_name: &str) -> String {
        std::fs::read_to_string(format!("../python-ast-builder/tests/{}.json", file_name))
            .map_err(|e| {
                format!(
                    "Failed to read json file: ../python-ast-builder/tests/{}.json: {}",
                    file_name, e
                )
            })
            .unwrap()
    }

    fn get_builder_from_json<T>(file_name: &str) -> T
    where
        T: serde::de::DeserializeOwned,
    {
        initialize();

        let json_file = read_json_ast_file(file_name);

        serde_json::from_str(&json_file)
            .map_err(|e| format!("Failed to parse json in test {}: {}", file_name, e))
            .unwrap()
    }

    macro_rules! test_builder {
        ($builder:ident, $file_name:literal, $expected:expr) => {
            let builder: $builder = get_builder_from_json($file_name);

            let ast = builder.clone().build(&SCHEME, &VARIABLES).unwrap();

            assert_eq!(
                ast,
                $expected,
                "Failed test: {} - {}",
                stringify!($builder),
                $file_name
            );

            let builder_from_ast = $builder::parse_ast(ast.clone()).unwrap();

            assert_eq!(
                builder,
                builder_from_ast,
                "Failed test: {} - {}",
                stringify!($builder),
                $file_name
            );
        };
    }

    #[test]
    fn test_str_type_builder() {
        test_builder!(
            StrTypeBuilder,
            "str_type_builder1",
            wirefilter::StrType::Escaped
        );

        test_builder!(
            StrTypeBuilder,
            "str_type_builder2",
            wirefilter::StrType::Raw { hash_count: 3 }
        );
    }

    #[test]
    fn test_byte_separator_builder() {
        test_builder!(
            ByteSeparatorBuilder,
            "byte_separator_builder",
            wirefilter::ByteSeparator::Colon(0)
        );
    }

    #[test]
    fn test_bytes_builder() {
        test_builder!(
            BytesBuilder,
            "bytes_builder1",
            wirefilter::Bytes::Str {
                value: "value".into(),
                ty: wirefilter::StrType::Escaped,
            }
        );

        test_builder!(
            BytesBuilder,
            "bytes_builder2",
            wirefilter::Bytes::Raw {
                value: vec![1, 2, 3].into_boxed_slice(),
                separator: wirefilter::ByteSeparator::Dot(0),
            }
        );
    }

    #[test]
    fn test_field_builder() {
        test_builder!(
            FieldBuilder,
            "field_builder",
            SCHEME.get_field("http.version").unwrap()
        );
    }

    #[test]
    fn test_function_builder() {
        test_builder!(
            FunctionBuilder,
            "function_builder",
            SCHEME.get_function("len").unwrap()
        );
    }

    #[test]
    fn test_variable_builder() {
        test_builder!(
            VariableBuilder,
            "variable_builder",
            wirefilter::Variable::new_with_type(
                "bytes_var".to_owned(),
                wirefilter::VariableType::Bytes
            )
        );
    }

    #[test]
    fn test_type_builder() {
        test_builder!(TypeBuilder, "type_builder1", wirefilter::Type::Bool);

        test_builder!(
            TypeBuilder,
            "type_builder2",
            wirefilter::Type::Array(Box::new(Type::Bytes))
        );
    }

    #[test]
    fn test_ordering_op_builder() {
        test_builder!(
            OrderingOpBuilder,
            "ordering_op_builder",
            wirefilter::OrderingOp::LessThan(0)
        );
    }

    #[test]
    fn test_regex_builder() {
        test_builder!(
            RegexBuilder,
            "regex_builder1",
            wirefilter::Regex::parse_str_with_str_type(r"^\d{3}$", wirefilter::StrType::Escaped)
                .unwrap()
        );

        test_builder!(
            RegexBuilder,
            "regex_builder2",
            wirefilter::Regex::parse_str_with_str_type(
                r"^\d{3}$",
                wirefilter::StrType::Raw { hash_count: 3 }
            )
            .unwrap()
        );
    }

    #[test]
    fn test_unary_op_builder() {
        test_builder!(
            UnaryOpBuilder,
            "unary_op_builder",
            wirefilter::UnaryOp::Not(0)
        );
    }

    #[test]
    fn test_comparison_op_expr_builder() {
        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder1",
            wirefilter::ComparisonOpExpr::IsTrue
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder2",
            wirefilter::ComparisonOpExpr::Ordering {
                op: wirefilter::OrderingOp::LessThan(0),
                rhs: wirefilter::RhsValue::Int(1),
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder3",
            wirefilter::ComparisonOpExpr::Int {
                op: wirefilter::IntOp::BitwiseAnd(0),
                rhs: 1,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder4",
            wirefilter::ComparisonOpExpr::Contains {
                rhs: wirefilter::Bytes::Str {
                    value: "value".into(),
                    ty: wirefilter::StrType::Escaped,
                },
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder5",
            wirefilter::ComparisonOpExpr::Matches {
                rhs: wirefilter::Regex::parse_str_with_str_type(
                    r"^\d{3}$",
                    wirefilter::StrType::Escaped
                )
                .unwrap(),
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder6",
            wirefilter::ComparisonOpExpr::OneOf {
                rhs: wirefilter::RhsValues::Int(vec![
                    wirefilter::IntRange(1..=2),
                    wirefilter::IntRange(3..=4),
                ]),
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder7",
            wirefilter::ComparisonOpExpr::HasAny {
                rhs: wirefilter::RhsValues::Bytes(vec![wirefilter::Bytes::Str {
                    value: "value".into(),
                    ty: wirefilter::StrType::Escaped,
                }]),
                case_insensitive: false,
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder8",
            wirefilter::ComparisonOpExpr::HasAll {
                rhs: wirefilter::RhsValues::Bytes(vec![wirefilter::Bytes::Str {
                    value: "value".into(),
                    ty: wirefilter::StrType::Escaped,
                }]),
                case_insensitive: false,
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder9",
            wirefilter::ComparisonOpExpr::OrderingVariable {
                op: wirefilter::OrderingOp::LessThan(0),
                var: wirefilter::Variable::new_with_type(
                    "int_var".to_owned(),
                    wirefilter::VariableType::Int
                )
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder10",
            wirefilter::ComparisonOpExpr::IntVariable {
                op: wirefilter::IntOp::BitwiseAnd(0),
                var: wirefilter::Variable::new_with_type(
                    "int_var".to_owned(),
                    wirefilter::VariableType::Int
                ),
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder11",
            wirefilter::ComparisonOpExpr::ContainsVariable {
                var: wirefilter::Variable::new_with_type(
                    "bytes_var".to_owned(),
                    wirefilter::VariableType::Bytes
                ),
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder12",
            wirefilter::ComparisonOpExpr::MatchesVariable {
                var: wirefilter::Variable::new_with_type(
                    "regex_var".to_owned(),
                    wirefilter::VariableType::Regex
                ),
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder13",
            wirefilter::ComparisonOpExpr::OneOfVariable {
                var: wirefilter::Variable::new_with_type(
                    "in_var".to_owned(),
                    wirefilter::VariableType::BytesList
                ),
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder14",
            wirefilter::ComparisonOpExpr::HasAnyVariable {
                var: wirefilter::Variable::new_with_type(
                    "has_any_var".to_owned(),
                    wirefilter::VariableType::BytesList
                ),
                case_insensitive: false,
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder15",
            wirefilter::ComparisonOpExpr::HasAllVariable {
                var: wirefilter::Variable::new_with_type(
                    "has_all_var".to_owned(),
                    wirefilter::VariableType::BytesList
                ),
                case_insensitive: false,
                variant: 0,
            }
        );

        test_builder!(
            ComparisonOpExprBuilder,
            "comparison_op_expr_builder16",
            wirefilter::ComparisonOpExpr::Cases(wirefilter::Cases {
                patterns: vec![(
                    vec![
                        wirefilter::CasePatternValue::Float(1.0.into()),
                        wirefilter::CasePatternValue::Bool,
                    ],
                    wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                        wirefilter::ComparisonExpr {
                            lhs: wirefilter::IndexExpr {
                                lhs: wirefilter::LhsFieldExpr::Field(
                                    SCHEME.get_field("http.version").unwrap()
                                ),
                                indexes: Vec::new(),
                            },
                            op: wirefilter::ComparisonOpExpr::Ordering {
                                op: wirefilter::OrderingOp::LessThan(0),
                                rhs: wirefilter::RhsValue::Float(1.0.into()),
                            },
                        }
                    )),
                )],
                variant: 0,
            })
        );
    }

    #[test]
    fn test_unary_expr_builder() {
        test_builder!(
            UnaryExprBuilder,
            "unary_expr_builder",
            wirefilter::SimpleExpr::Unary {
                op: wirefilter::UnaryOp::Not(0),
                arg: Box::new(wirefilter::SimpleExpr::Comparison(
                    wirefilter::ComparisonExpr {
                        lhs: wirefilter::IndexExpr {
                            lhs: wirefilter::LhsFieldExpr::Field(
                                SCHEME.get_field("http.version").unwrap()
                            ),
                            indexes: Vec::new(),
                        },
                        op: wirefilter::ComparisonOpExpr::Ordering {
                            op: wirefilter::OrderingOp::LessThan(0),
                            rhs: wirefilter::RhsValue::Int(1),
                        },
                    }
                ))
            }
        );
    }

    #[test]
    fn test_index_expr_builder() {
        test_builder!(
            IndexExprBuilder,
            "index_expr_builder1",
            wirefilter::IndexExpr {
                lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                indexes: Vec::new(),
            }
        );

        test_builder!(
            IndexExprBuilder,
            "index_expr_builder2",
            wirefilter::IndexExpr {
                lhs: wirefilter::LhsFieldExpr::Field(
                    SCHEME.get_field("http.request.headers").unwrap()
                ),
                indexes: vec![
                    wirefilter::FieldIndex::ArrayIndex(1),
                    wirefilter::FieldIndex::MapKey("key".into()),
                ],
            }
        );
    }

    #[test]
    fn test_lhs_field_expr_builder() {
        test_builder!(
            LhsFieldExprBuilder,
            "lhs_field_expr_builder1",
            wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap())
        );

        test_builder!(
            LhsFieldExprBuilder,
            "lhs_field_expr_builder2",
            wirefilter::LhsFieldExpr::FunctionCallExpr(wirefilter::FunctionCallExpr {
                function: SCHEME.get_function("len").unwrap(),
                return_type: wirefilter::Type::Int,
                args: vec![wirefilter::FunctionCallArgExpr::IndexExpr(
                    wirefilter::IndexExpr {
                        lhs: wirefilter::LhsFieldExpr::Field(
                            SCHEME.get_field("http.host").unwrap()
                        ),
                        indexes: Vec::new(),
                    }
                )],
                context: None,
            })
        );
    }

    #[test]
    fn test_function_call_arg_expr_builder() {
        test_builder!(
            FunctionCallArgExprBuilder,
            "function_call_arg_expr_builder1",
            wirefilter::FunctionCallArgExpr::IndexExpr(wirefilter::IndexExpr {
                lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                indexes: Vec::new(),
            })
        );

        test_builder!(
            FunctionCallArgExprBuilder,
            "function_call_arg_expr_builder2",
            wirefilter::FunctionCallArgExpr::Literal(wirefilter::RhsValue::Int(1))
        );

        test_builder!(
            FunctionCallArgExprBuilder,
            "function_call_arg_expr_builder3",
            wirefilter::FunctionCallArgExpr::Literal(wirefilter::RhsValue::Bytes(
                "value".as_bytes().to_owned().into()
            ))
        );

        test_builder!(
            FunctionCallArgExprBuilder,
            "function_call_arg_expr_builder4",
            wirefilter::FunctionCallArgExpr::Literal(wirefilter::RhsValue::Float(1.0.into()))
        );

        test_builder!(
            FunctionCallArgExprBuilder,
            "function_call_arg_expr_builder5",
            wirefilter::FunctionCallArgExpr::Literal(wirefilter::RhsValue::Ip(
                Ipv4Addr::new(127, 0, 0, 1).into()
            ))
        );

        test_builder!(
            FunctionCallArgExprBuilder,
            "function_call_arg_expr_builder6",
            wirefilter::FunctionCallArgExpr::SimpleExpr(wirefilter::SimpleExpr::Comparison(
                wirefilter::ComparisonExpr {
                    lhs: wirefilter::IndexExpr {
                        lhs: wirefilter::LhsFieldExpr::Field(
                            SCHEME.get_field("http.host").unwrap()
                        ),
                        indexes: Vec::new(),
                    },
                    op: wirefilter::ComparisonOpExpr::Ordering {
                        op: wirefilter::OrderingOp::LessThan(0),
                        rhs: wirefilter::RhsValue::Int(1),
                    },
                }
            ))
        );
    }

    #[test]
    fn test_function_call_expr_builder() {
        test_builder!(
            FunctionCallExprBuilder,
            "function_call_expr_builder",
            wirefilter::FunctionCallExpr {
                function: SCHEME.get_function("len").unwrap(),
                return_type: wirefilter::Type::Int,
                args: vec![wirefilter::FunctionCallArgExpr::IndexExpr(
                    wirefilter::IndexExpr {
                        lhs: wirefilter::LhsFieldExpr::Field(
                            SCHEME.get_field("http.host").unwrap()
                        ),
                        indexes: Vec::new(),
                    }
                )],
                context: None,
            }
        );
    }

    #[test]
    fn test_comparison_expr_builder() {
        test_builder!(
            ComparisonExprBuilder,
            "comparison_expr_builder1",
            wirefilter::ComparisonExpr {
                lhs: wirefilter::IndexExpr {
                    lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                    indexes: Vec::new(),
                },
                op: wirefilter::ComparisonOpExpr::Ordering {
                    op: wirefilter::OrderingOp::LessThan(0),
                    rhs: wirefilter::RhsValue::Int(1),
                },
            }
        );

        test_builder!(
            ComparisonExprBuilder,
            "comparison_expr_builder2",
            wirefilter::ComparisonExpr {
                lhs: wirefilter::IndexExpr {
                    lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                    indexes: Vec::new(),
                },
                op: wirefilter::ComparisonOpExpr::IsTrue,
            }
        );

        test_builder!(
            ComparisonExprBuilder,
            "comparison_expr_builder3",
            wirefilter::ComparisonExpr {
                lhs: wirefilter::IndexExpr {
                    lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                    indexes: Vec::new(),
                },
                op: wirefilter::ComparisonOpExpr::Int {
                    op: wirefilter::IntOp::BitwiseAnd(0),
                    rhs: 1,
                },
            }
        );

        test_builder!(
            ComparisonExprBuilder,
            "comparison_expr_builder4",
            wirefilter::ComparisonExpr {
                lhs: wirefilter::IndexExpr {
                    lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                    indexes: Vec::new(),
                },
                op: wirefilter::ComparisonOpExpr::Contains {
                    rhs: wirefilter::Bytes::Str {
                        value: "value".into(),
                        ty: wirefilter::StrType::Escaped,
                    },
                    variant: 0,
                },
            }
        );

        test_builder!(
            ComparisonExprBuilder,
            "comparison_expr_builder5",
            wirefilter::ComparisonExpr {
                lhs: wirefilter::IndexExpr {
                    lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                    indexes: Vec::new(),
                },
                op: wirefilter::ComparisonOpExpr::Matches {
                    rhs: wirefilter::Regex::parse_str_with_str_type(
                        r"^\d{3}$",
                        wirefilter::StrType::Escaped
                    )
                    .unwrap(),
                    variant: 0,
                },
            }
        );
    }

    #[test]
    fn test_logical_op_builder() {
        test_builder!(
            LogicalOpBuilder,
            "logical_op_builder",
            wirefilter::LogicalOp::And(0)
        );
    }

    #[test]
    fn test_simple_expr_builder() {
        test_builder!(
            SimpleExprBuilder,
            "simple_expr_builder1",
            wirefilter::SimpleExpr::Comparison(wirefilter::ComparisonExpr {
                lhs: wirefilter::IndexExpr {
                    lhs: wirefilter::LhsFieldExpr::Field(SCHEME.get_field("http.version").unwrap()),
                    indexes: Vec::new(),
                },
                op: wirefilter::ComparisonOpExpr::Ordering {
                    op: wirefilter::OrderingOp::LessThan(0),
                    rhs: wirefilter::RhsValue::Int(1),
                },
            })
        );

        test_builder!(
            SimpleExprBuilder,
            "simple_expr_builder2",
            wirefilter::SimpleExpr::Unary {
                op: wirefilter::UnaryOp::Not(0),
                arg: Box::new(wirefilter::SimpleExpr::Comparison(
                    wirefilter::ComparisonExpr {
                        lhs: wirefilter::IndexExpr {
                            lhs: wirefilter::LhsFieldExpr::Field(
                                SCHEME.get_field("http.version").unwrap()
                            ),
                            indexes: Vec::new(),
                        },
                        op: wirefilter::ComparisonOpExpr::Ordering {
                            op: wirefilter::OrderingOp::LessThan(0),
                            rhs: wirefilter::RhsValue::Int(1),
                        },
                    }
                ))
            }
        );
    }

    #[test]
    fn test_combining_expr_builder() {
        test_builder!(
            CombiningExprBuilder,
            "combining_expr_builder",
            wirefilter::LogicalExpr::Combining {
                op: wirefilter::LogicalOp::And(0),
                items: vec![
                    wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                        wirefilter::ComparisonExpr {
                            lhs: wirefilter::IndexExpr {
                                lhs: wirefilter::LhsFieldExpr::Field(
                                    SCHEME.get_field("http.version").unwrap()
                                ),
                                indexes: Vec::new(),
                            },
                            op: wirefilter::ComparisonOpExpr::Ordering {
                                op: wirefilter::OrderingOp::LessThan(0),
                                rhs: wirefilter::RhsValue::Int(1),
                            },
                        }
                    )),
                    wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                        wirefilter::ComparisonExpr {
                            lhs: wirefilter::IndexExpr {
                                lhs: wirefilter::LhsFieldExpr::Field(
                                    SCHEME.get_field("http.version").unwrap()
                                ),
                                indexes: Vec::new(),
                            },
                            op: wirefilter::ComparisonOpExpr::Ordering {
                                op: wirefilter::OrderingOp::LessThan(0),
                                rhs: wirefilter::RhsValue::Int(1),
                            },
                        }
                    )),
                ],
            }
        );
    }

    #[test]
    fn test_logical_expr_builder() {
        test_builder!(
            LogicalExprBuilder,
            "logical_expr_builder1",
            wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                wirefilter::ComparisonExpr {
                    lhs: wirefilter::IndexExpr {
                        lhs: wirefilter::LhsFieldExpr::Field(
                            SCHEME.get_field("http.version").unwrap()
                        ),
                        indexes: Vec::new(),
                    },
                    op: wirefilter::ComparisonOpExpr::Ordering {
                        op: wirefilter::OrderingOp::LessThan(0),
                        rhs: wirefilter::RhsValue::Int(1),
                    },
                }
            ))
        );

        test_builder!(
            LogicalExprBuilder,
            "logical_expr_builder2",
            wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Unary {
                op: wirefilter::UnaryOp::Not(0),
                arg: Box::new(wirefilter::SimpleExpr::Comparison(
                    wirefilter::ComparisonExpr {
                        lhs: wirefilter::IndexExpr {
                            lhs: wirefilter::LhsFieldExpr::Field(
                                SCHEME.get_field("http.version").unwrap()
                            ),
                            indexes: Vec::new(),
                        },
                        op: wirefilter::ComparisonOpExpr::Ordering {
                            op: wirefilter::OrderingOp::LessThan(0),
                            rhs: wirefilter::RhsValue::Int(1),
                        },
                    }
                ))
            })
        );

        test_builder!(
            LogicalExprBuilder,
            "logical_expr_builder3",
            wirefilter::LogicalExpr::Combining {
                op: wirefilter::LogicalOp::And(0),
                items: vec![
                    wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                        wirefilter::ComparisonExpr {
                            lhs: wirefilter::IndexExpr {
                                lhs: wirefilter::LhsFieldExpr::Field(
                                    SCHEME.get_field("http.version").unwrap()
                                ),
                                indexes: Vec::new(),
                            },
                            op: wirefilter::ComparisonOpExpr::Ordering {
                                op: wirefilter::OrderingOp::LessThan(0),
                                rhs: wirefilter::RhsValue::Int(1),
                            },
                        }
                    )),
                    wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                        wirefilter::ComparisonExpr {
                            lhs: wirefilter::IndexExpr {
                                lhs: wirefilter::LhsFieldExpr::Field(
                                    SCHEME.get_field("http.version").unwrap()
                                ),
                                indexes: Vec::new(),
                            },
                            op: wirefilter::ComparisonOpExpr::Ordering {
                                op: wirefilter::OrderingOp::LessThan(0),
                                rhs: wirefilter::RhsValue::Int(1),
                            },
                        }
                    )),
                ],
            }
        );
    }

    #[test]
    fn test_filter_ast_builder() {
        test_builder!(
            FilterAstBuilder,
            "filter_ast_builder",
            wirefilter::FilterAst {
                op: wirefilter::LogicalExpr::Simple(wirefilter::SimpleExpr::Comparison(
                    wirefilter::ComparisonExpr {
                        lhs: wirefilter::IndexExpr {
                            lhs: wirefilter::LhsFieldExpr::Field(
                                SCHEME.get_field("http.version").unwrap()
                            ),
                            indexes: Vec::new(),
                        },
                        op: wirefilter::ComparisonOpExpr::Ordering {
                            op: wirefilter::OrderingOp::LessThan(0),
                            rhs: wirefilter::RhsValue::Int(1),
                        },
                    }
                )),
                scheme: &SCHEME,
            }
        );
    }

    #[test]
    // SingleValueExprAstBuilder
    fn test_single_value_expr_ast_builder() {
        test_builder!(
            SingleValueExprAstBuilder,
            "single_value_expr_ast_builder1",
            wirefilter::SingleValueExprAst {
                op: wirefilter::SingleIndexExpr {
                    op: wirefilter::IndexExpr {
                        lhs: wirefilter::LhsFieldExpr::Field(
                            SCHEME.get_field("http.version").unwrap()
                        ),
                        indexes: Vec::new(),
                    },
                    cases: Some(wirefilter::Cases {
                        patterns: vec![(
                            vec![
                                wirefilter::CasePatternValue::Float(1.0.into()),
                                wirefilter::CasePatternValue::Bool,
                            ],
                            wirefilter::IndexExpr {
                                lhs: wirefilter::LhsFieldExpr::Field(
                                    SCHEME.get_field("ssl.version").unwrap(),
                                ),
                                indexes: Vec::new(),
                            },
                        )],
                        variant: 0,
                    }),
                },
                scheme: &SCHEME,
            }
        );

        test_builder!(
            SingleValueExprAstBuilder,
            "single_value_expr_ast_builder2",
            wirefilter::SingleValueExprAst {
                op: wirefilter::SingleIndexExpr {
                    op: wirefilter::IndexExpr {
                        lhs: wirefilter::LhsFieldExpr::FunctionCallExpr(
                            wirefilter::FunctionCallExpr {
                                function: SCHEME.get_function("len").unwrap(),
                                return_type: wirefilter::Type::Int,
                                args: vec![wirefilter::FunctionCallArgExpr::IndexExpr(
                                    wirefilter::IndexExpr {
                                        lhs: wirefilter::LhsFieldExpr::Field(
                                            SCHEME.get_field("http.host").unwrap()
                                        ),
                                        indexes: Vec::new(),
                                    }
                                )],
                                context: None,
                            }
                        ),
                        indexes: Vec::new(),
                    },
                    cases: None,
                },
                scheme: &SCHEME,
            }
        );
    }

    #[test]
    fn test_int_op_builder() {
        test_builder!(
            IntOpBuilder,
            "int_op_builder",
            wirefilter::IntOp::BitwiseAnd(0)
        );
    }

    #[test]
    fn test_field_index_builder() {
        test_builder!(
            FieldIndexBuilder,
            "field_index_builder1",
            wirefilter::FieldIndex::ArrayIndex(1)
        );

        test_builder!(
            FieldIndexBuilder,
            "field_index_builder2",
            wirefilter::FieldIndex::MapKey("key".into())
        );
    }

    #[test]
    fn test_ip_cidr_builder() {
        test_builder!(
            IpCidrBuilder,
            "ip_cidr_builder",
            cidr::IpCidr::new(Ipv4Addr::new(127, 0, 0, 0).into(), 24).unwrap()
        );
    }

    #[test]
    fn test_explicit_ip_range_builder() {
        test_builder!(
            ExplicitIpRangeBuilder,
            "explicit_ip_range_builder",
            wirefilter::ExplicitIpRange::V4(
                Ipv4Addr::new(127, 0, 0, 1)..=Ipv4Addr::new(127, 0, 0, 255)
            )
        );
    }

    #[test]
    fn test_ip_range_builder() {
        test_builder!(
            IpRangeBuilder,
            "ip_range_builder1",
            wirefilter::IpRange::Explicit(wirefilter::ExplicitIpRange::V4(
                Ipv4Addr::new(127, 0, 0, 1)..=Ipv4Addr::new(127, 0, 0, 255)
            ))
        );

        test_builder!(
            IpRangeBuilder,
            "ip_range_builder2",
            wirefilter::IpRange::Cidr(
                cidr::IpCidr::new(Ipv4Addr::new(127, 0, 0, 0).into(), 24).unwrap()
            )
        );
    }

    #[test]
    fn test_rhs_value_builder() {
        test_builder!(
            RhsValueBuilder,
            "rhs_value_builder1",
            wirefilter::RhsValue::Int(1)
        );

        test_builder!(
            RhsValueBuilder,
            "rhs_value_builder2",
            wirefilter::RhsValue::Bytes("value".as_bytes().to_owned().into())
        );

        test_builder!(
            RhsValueBuilder,
            "rhs_value_builder3",
            wirefilter::RhsValue::Float(1.0.into())
        );

        test_builder!(
            RhsValueBuilder,
            "rhs_value_builder4",
            wirefilter::RhsValue::Ip(Ipv4Addr::new(127, 0, 0, 1).into())
        );
    }

    #[test]
    fn test_rhs_values_builder() {
        test_builder!(
            RhsValuesBuilder,
            "rhs_values_builder1",
            wirefilter::RhsValues::Int(vec![
                wirefilter::IntRange(1..=2),
                wirefilter::IntRange(3..=4),
            ])
        );

        test_builder!(
            RhsValuesBuilder,
            "rhs_values_builder2",
            wirefilter::RhsValues::Float(vec![wirefilter::FloatRange(1.0.into()..=10.0.into())])
        );

        test_builder!(
            RhsValuesBuilder,
            "rhs_values_builder3",
            wirefilter::RhsValues::Ip(vec![wirefilter::IpRange::Cidr(
                cidr::IpCidr::new(Ipv4Addr::new(127, 0, 0, 0).into(), 24).unwrap()
            )])
        );

        test_builder!(
            RhsValuesBuilder,
            "rhs_values_builder4",
            wirefilter::RhsValues::Bytes(vec![wirefilter::Bytes::Str {
                value: "value".into(),
                ty: wirefilter::StrType::Escaped
            }])
        );
    }

    #[test]
    fn test_case_pattern_value_builder() {
        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder1",
            wirefilter::CasePatternValue::Bool
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder2",
            wirefilter::CasePatternValue::Int(1)
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder3",
            wirefilter::CasePatternValue::IntRange(wirefilter::IntRange(1..=2))
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder4",
            wirefilter::CasePatternValue::Float(1.0.into())
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder5",
            wirefilter::CasePatternValue::FloatRange(wirefilter::FloatRange(
                1.0.into()..=2.0.into()
            ))
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder6",
            wirefilter::CasePatternValue::Ip(Ipv4Addr::new(127, 0, 0, 1).into())
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder7",
            wirefilter::CasePatternValue::IpRange(wirefilter::IpRange::Explicit(
                wirefilter::ExplicitIpRange::V4(
                    Ipv4Addr::new(127, 0, 0, 1)..=Ipv4Addr::new(127, 0, 0, 255)
                )
            ))
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder8",
            wirefilter::CasePatternValue::IpRange(wirefilter::IpRange::Cidr(
                cidr::IpCidr::new(Ipv4Addr::new(127, 0, 0, 0).into(), 24).unwrap()
            ))
        );

        test_builder!(
            CasePatternValueBuilder,
            "case_pattern_value_builder9",
            wirefilter::CasePatternValue::Bytes(wirefilter::Bytes::Str {
                value: "value".into(),
                ty: wirefilter::StrType::Escaped
            })
        );
    }
}
