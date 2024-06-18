//! This crate provides a builder for WireFilter ASTs.
//!
//! The AST builder is a set of functions that allow you to build a WireFilter AST.
//! The builder can then create a `FilterAst` or `SingleValueExprAst` from the AST.
#![warn(missing_docs)]

use thiserror::Error;
use wirefilter::{UnknownFieldError, UnknownFunctionError};

pub mod ast;
pub mod build;

pub use ast::{
    ByteSeparatorBuilder, BytesBuilder, CombiningExprBuilder, ComparisonExprBuilder,
    ComparisonOpExprBuilder, ExplicitIpRangeBuilder, FieldBuilder, FieldIndexBuilder,
    FilterAstBuilder, FunctionBuilder, FunctionCallArgExprBuilder, FunctionCallExprBuilder,
    IndexExprBuilder, IntOpBuilder, IpCidrBuilder, IpRangeBuilder, LhsFieldExprBuilder,
    LogicalExprBuilder, LogicalOpBuilder, RegexBuilder, RhsValueBuilder, RhsValuesBuilder,
    SimpleExprBuilder, SingleValueExprAstBuilder, StrTypeBuilder, TypeBuilder, UnaryExprBuilder,
    UnaryOpBuilder,
};

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
    /// Error when parsing a regex.
    #[error("Invalid regex: {0}")]
    InvalidRegex(#[from] regex::Error),
    /// Error when parsing an IP CIDR.
    #[error("Invalid IP CIDR: {0}")]
    InvalidIpCidr(#[from] cidr::errors::NetworkParseError),
}
