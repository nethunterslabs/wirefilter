//! AST Builders for WireFilter.

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use serde::{Deserialize, Serialize};

/// Builder for `FilterAst`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct FilterAstBuilder {
    pub(crate) op: LogicalExprBuilder,
}

/// Builder for `SingleValueExprAst`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct SingleValueExprAstBuilder {
    pub(crate) op: LhsFieldExprBuilder,
}

/// Builder for `LogicalExprAst`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum LogicalExprBuilder {
    /// Sub-expression
    Simple(SimpleExprBuilder),
    /// Logical conjunction expression
    Combining(CombiningExprBuilder),
}

/// Builder for `CombiningExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct CombiningExprBuilder {
    /// Logical operator
    pub(crate) op: LogicalOpBuilder,
    /// List of sub-expressions
    pub(crate) items: Vec<LogicalExprBuilder>,
}

/// Builder for `LogicalOp`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum LogicalOpBuilder {
    /// Logical OR
    Or,
    /// Logical XOR
    Xor,
    /// Logical AND
    And,
}

/// Builder for `SimpleExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum SimpleExprBuilder {
    /// A comparison expression.
    Comparison(ComparisonExprBuilder),
    /// A parenthisized expression.
    Parenthesized(Box<LogicalExprBuilder>),
    /// A unary expression.
    Unary(UnaryExprBuilder),
}

/// Builder for `UnaryExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct UnaryExprBuilder {
    /// Unary operator.
    pub(crate) op: UnaryOpBuilder,
    /// Sub-expression.
    pub(crate) arg: Box<SimpleExprBuilder>,
}

/// Builder for `UnaryOp`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum UnaryOpBuilder {
    /// Logical NOT
    Not,
}

/// Builder for `ComparisonExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct ComparisonExprBuilder {
    pub(crate) lhs: IndexExprBuilder,
    pub(crate) op: ComparisonOpExprBuilder,
}

/// Builder for `ComparisonOpExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum ComparisonOpExprBuilder {
    /// Boolean field verification
    IsTrue,

    /// Ordering comparison
    Ordering {
        /// Ordering comparison operator:
        /// * "eq" | "EQ" | "=="
        /// * "ne" | "NE" | "!="
        /// * "ge" | "GE" | ">="
        /// * "le" | "LE" | "<="
        /// * "gt" | "GT" | ">"
        /// * "lt" | "LT" | "<"
        op: OrderingOpBuilder,
        /// Right-hand side literal
        rhs: RhsValueBuilder,
    },

    /// Ordering comparison with a variable
    OrderingVariable {
        /// Ordering comparison operator:
        /// * "eq" | "EQ" | "=="
        /// * "ne" | "NE" | "!="
        /// * "ge" | "GE" | ">="
        /// * "le" | "LE" | "<="
        /// * "gt" | "GT" | ">"
        /// * "lt" | "LT" | "<"
        op: OrderingOpBuilder,
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },

    /// Integer comparison
    Int {
        /// Integer comparison operator:
        /// * "&" | "bitwise_and" | "BITWISE_AND"
        op: IntOpBuilder,
        /// Right-hand side integer value
        rhs: i32,
    },

    /// Integer comparison with a variable
    IntVariable {
        /// Integer comparison operator:
        /// * "&" | "bitwise_and" | "BITWISE_AND"
        op: IntOpBuilder,
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },

    /// "contains" / "CONTAINS" comparison
    Contains {
        /// Right-hand side bytes value
        rhs: BytesBuilder,
    },

    /// "contains" / "CONTAINS" comparison with a variable
    ContainsVariable {
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },

    /// "matches / MATCHES / ~" comparison
    Matches {
        /// Right-hand side regex value
        rhs: RegexBuilder,
    },

    /// "matches / MATCHES / ~" comparison with a variable
    MatchesVariable {
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },

    /// "in [...]" / "IN [...]" comparison
    OneOf {
        /// Right-hand side values
        rhs: RhsValuesBuilder,
    },

    /// "in $..." | "IN $..." comparison with a variable
    OneOfVariable {
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },

    /// "has_any [...]" / "HAS_ANY [...]" comparison
    HasAny {
        /// Right-hand side values
        rhs: RhsValuesBuilder,
    },

    /// "has_any $..." / "HAS_ANY $..." comparison with a variable
    HasAnyVariable {
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },

    /// "has_all [...]" / "HAS_ALL [...]" comparison
    HasAll {
        /// Right-hand side values
        rhs: RhsValuesBuilder,
    },

    /// "has_all $..." / "HAS_ALL $..." comparison with a variable
    HasAllVariable {
        /// `Variable` from the `Scheme`
        var: VariableBuilder,
    },
}

/// Builder for `Regex`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct RegexBuilder {
    /// Regex value.
    pub(crate) value: String,
    /// Type of string literal.
    pub(crate) ty: StrTypeBuilder,
}

/// Builder for `Bytes`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum BytesBuilder {
    /// String representation of bytes
    Str {
        /// String value.
        value: Box<str>,
        /// Type of string literal.
        ty: StrTypeBuilder,
    },
    /// Raw representation of bytes.
    Raw {
        /// Raw bytes.
        value: Box<[u8]>,
        /// Separator between bytes.
        separator: ByteSeparatorBuilder,
    },
}

/// Builder for `StrType`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum StrTypeBuilder {
    /// Raw string literal.
    Raw {
        /// Number of `#` characters in the opening and closing delimiter.
        hash_count: usize,
    },
    /// Escaped string literal.
    Escaped,
}

/// Builder for `ByteSeparator`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum ByteSeparatorBuilder {
    /// Colon separator.
    Colon,
    /// Dash separator.
    Dash,
    /// Dot separator.
    Dot,
}

/// Builder for `IntOp`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum IntOpBuilder {
    /// "&" | "bitwise_and" | "BITWISE_AND"
    BitwiseAnd,
}

/// Builder for `RhsValue`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum RhsValueBuilder {
    /// A 32-bit integer number.
    Int(i32),
    /// A 64-bit floating point number.
    Float(f64),
    /// An IPv4 or IPv6 address.
    ///
    /// These are represented as a single type to allow interop comparisons.
    Ip(IpAddr),
    /// A raw bytes or a string field.
    ///
    /// These are completely interchangeable in runtime and differ only in
    /// syntax representation, so we represent them as a single type.
    Bytes(BytesBuilder),
}

/// Builder for `RhsValues`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum RhsValuesBuilder {
    /// A list of 32-bit integer numbers.
    Int(Vec<(i32, i32)>),
    /// A list of 64-bit floating point numbers.
    Float(Vec<(f64, f64)>),
    /// A list of IPv4 or IPv6 addresses.
    Ip(Vec<IpRangeBuilder>),
    /// A list of raw bytes or string fields.
    Bytes(Vec<BytesBuilder>),
}

/// Builder for `IpRange`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum IpRangeBuilder {
    /// Explicit range of IP addresses.
    Explicit(ExplicitIpRangeBuilder),
    /// CIDR range of IP addresses.
    Cidr(IpCidrBuilder),
}

/// Builder for `ExplicitIpRange`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum ExplicitIpRangeBuilder {
    /// An explicit range of IPv4 addresses.
    V4((Ipv4Addr, Ipv4Addr)),
    /// An explicit range of IPv6 addresses.
    V6((Ipv6Addr, Ipv6Addr)),
}

/// Builder for `IpCidr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct IpCidrBuilder(pub IpAddr, pub u8);

/// Builder for `OrderingOp`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum OrderingOpBuilder {
    /// "eq" | "EQ" | "=="
    Equal,
    /// "ne" | "NE" | "!="
    NotEqual,
    /// "ge" | "GE" | ">="
    GreaterThanEqual,
    /// "le" | "LE" | "<="
    LessThanEqual,
    /// "gt" | "GT" | ">"
    GreaterThan,
    /// "lt" | "LT" | "<"
    LessThan,
}

/// Builder for `IndexExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct IndexExprBuilder {
    /// Left-hand side of the index expression.
    pub lhs: LhsFieldExprBuilder,
    /// Indexes to access the value.
    pub indexes: Vec<FieldIndexBuilder>,
}

/// Builder for `FieldIndex`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum FieldIndexBuilder {
    /// Index into an Array
    ArrayIndex(u32),

    /// Key into a Map
    MapKey(String),

    /// Map each element by applying a function or a comparison
    MapEach,
}

/// Builder for `LhsFieldExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum LhsFieldExprBuilder {
    /// Field expression
    Field(FieldBuilder),
    /// Function call expression
    FunctionCallExpr(FunctionCallExprBuilder),
}

/// Builder for `FunctionCallExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct FunctionCallExprBuilder {
    /// Function being called.
    pub function: FunctionBuilder,
    /// Return type of the function.
    pub return_type: TypeBuilder,
    /// Arguments of the function.
    pub args: Vec<FunctionCallArgExprBuilder>,
}

/// Builder for `Type`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum TypeBuilder {
    /// A boolean.
    Bool,

    /// A 32-bit integer number.
    Int,

    /// A 64-bit floating point number.
    Float,

    /// An IPv4 or IPv6 address.
    ///
    /// These are represented as a single type to allow interop comparisons.
    Ip,

    /// A raw bytes or a string field.
    ///
    /// These are completely interchangeable in runtime and differ only in
    /// syntax representation, so we represent them as a single type.
    Bytes,

    /// An Array of [`Type`].
    Array(Box<TypeBuilder>),

    /// A Map of string to [`Type`].
    Map(Box<TypeBuilder>),
}

/// Builder for `FunctionCallArgExpr`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum FunctionCallArgExprBuilder {
    /// IndexExpr is a field that supports the indexing operator.
    IndexExpr(IndexExprBuilder),
    /// A literal.
    Literal(RhsValueBuilder),
    /// SimpleExpr is a sub-expression which can evaluate to either true/false
    /// or a list of true/false. It compiles to a CompiledExpr and is coerced
    /// into a CompiledValueExpr.
    SimpleExpr(SimpleExprBuilder),
    /// A variable.
    Variable(VariableBuilder),
}

/// Builder for `Variable`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct VariableBuilder {
    /// Name of the variable.
    pub name: String,
}

/// Builder for `Function`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct FunctionBuilder {
    /// Name of the function.
    pub name: String,
}

/// Builder for `Field`.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct FieldBuilder {
    /// Name of the field.
    pub name: String,
}
