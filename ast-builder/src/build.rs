//! AST builder implementations for WireFilter.

use std::net::IpAddr;

use cidr::IpCidr;
use wirefilter::{
    ByteSeparator, Bytes, ComparisonExpr, ComparisonOpExpr, ExplicitIpRange, FieldIndex, FilterAst,
    FloatRange, Function, FunctionCallArgExpr, FunctionCallExpr, GetType, IndexExpr, IntOp,
    IntRange, IpRange, LhsFieldExpr, LogicalExpr, LogicalOp, OrderedFloat, OrderingOp, Regex,
    RhsValue, RhsValues, Scheme, SimpleExpr, SingleValueExprAst, StrType, Type, UnaryOp,
    UnknownVariableError, Variable, Variables,
};

use crate::ast::*;
use crate::BuilderError;
use crate::Result;

impl FilterAstBuilder {
    /// Creates a new `FilterAstBuilder` with the given root `LogicalExprBuilder`.
    pub fn new(op: LogicalExprBuilder) -> Self {
        Self { op }
    }

    /// Builds a `FilterAst` from the `FilterAstBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<FilterAst<'s>> {
        Ok(FilterAst {
            scheme,
            op: self.op.build(scheme, variables)?,
        })
    }

    /// Creates a new `FilterAstBuilder` from the given `FilterAst`.
    pub fn from(filter_ast: FilterAst<'_>) -> Result<Self> {
        Ok(Self {
            op: LogicalExprBuilder::from(filter_ast.op)?,
        })
    }
}

impl SingleValueExprAstBuilder {
    /// Creates a new `SingleValueExprAstBuilder` with the given root `LhsFieldExprBuilder`.
    pub fn new(op: LhsFieldExprBuilder) -> Self {
        Self { op }
    }

    /// Builds a `SingleValueExprAst` from the `SingleValueExprAstBuilder`.
    pub fn build<'s>(
        self,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> Result<SingleValueExprAst<'s>> {
        Ok(SingleValueExprAst {
            scheme,
            op: self.op.build(scheme, variables)?,
        })
    }

    /// Creates a new `SingleValueExprAstBuilder` from the given `SingleValueExprAst`.
    pub fn from(single_value_expr: SingleValueExprAst<'_>) -> Result<Self> {
        Ok(Self {
            op: LhsFieldExprBuilder::from(single_value_expr.op)?,
        })
    }
}

impl LogicalExprBuilder {
    /// Builds a `LogicalExprAst` from the `LogicalExprBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<LogicalExpr<'s>> {
        match self {
            LogicalExprBuilder::Simple(builder) => {
                Ok(LogicalExpr::Simple(builder.build(scheme, variables)?))
            }
            LogicalExprBuilder::Combining(builder) => builder.build(scheme, variables),
        }
    }

    /// Creates a new `LogicalExprBuilder` from the given `LogicalExpr`.
    pub fn from(logical_expr: LogicalExpr<'_>) -> Result<Self> {
        Ok(match logical_expr {
            LogicalExpr::Simple(expr) => LogicalExprBuilder::Simple(SimpleExprBuilder::from(expr)?),
            LogicalExpr::Combining { op, items } => {
                LogicalExprBuilder::Combining(CombiningExprBuilder::new(
                    LogicalOpBuilder::from(op),
                    items
                        .into_iter()
                        .map(LogicalExprBuilder::from)
                        .collect::<Result<Vec<_>>>()?,
                ))
            }
        })
    }
}

impl CombiningExprBuilder {
    /// Creates a new `CombiningExprBuilder` with the given `op` and `items`.
    pub fn new(op: LogicalOpBuilder, items: Vec<LogicalExprBuilder>) -> Self {
        Self { op, items }
    }

    /// Builds a `CombiningExpr` from the `CombiningExprBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<LogicalExpr<'s>> {
        Ok(LogicalExpr::Combining {
            op: self.op.build(),
            items: self
                .items
                .into_iter()
                .map(|i| i.build(scheme, variables))
                .collect::<Result<Vec<_>>>()?,
        })
    }

    /// Creates a new `CombiningExprBuilder` from the given `LogicalExpr`.
    pub fn from(logical_expr: LogicalExpr<'_>) -> Result<Self> {
        Ok(match logical_expr {
            LogicalExpr::Simple(expr) => CombiningExprBuilder::new(
                LogicalOpBuilder::from(LogicalOp::And(0)),
                vec![LogicalExprBuilder::Simple(SimpleExprBuilder::from(expr)?)],
            ),
            LogicalExpr::Combining { op, items } => CombiningExprBuilder::new(
                LogicalOpBuilder::from(op),
                items
                    .into_iter()
                    .map(LogicalExprBuilder::from)
                    .collect::<Result<Vec<_>>>()?,
            ),
        })
    }
}

impl LogicalOpBuilder {
    /// Builds a `LogicalOp` from the `LogicalOpBuilder`.
    pub fn build(self) -> LogicalOp {
        match self {
            LogicalOpBuilder::Or => LogicalOp::Or(0),
            LogicalOpBuilder::Xor => LogicalOp::Xor(0),
            LogicalOpBuilder::And => LogicalOp::And(0),
        }
    }

    /// Creates a new `LogicalOpBuilder` from the given `LogicalOp`.
    pub fn from(logical_op: LogicalOp) -> Self {
        match logical_op {
            LogicalOp::Or(_) => LogicalOpBuilder::Or,
            LogicalOp::Xor(_) => LogicalOpBuilder::Xor,
            LogicalOp::And(_) => LogicalOpBuilder::And,
        }
    }
}

impl SimpleExprBuilder {
    /// Builds a `SimpleExprAst` from the `SimpleExprBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<SimpleExpr<'s>> {
        match self {
            SimpleExprBuilder::Comparison(builder) => {
                Ok(SimpleExpr::Comparison(builder.build(scheme, variables)?))
            }
            SimpleExprBuilder::Parenthesized(builder) => Ok(SimpleExpr::Parenthesized(Box::new(
                builder.build(scheme, variables)?,
            ))),
            SimpleExprBuilder::Unary(builder) => builder.build(scheme, variables),
        }
    }

    /// Creates a new `SimpleExprBuilder` from the given `SimpleExpr`.
    pub fn from(simple_expr: SimpleExpr<'_>) -> Result<Self> {
        Ok(match simple_expr {
            SimpleExpr::Comparison(comparison) => {
                SimpleExprBuilder::Comparison(ComparisonExprBuilder::from(comparison)?)
            }
            SimpleExpr::Parenthesized(expr) => {
                SimpleExprBuilder::Parenthesized(Box::new(LogicalExprBuilder::from(*expr)?))
            }
            SimpleExpr::Unary { .. } => {
                SimpleExprBuilder::Unary(UnaryExprBuilder::from(simple_expr)?)
            }
        })
    }
}

impl UnaryExprBuilder {
    /// Creates a new `UnaryExprBuilder` with the given `op` and `arg`.
    pub fn new(op: UnaryOpBuilder, arg: SimpleExprBuilder) -> Self {
        Self {
            op,
            arg: Box::new(arg),
        }
    }

    /// Builds a `UnaryExpr` from the `UnaryExprBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<SimpleExpr<'s>> {
        Ok(SimpleExpr::Unary {
            op: self.op.build(),
            arg: Box::new(self.arg.build(scheme, variables)?),
        })
    }

    /// Creates a new `UnaryExprBuilder` from the given `SimpleExpr`.
    pub fn from(expr: SimpleExpr<'_>) -> Result<Self> {
        match expr {
            SimpleExpr::Unary { op, arg } => Ok(Self {
                op: UnaryOpBuilder::from(op),
                arg: Box::new(SimpleExprBuilder::from(*arg)?),
            }),
            _ => Err(BuilderError::UnsupportedUnaryExpr(expr.get_type())),
        }
    }
}

impl UnaryOpBuilder {
    /// Builds a `UnaryOp` from the `UnaryOpBuilder`.
    pub fn build(self) -> UnaryOp {
        match self {
            UnaryOpBuilder::Not => UnaryOp::Not(0),
        }
    }

    /// Creates a new `UnaryOpBuilder` from the given `UnaryOp`.
    pub fn from(unary_op: UnaryOp) -> Self {
        match unary_op {
            UnaryOp::Not(_) => UnaryOpBuilder::Not,
        }
    }
}

impl ComparisonExprBuilder {
    /// Creates a new `ComparisonExprBuilder` with the given `lhs` and `op`.
    pub fn new(lhs: IndexExprBuilder, op: ComparisonOpExprBuilder) -> Self {
        Self { lhs, op }
    }

    /// Builds a `ComparisonExpr` from the `ComparisonExprBuilder`.
    pub fn build<'s>(
        self,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> Result<ComparisonExpr<'s>> {
        Ok(ComparisonExpr {
            lhs: self.lhs.build(scheme, variables)?,
            op: self.op.build(variables)?,
        })
    }

    /// Creates a new `ComparisonExprBuilder` from the given `ComparisonExpr`.
    pub fn from(comparison_expr: ComparisonExpr<'_>) -> Result<Self> {
        Ok(Self {
            lhs: IndexExprBuilder::from(comparison_expr.lhs)?,
            op: ComparisonOpExprBuilder::from(comparison_expr.op)?,
        })
    }
}

impl RegexBuilder {
    /// Creates a new `RegexBuilder` with the given `value` and `ty`.
    pub fn new(value: String, ty: StrTypeBuilder) -> Self {
        Self { value, ty }
    }

    /// Builds a `Regex` from the `RegexBuilder`.
    pub fn build(self) -> Result<Regex> {
        Ok(Regex::parse_str_with_str_type(
            &self.value,
            self.ty.build(),
        )?)
    }

    /// Creates a new `RegexBuilder` from the given `Regex`.
    pub fn from(regex: Regex) -> Self {
        Self {
            value: regex.as_str().to_string(),
            ty: StrTypeBuilder::from(regex.ty()),
        }
    }
}

impl BytesBuilder {
    /// Builds a `Bytes` from the `BytesBuilder`.
    pub fn build(self) -> Bytes {
        match self {
            BytesBuilder::Str { value, ty } => Bytes::Str {
                value,
                ty: ty.build(),
            },
            BytesBuilder::Raw { value, separator } => Bytes::Raw {
                value,
                separator: separator.build(),
            },
        }
    }

    /// Creates a new `BytesBuilder` from the given `Bytes`.
    pub fn from(bytes: Bytes) -> Self {
        match bytes {
            Bytes::Str { value, ty } => BytesBuilder::Str {
                value,
                ty: StrTypeBuilder::from(ty),
            },
            Bytes::Raw { value, separator } => BytesBuilder::Raw {
                value,
                separator: ByteSeparatorBuilder::from(separator),
            },
        }
    }
}

impl StrTypeBuilder {
    /// Builds a `StrType` from the `StrTypeBuilder`.
    pub fn build(self) -> StrType {
        match self {
            StrTypeBuilder::Raw { hash_count } => StrType::Raw { hash_count },
            StrTypeBuilder::Escaped => StrType::Escaped,
        }
    }

    /// Creates a new `StrTypeBuilder` from the given `StrType`.
    pub fn from(str_type: StrType) -> Self {
        match str_type {
            StrType::Raw { hash_count } => StrTypeBuilder::Raw { hash_count },
            StrType::Escaped => StrTypeBuilder::Escaped,
        }
    }
}

impl ByteSeparatorBuilder {
    /// Builds a `ByteSeparator` from the `ByteSeparatorBuilder`.
    pub fn build(self) -> ByteSeparator {
        match self {
            ByteSeparatorBuilder::Colon => ByteSeparator::Colon(0),
            ByteSeparatorBuilder::Dash => ByteSeparator::Dash(0),
            ByteSeparatorBuilder::Dot => ByteSeparator::Dot(0),
        }
    }

    /// Creates a new `ByteSeparatorBuilder` from the given `ByteSeparator`.
    pub fn from(separator: ByteSeparator) -> Self {
        match separator {
            ByteSeparator::Colon(_) => ByteSeparatorBuilder::Colon,
            ByteSeparator::Dash(_) => ByteSeparatorBuilder::Dash,
            ByteSeparator::Dot(_) => ByteSeparatorBuilder::Dot,
        }
    }
}

impl IntOpBuilder {
    /// Builds a `IntOp` from the `IntOpBuilder`.
    pub fn build(self) -> IntOp {
        match self {
            IntOpBuilder::BitwiseAnd => IntOp::BitwiseAnd(0),
        }
    }

    /// Creates a new `IntOpBuilder` from the given `IntOp`.
    pub fn from(int_op: IntOp) -> Self {
        match int_op {
            IntOp::BitwiseAnd(_) => IntOpBuilder::BitwiseAnd,
        }
    }
}

impl RhsValueBuilder {
    /// Builds a `RhsValue` from the `RhsValueBuilder`.
    pub fn build(self) -> RhsValue {
        match self {
            RhsValueBuilder::Int(value) => RhsValue::Int(value),
            RhsValueBuilder::Float(value) => RhsValue::Float(OrderedFloat(value)),
            RhsValueBuilder::Ip(value) => RhsValue::Ip(value),
            RhsValueBuilder::Bytes(value) => RhsValue::Bytes(value.build()),
        }
    }

    /// Creates a new `RhsValueBuilder` from the given `RhsValue`.
    pub fn from(rhs_value: RhsValue) -> Result<Self> {
        Ok(match rhs_value {
            RhsValue::Int(value) => RhsValueBuilder::Int(value),
            RhsValue::Float(value) => RhsValueBuilder::Float(value.into_inner()),
            RhsValue::Ip(value) => RhsValueBuilder::Ip(value),
            RhsValue::Bytes(value) => RhsValueBuilder::Bytes(BytesBuilder::from(value)),
            _ => return Err(BuilderError::UnsupportedRhsValue(rhs_value.get_type())),
        })
    }
}

impl RhsValuesBuilder {
    /// Builds a `RhsValues` from the `RhsValuesBuilder`.
    pub fn build(self) -> Result<RhsValues> {
        Ok(match self {
            RhsValuesBuilder::Int(values) => RhsValues::Int(
                values
                    .into_iter()
                    .map(|(first, last)| IntRange(first..=last))
                    .collect(),
            ),
            RhsValuesBuilder::Float(values) => RhsValues::Float(
                values
                    .into_iter()
                    .map(|(first, last)| FloatRange(OrderedFloat(first)..=OrderedFloat(last)))
                    .collect(),
            ),
            RhsValuesBuilder::Ip(values) => RhsValues::Ip(
                values
                    .into_iter()
                    .map(|value| value.build())
                    .collect::<Result<Vec<_>>>()?,
            ),
            RhsValuesBuilder::Bytes(values) => RhsValues::Bytes(
                values
                    .into_iter()
                    .map(BytesBuilder::build)
                    .collect::<Vec<_>>(),
            ),
        })
    }

    /// Creates a new `RhsValuesBuilder` from the given `RhsValues`.
    pub fn from(rhs_values: RhsValues) -> Result<Self> {
        Ok(match rhs_values {
            RhsValues::Int(values) => RhsValuesBuilder::Int(
                values
                    .into_iter()
                    .map(|range| (*range.0.start(), *range.0.end()))
                    .collect(),
            ),
            RhsValues::Float(values) => RhsValuesBuilder::Float(
                values
                    .into_iter()
                    .map(|range| (range.0.start().into_inner(), range.0.end().into_inner()))
                    .collect(),
            ),
            RhsValues::Ip(values) => RhsValuesBuilder::Ip(
                values
                    .into_iter()
                    .map(IpRangeBuilder::from)
                    .collect::<Result<Vec<_>>>()?,
            ),
            RhsValues::Bytes(values) => {
                RhsValuesBuilder::Bytes(values.into_iter().map(BytesBuilder::from).collect())
            }
            _ => return Err(BuilderError::UnsupportedRhsValue(rhs_values.get_type())),
        })
    }
}

impl IpRangeBuilder {
    /// Builds a `IpRange` from the `IpRangeBuilder`.
    pub fn build(self) -> Result<IpRange> {
        Ok(match self {
            IpRangeBuilder::Explicit(builder) => IpRange::Explicit(builder.build()),
            IpRangeBuilder::Cidr(builder) => IpRange::Cidr(builder.build()?),
        })
    }

    /// Creates a new `IpRangeBuilder` from the given `IpRange`.
    pub fn from(ip_range: IpRange) -> Result<Self> {
        Ok(match ip_range {
            IpRange::Explicit(range) => {
                IpRangeBuilder::Explicit(ExplicitIpRangeBuilder::from(range))
            }
            IpRange::Cidr(cidr) => IpRangeBuilder::Cidr(IpCidrBuilder::from(cidr)),
        })
    }
}

impl ExplicitIpRangeBuilder {
    /// Builds a `ExplicitIpRange` from the `ExplicitIpRangeBuilder`.
    pub fn build(self) -> ExplicitIpRange {
        match self {
            ExplicitIpRangeBuilder::V4((first, last)) => ExplicitIpRange::V4(first..=last),
            ExplicitIpRangeBuilder::V6((first, last)) => ExplicitIpRange::V6(first..=last),
        }
    }

    /// Creates a new `ExplicitIpRangeBuilder` from the given `ExplicitIpRange`.
    pub fn from(explicit_ip_range: ExplicitIpRange) -> Self {
        match explicit_ip_range {
            ExplicitIpRange::V4(range) => {
                ExplicitIpRangeBuilder::V4((*range.start(), *range.end()))
            }
            ExplicitIpRange::V6(range) => {
                ExplicitIpRangeBuilder::V6((*range.start(), *range.end()))
            }
        }
    }
}

impl IpCidrBuilder {
    /// Creates a new `IpCidrBuilder` with the given `addr` and `len`.
    pub fn new(addr: IpAddr, len: u8) -> Self {
        Self(addr, len)
    }

    /// Builds a `IpCidr` from the `IpCidrBuilder`.
    pub fn build(self) -> Result<IpCidr> {
        Ok(IpCidr::new(self.0, self.1)?)
    }

    /// Creates a new `IpCidrBuilder` from the given `IpCidr`.
    pub fn from(ip_cidr: IpCidr) -> Self {
        IpCidrBuilder::new(ip_cidr.first_address(), ip_cidr.network_length())
    }
}

impl ComparisonOpExprBuilder {
    /// Builds a `ComparisonOpExpr` from the `ComparisonOpExprBuilder`.
    pub fn build(self, variables: &Variables) -> Result<ComparisonOpExpr> {
        Ok(match self {
            ComparisonOpExprBuilder::IsTrue => ComparisonOpExpr::IsTrue,
            ComparisonOpExprBuilder::Ordering { op, rhs } => ComparisonOpExpr::Ordering {
                op: op.build(),
                rhs: rhs.build(),
            },
            ComparisonOpExprBuilder::OrderingVariable { op, var } => {
                ComparisonOpExpr::OrderingVariable {
                    op: op.build(),
                    var: var.build(variables)?,
                }
            }
            ComparisonOpExprBuilder::Int { op, rhs } => ComparisonOpExpr::Int {
                op: op.build(),
                rhs,
            },
            ComparisonOpExprBuilder::IntVariable { op, var } => ComparisonOpExpr::IntVariable {
                op: op.build(),
                var: var.build(variables)?,
            },
            ComparisonOpExprBuilder::Contains { rhs } => ComparisonOpExpr::Contains {
                rhs: rhs.build(),
                variant: 0,
            },
            ComparisonOpExprBuilder::ContainsVariable { var } => {
                ComparisonOpExpr::ContainsVariable {
                    var: var.build(variables)?,
                    variant: 0,
                }
            }
            ComparisonOpExprBuilder::Matches { rhs } => ComparisonOpExpr::Matches {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::MatchesVariable { var } => ComparisonOpExpr::MatchesVariable {
                var: var.build(variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::OneOf { rhs } => ComparisonOpExpr::OneOf {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::OneOfVariable { var } => ComparisonOpExpr::OneOfVariable {
                var: var.build(variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAny { rhs } => ComparisonOpExpr::HasAny {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAnyVariable { var } => ComparisonOpExpr::HasAnyVariable {
                var: var.build(variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAll { rhs } => ComparisonOpExpr::HasAll {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAllVariable { var } => ComparisonOpExpr::HasAllVariable {
                var: var.build(variables)?,
                variant: 0,
            },
        })
    }

    /// Creates a new `ComparisonOpExprBuilder` from the given `ComparisonOpExpr`.
    pub fn from(comparison_op_expr: ComparisonOpExpr) -> Result<Self> {
        Ok(match comparison_op_expr {
            ComparisonOpExpr::IsTrue => ComparisonOpExprBuilder::IsTrue,
            ComparisonOpExpr::Ordering { op, rhs } => ComparisonOpExprBuilder::Ordering {
                op: OrderingOpBuilder::from(op),
                rhs: RhsValueBuilder::from(rhs)?,
            },
            ComparisonOpExpr::OrderingVariable { op, var } => {
                ComparisonOpExprBuilder::OrderingVariable {
                    op: OrderingOpBuilder::from(op),
                    var: VariableBuilder::from(var),
                }
            }
            ComparisonOpExpr::Int { op, rhs } => ComparisonOpExprBuilder::Int {
                op: IntOpBuilder::from(op),
                rhs,
            },
            ComparisonOpExpr::IntVariable { op, var } => ComparisonOpExprBuilder::IntVariable {
                op: IntOpBuilder::from(op),
                var: VariableBuilder::from(var),
            },
            ComparisonOpExpr::Contains { rhs, variant: _ } => ComparisonOpExprBuilder::Contains {
                rhs: BytesBuilder::from(rhs),
            },
            ComparisonOpExpr::ContainsVariable { var, variant: _ } => {
                ComparisonOpExprBuilder::ContainsVariable {
                    var: VariableBuilder::from(var),
                }
            }
            ComparisonOpExpr::Matches { rhs, .. } => ComparisonOpExprBuilder::Matches {
                rhs: RegexBuilder::from(rhs),
            },
            ComparisonOpExpr::MatchesVariable { var, .. } => {
                ComparisonOpExprBuilder::MatchesVariable {
                    var: VariableBuilder::from(var),
                }
            }
            ComparisonOpExpr::OneOf { rhs, .. } => ComparisonOpExprBuilder::OneOf {
                rhs: RhsValuesBuilder::from(rhs)?,
            },
            ComparisonOpExpr::OneOfVariable { var, .. } => ComparisonOpExprBuilder::OneOfVariable {
                var: VariableBuilder::from(var),
            },
            ComparisonOpExpr::HasAny { rhs, .. } => ComparisonOpExprBuilder::HasAny {
                rhs: RhsValuesBuilder::from(rhs)?,
            },
            ComparisonOpExpr::HasAnyVariable { var, .. } => {
                ComparisonOpExprBuilder::HasAnyVariable {
                    var: VariableBuilder::from(var),
                }
            }
            ComparisonOpExpr::HasAll { rhs, .. } => ComparisonOpExprBuilder::HasAll {
                rhs: RhsValuesBuilder::from(rhs)?,
            },
            ComparisonOpExpr::HasAllVariable { var, .. } => {
                ComparisonOpExprBuilder::HasAllVariable {
                    var: VariableBuilder::from(var),
                }
            }
        })
    }
}

impl OrderingOpBuilder {
    /// Builds a `OrderingOp` from the `OrderingOpBuilder`.
    pub fn build(self) -> OrderingOp {
        match self {
            OrderingOpBuilder::Equal => OrderingOp::Equal(0),
            OrderingOpBuilder::NotEqual => OrderingOp::NotEqual(0),
            OrderingOpBuilder::GreaterThanEqual => OrderingOp::GreaterThanEqual(0),
            OrderingOpBuilder::LessThanEqual => OrderingOp::LessThanEqual(0),
            OrderingOpBuilder::GreaterThan => OrderingOp::GreaterThan(0),
            OrderingOpBuilder::LessThan => OrderingOp::LessThan(0),
        }
    }

    /// Creates a new `OrderingOpBuilder` from the given `OrderingOp`.
    pub fn from(ordering_op: OrderingOp) -> Self {
        match ordering_op {
            OrderingOp::Equal(_) => OrderingOpBuilder::Equal,
            OrderingOp::NotEqual(_) => OrderingOpBuilder::NotEqual,
            OrderingOp::GreaterThanEqual(_) => OrderingOpBuilder::GreaterThanEqual,
            OrderingOp::LessThanEqual(_) => OrderingOpBuilder::LessThanEqual,
            OrderingOp::GreaterThan(_) => OrderingOpBuilder::GreaterThan,
            OrderingOp::LessThan(_) => OrderingOpBuilder::LessThan,
        }
    }
}

impl IndexExprBuilder {
    /// Creates a new `IndexExprBuilder` with the given `lhs` and `indexes`.
    pub fn new(lhs: LhsFieldExprBuilder, indexes: Vec<FieldIndexBuilder>) -> Self {
        Self { lhs, indexes }
    }

    /// Builds a `IndexExpr` from the `IndexExprBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<IndexExpr<'s>> {
        Ok(IndexExpr {
            lhs: self.lhs.build(scheme, variables)?,
            indexes: self
                .indexes
                .into_iter()
                .map(FieldIndexBuilder::build)
                .collect(),
        })
    }

    /// Creates a new `IndexExprBuilder` from the given `IndexExpr`.
    pub fn from(index_expr: IndexExpr<'_>) -> Result<Self> {
        Ok(Self {
            lhs: LhsFieldExprBuilder::from(index_expr.lhs)?,
            indexes: index_expr
                .indexes
                .into_iter()
                .map(FieldIndexBuilder::from)
                .collect(),
        })
    }
}

impl FieldIndexBuilder {
    /// Builds a `FieldIndex` from the `FieldIndexBuilder`.
    pub fn build(self) -> FieldIndex {
        match self {
            FieldIndexBuilder::ArrayIndex(index) => FieldIndex::ArrayIndex(index),
            FieldIndexBuilder::MapKey(key) => FieldIndex::MapKey(key),
            FieldIndexBuilder::MapEach => FieldIndex::MapEach,
        }
    }

    /// Creates a new `FieldIndexBuilder` from the given `FieldIndex`.
    pub fn from(field_index: FieldIndex) -> Self {
        match field_index {
            FieldIndex::ArrayIndex(index) => FieldIndexBuilder::ArrayIndex(index),
            FieldIndex::MapKey(key) => FieldIndexBuilder::MapKey(key),
            FieldIndex::MapEach => FieldIndexBuilder::MapEach,
        }
    }
}

impl LhsFieldExprBuilder {
    /// Builds a `LhsFieldExpr` from the `LhsFieldExprBuilder`.
    pub fn build<'s>(self, scheme: &'s Scheme, variables: &Variables) -> Result<LhsFieldExpr<'s>> {
        match self {
            LhsFieldExprBuilder::Field(builder) => Ok(LhsFieldExpr::Field(builder.build(scheme)?)),
            LhsFieldExprBuilder::FunctionCallExpr(builder) => Ok(LhsFieldExpr::FunctionCallExpr(
                builder.build(scheme, variables)?,
            )),
        }
    }

    /// Creates a new `LhsFieldExprBuilder` from the given `LhsFieldExpr`.
    pub fn from(lhs_field_expr: LhsFieldExpr<'_>) -> Result<Self> {
        Ok(match lhs_field_expr {
            LhsFieldExpr::Field(field) => LhsFieldExprBuilder::Field(FieldBuilder::from(field)),
            LhsFieldExpr::FunctionCallExpr(expr) => {
                LhsFieldExprBuilder::FunctionCallExpr(FunctionCallExprBuilder::from(expr)?)
            }
        })
    }
}

impl FunctionCallExprBuilder {
    /// Creates a new `FunctionCallExprBuilder` with the given `function` and `args`.
    pub fn new(
        function: FunctionBuilder,
        return_type: TypeBuilder,
        args: Vec<FunctionCallArgExprBuilder>,
    ) -> Self {
        Self {
            function,
            return_type,
            args,
        }
    }

    /// Builds a `FunctionCallExpr` from the `FunctionCallExprBuilder`.
    pub fn build<'s>(
        self,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> Result<FunctionCallExpr<'s>> {
        Ok(FunctionCallExpr {
            function: self.function.build(scheme)?,
            return_type: self.return_type.build(),
            args: self
                .args
                .into_iter()
                .map(|a| a.build(scheme, variables))
                .collect::<Result<Vec<_>>>()?,
            context: None,
        })
    }

    /// Creates a new `FunctionCallExprBuilder` from the given `FunctionCallExpr`.
    pub fn from(expr: FunctionCallExpr<'_>) -> Result<Self> {
        Ok(Self {
            function: FunctionBuilder::from(expr.function),
            return_type: TypeBuilder::from(expr.return_type)?,
            args: expr
                .args
                .into_iter()
                .map(FunctionCallArgExprBuilder::from)
                .collect::<Result<Vec<_>>>()?,
        })
    }
}

impl TypeBuilder {
    /// Builds a `Type` from the `TypeBuilder`.
    pub fn build(self) -> Type {
        match self {
            TypeBuilder::Bool => Type::Bool,
            TypeBuilder::Int => Type::Int,
            TypeBuilder::Float => Type::Float,
            TypeBuilder::Ip => Type::Ip,
            TypeBuilder::Bytes => Type::Bytes,
            TypeBuilder::Array(inner) => Type::Array(Box::new(inner.build())),
            TypeBuilder::Map(inner) => Type::Map(Box::new(inner.build())),
        }
    }

    /// Creates a new `TypeBuilder` from the given `Type`.
    pub fn from(ty: Type) -> Result<Self> {
        Ok(match ty {
            Type::Bool => TypeBuilder::Bool,
            Type::Int => TypeBuilder::Int,
            Type::Float => TypeBuilder::Float,
            Type::Ip => TypeBuilder::Ip,
            Type::Bytes => TypeBuilder::Bytes,
            Type::Array(inner) => TypeBuilder::Array(Box::new(TypeBuilder::from(*inner)?)),
            Type::Map(inner) => TypeBuilder::Map(Box::new(TypeBuilder::from(*inner)?)),
            _ => return Err(BuilderError::UnsupportedType(ty)),
        })
    }
}

impl FunctionCallArgExprBuilder {
    /// Builds a `FunctionCallArgExpr` from the `FunctionCallArgExprBuilder`.
    pub fn build<'s>(
        self,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> Result<FunctionCallArgExpr<'s>> {
        Ok(match self {
            FunctionCallArgExprBuilder::IndexExpr(builder) => {
                FunctionCallArgExpr::IndexExpr(builder.build(scheme, variables)?)
            }
            FunctionCallArgExprBuilder::Literal(value) => {
                FunctionCallArgExpr::Literal(value.build())
            }
            FunctionCallArgExprBuilder::SimpleExpr(builder) => {
                FunctionCallArgExpr::SimpleExpr(builder.build(scheme, variables)?)
            }
            FunctionCallArgExprBuilder::Variable(builder) => {
                FunctionCallArgExpr::Variable(builder.build(variables)?)
            }
        })
    }

    /// Creates a new `FunctionCallArgExprBuilder` from the given `FunctionCallArgExpr`.
    pub fn from(arg: FunctionCallArgExpr<'_>) -> Result<Self> {
        Ok(match arg {
            FunctionCallArgExpr::IndexExpr(expr) => {
                FunctionCallArgExprBuilder::IndexExpr(IndexExprBuilder::from(expr)?)
            }
            FunctionCallArgExpr::Literal(value) => {
                FunctionCallArgExprBuilder::Literal(RhsValueBuilder::from(value)?)
            }
            FunctionCallArgExpr::SimpleExpr(expr) => {
                FunctionCallArgExprBuilder::SimpleExpr(SimpleExprBuilder::from(expr)?)
            }
            FunctionCallArgExpr::Variable(variable) => {
                FunctionCallArgExprBuilder::Variable(VariableBuilder::from(variable))
            }
        })
    }
}

impl FunctionBuilder {
    /// Creates a new `FunctionBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }

    /// Builds a `Function` from the `FunctionBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<Function<'_>> {
        Ok(scheme.get_function(&self.name)?)
    }

    /// Creates a new `FunctionBuilder` from the given `Function`.
    pub fn from(function: Function<'_>) -> Self {
        Self {
            name: function.name().to_string(),
        }
    }
}

impl VariableBuilder {
    /// Creates a new `VariableBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }

    /// Builds a `Variable` from the `VariableBuilder`.
    pub fn build(self, variables: &Variables) -> Result<Variable> {
        if let Some(variable_value) = variables.get(&self.name) {
            Ok(Variable::new_with_type(
                self.name,
                variable_value.get_variable_type(),
            ))
        } else {
            Err(BuilderError::VariableNotFound(UnknownVariableError))
        }
    }

    /// Creates a new `VariableBuilder` from the given `Variable`.
    pub fn from(variable: Variable) -> Self {
        Self {
            name: variable.take_name().to_string(),
        }
    }
}

impl FieldBuilder {
    /// Creates a new `FieldBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }

    /// Builds a `Field` from the `FieldBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<wirefilter::Field<'_>> {
        Ok(scheme.get_field(&self.name)?)
    }

    /// Creates a new `FieldBuilder` from the given `wirefilter::Field`.
    pub fn from(field: wirefilter::Field<'_>) -> Self {
        Self {
            name: field.name().to_string(),
        }
    }
}
