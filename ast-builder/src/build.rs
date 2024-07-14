//! AST builder implementations for WireFilter.

use std::net::IpAddr;

use cidr::IpCidr;
use wirefilter::{
    ByteSeparator, Bytes, CasePatternValue, Cases, ComparisonExpr, ComparisonOpExpr,
    ExplicitIpRange, Field, FieldIndex, FilterAst, FloatRange, Function, FunctionCallArgExpr,
    FunctionCallExpr, GetType, IndexExpr, IntOp, IntRange, IpRange, LhsFieldExpr, LogicalExpr,
    LogicalOp, OrderedFloat, OrderingOp, Regex, RhsValue, RhsValues, Scheme, SimpleExpr,
    SingleIndexExpr, SingleValueExprAst, StrType, Type, UnaryOp, UnknownVariableError, Variable,
    Variables,
};

use crate::ast::*;
use crate::BuilderError;
use crate::Result;

/// A trait for building and parsing ASTs.
pub trait AstBuilder<'s, 'v, T> {
    /// Builds a `T` from the `AstBuilder`.
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<T>;

    /// Creates a new `AstBuilder` from the given `T`.
    fn parse_ast(ast: T) -> Result<Self>
    where
        Self: Sized;
}

impl<'s, 'v> AstBuilder<'s, 'v, FilterAst<'s>> for FilterAstBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<FilterAst<'s>> {
        Ok(FilterAst {
            scheme,
            op: self.op.build(scheme, variables)?,
        })
    }

    fn parse_ast(filter_ast: FilterAst<'_>) -> Result<Self> {
        Ok(Self {
            op: LogicalExprBuilder::parse_ast(filter_ast.op)?,
        })
    }
}

impl FilterAstBuilder {
    /// Creates a new `FilterAstBuilder` with the given root `LogicalExprBuilder`.
    pub fn new(op: LogicalExprBuilder) -> Self {
        Self { op }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, SingleValueExprAst<'s>> for SingleValueExprAstBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<SingleValueExprAst<'s>> {
        Ok(SingleValueExprAst {
            scheme,
            op: self.op.build(scheme, variables)?,
        })
    }

    fn parse_ast(single_value_expr: SingleValueExprAst<'_>) -> Result<Self> {
        Ok(Self {
            op: SingleIndexExprBuilder::parse_ast(single_value_expr.op)?,
        })
    }
}

impl SingleValueExprAstBuilder {
    /// Creates a new `SingleValueExprAstBuilder` with the given root `SingleIndexExprBuilder`.
    pub fn new(op: SingleIndexExprBuilder) -> Self {
        Self { op }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, SingleIndexExpr<'s>> for SingleIndexExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<SingleIndexExpr<'s>> {
        Ok(SingleIndexExpr {
            op: self.op.build(scheme, variables)?,
            cases: if let Some(cases) = self.cases {
                Some(cases.build(scheme, variables)?)
            } else {
                None
            },
        })
    }

    fn parse_ast(single_value_expr: SingleIndexExpr<'_>) -> Result<Self> {
        Ok(Self {
            op: IndexExprBuilder::parse_ast(single_value_expr.op)?,
            cases: if let Some(cases) = single_value_expr.cases {
                Some(CasesBuilder::parse_ast(cases)?)
            } else {
                None
            },
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, LogicalExpr<'s>> for LogicalExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<LogicalExpr<'s>> {
        match self {
            LogicalExprBuilder::Simple(builder) => {
                Ok(LogicalExpr::Simple(builder.build(scheme, variables)?))
            }
            LogicalExprBuilder::Combining(builder) => builder.build(scheme, variables),
        }
    }

    fn parse_ast(logical_expr: LogicalExpr<'_>) -> Result<Self> {
        Ok(match logical_expr {
            LogicalExpr::Simple(expr) => {
                LogicalExprBuilder::Simple(SimpleExprBuilder::parse_ast(expr)?)
            }
            LogicalExpr::Combining { op, items } => {
                LogicalExprBuilder::Combining(CombiningExprBuilder::new(
                    LogicalOpBuilder::parse_ast(op)?,
                    items
                        .into_iter()
                        .map(LogicalExprBuilder::parse_ast)
                        .collect::<Result<Vec<_>>>()?,
                ))
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, LogicalExpr<'s>> for CombiningExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<LogicalExpr<'s>> {
        Ok(LogicalExpr::Combining {
            op: self.op.build(scheme, variables)?,
            items: self
                .items
                .into_iter()
                .map(|i| i.build(scheme, variables))
                .collect::<Result<Vec<_>>>()?,
        })
    }

    fn parse_ast(logical_expr: LogicalExpr<'_>) -> Result<Self> {
        Ok(match logical_expr {
            LogicalExpr::Simple(expr) => CombiningExprBuilder::new(
                LogicalOpBuilder::parse_ast(LogicalOp::And(0))?,
                vec![LogicalExprBuilder::Simple(SimpleExprBuilder::parse_ast(
                    expr,
                )?)],
            ),
            LogicalExpr::Combining { op, items } => CombiningExprBuilder::new(
                LogicalOpBuilder::parse_ast(op)?,
                items
                    .into_iter()
                    .map(LogicalExprBuilder::parse_ast)
                    .collect::<Result<Vec<_>>>()?,
            ),
        })
    }
}

impl CombiningExprBuilder {
    /// Creates a new `CombiningExprBuilder` with the given `op` and `items`.
    pub fn new(op: LogicalOpBuilder, items: Vec<LogicalExprBuilder>) -> Self {
        Self { op, items }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, LogicalOp> for LogicalOpBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<LogicalOp> {
        Ok(match self {
            LogicalOpBuilder::Or => LogicalOp::Or(0),
            LogicalOpBuilder::Xor => LogicalOp::Xor(0),
            LogicalOpBuilder::And => LogicalOp::And(0),
        })
    }

    fn parse_ast(logical_op: LogicalOp) -> Result<Self> {
        Ok(match logical_op {
            LogicalOp::Or(_) => LogicalOpBuilder::Or,
            LogicalOp::Xor(_) => LogicalOpBuilder::Xor,
            LogicalOp::And(_) => LogicalOpBuilder::And,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, SimpleExpr<'s>> for SimpleExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<SimpleExpr<'s>> {
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

    fn parse_ast(simple_expr: SimpleExpr<'_>) -> Result<Self> {
        Ok(match simple_expr {
            SimpleExpr::Comparison(comparison) => {
                SimpleExprBuilder::Comparison(ComparisonExprBuilder::parse_ast(comparison)?)
            }
            SimpleExpr::Parenthesized(expr) => {
                SimpleExprBuilder::Parenthesized(Box::new(LogicalExprBuilder::parse_ast(*expr)?))
            }
            SimpleExpr::Unary { .. } => {
                SimpleExprBuilder::Unary(UnaryExprBuilder::parse_ast(simple_expr)?)
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, SimpleExpr<'s>> for UnaryExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<SimpleExpr<'s>> {
        Ok(SimpleExpr::Unary {
            op: self.op.build(scheme, variables)?,
            arg: Box::new(self.arg.build(scheme, variables)?),
        })
    }

    fn parse_ast(simple_expr: SimpleExpr<'_>) -> Result<Self> {
        match simple_expr {
            SimpleExpr::Unary { op, arg } => Ok(Self {
                op: UnaryOpBuilder::parse_ast(op)?,
                arg: Box::new(SimpleExprBuilder::parse_ast(*arg)?),
            }),
            _ => Err(BuilderError::UnsupportedUnaryExpr(simple_expr.get_type())),
        }
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
}

impl<'s, 'v> AstBuilder<'s, 'v, UnaryOp> for UnaryOpBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<UnaryOp> {
        Ok(match self {
            UnaryOpBuilder::Not => UnaryOp::Not(0),
        })
    }

    fn parse_ast(unary_op: UnaryOp) -> Result<Self> {
        Ok(match unary_op {
            UnaryOp::Not(_) => UnaryOpBuilder::Not,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, ComparisonExpr<'s>> for ComparisonExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<ComparisonExpr<'s>> {
        Ok(ComparisonExpr {
            lhs: self.lhs.build(scheme, variables)?,
            op: self.op.build(scheme, variables)?,
        })
    }

    fn parse_ast(comparison_expr: ComparisonExpr<'_>) -> Result<Self> {
        Ok(Self {
            lhs: IndexExprBuilder::parse_ast(comparison_expr.lhs)?,
            op: ComparisonOpExprBuilder::parse_ast(comparison_expr.op)?,
        })
    }
}

impl ComparisonExprBuilder {
    /// Creates a new `ComparisonExprBuilder` with the given `lhs` and `op`.
    pub fn new(lhs: IndexExprBuilder, op: ComparisonOpExprBuilder) -> Self {
        Self { lhs, op }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Regex> for RegexBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<Regex> {
        Ok(Regex::parse_str_with_str_type(
            &self.value,
            self.ty.build(scheme, variables)?,
        )?)
    }

    fn parse_ast(regex: Regex) -> Result<Self> {
        Ok(Self {
            value: regex.as_str().to_string(),
            ty: StrTypeBuilder::parse_ast(regex.ty())?,
        })
    }
}

impl RegexBuilder {
    /// Creates a new `RegexBuilder` with the given `value` and `ty`.
    pub fn new(value: String, ty: StrTypeBuilder) -> Self {
        Self { value, ty }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Bytes> for BytesBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<Bytes> {
        Ok(match self {
            BytesBuilder::Str { value, ty } => Bytes::Str {
                value,
                ty: ty.build(scheme, variables)?,
            },
            BytesBuilder::Raw { value, separator } => Bytes::Raw {
                value,
                separator: separator.build(scheme, variables)?,
            },
        })
    }

    fn parse_ast(bytes: Bytes) -> Result<Self> {
        Ok(match bytes {
            Bytes::Str { value, ty } => BytesBuilder::Str {
                value,
                ty: StrTypeBuilder::parse_ast(ty)?,
            },
            Bytes::Raw { value, separator } => BytesBuilder::Raw {
                value,
                separator: ByteSeparatorBuilder::parse_ast(separator)?,
            },
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, StrType> for StrTypeBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<StrType> {
        Ok(match self {
            StrTypeBuilder::Raw { hash_count } => StrType::Raw { hash_count },
            StrTypeBuilder::Escaped => StrType::Escaped,
        })
    }

    fn parse_ast(str_type: StrType) -> Result<Self> {
        Ok(match str_type {
            StrType::Raw { hash_count } => StrTypeBuilder::Raw { hash_count },
            StrType::Escaped => StrTypeBuilder::Escaped,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, ByteSeparator> for ByteSeparatorBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<ByteSeparator> {
        Ok(match self {
            ByteSeparatorBuilder::Colon => ByteSeparator::Colon(0),
            ByteSeparatorBuilder::Dash => ByteSeparator::Dash(0),
            ByteSeparatorBuilder::Dot => ByteSeparator::Dot(0),
        })
    }

    fn parse_ast(separator: ByteSeparator) -> Result<Self> {
        Ok(match separator {
            ByteSeparator::Colon(_) => ByteSeparatorBuilder::Colon,
            ByteSeparator::Dash(_) => ByteSeparatorBuilder::Dash,
            ByteSeparator::Dot(_) => ByteSeparatorBuilder::Dot,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, IntOp> for IntOpBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<IntOp> {
        Ok(match self {
            IntOpBuilder::BitwiseAnd => IntOp::BitwiseAnd(0),
        })
    }

    fn parse_ast(int_op: IntOp) -> Result<Self> {
        Ok(match int_op {
            IntOp::BitwiseAnd(_) => IntOpBuilder::BitwiseAnd,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, CasePatternValue> for CasePatternValueBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<CasePatternValue> {
        Ok(match self {
            CasePatternValueBuilder::Bool => CasePatternValue::Bool,
            CasePatternValueBuilder::Int(value) => CasePatternValue::Int(value),
            CasePatternValueBuilder::IntRange((first, last)) => {
                CasePatternValue::IntRange(IntRange(first..=last))
            }
            CasePatternValueBuilder::Float(value) => CasePatternValue::Float(OrderedFloat(value)),
            CasePatternValueBuilder::FloatRange((first, last)) => {
                CasePatternValue::FloatRange(FloatRange(OrderedFloat(first)..=OrderedFloat(last)))
            }
            CasePatternValueBuilder::Ip(value) => CasePatternValue::Ip(value),
            CasePatternValueBuilder::IpRange(range) => {
                CasePatternValue::IpRange(range.build(scheme, variables)?)
            }
            CasePatternValueBuilder::Bytes(value) => {
                CasePatternValue::Bytes(value.build(scheme, variables)?)
            }
        })
    }

    fn parse_ast(case_pattern_value: CasePatternValue) -> Result<Self> {
        Ok(match case_pattern_value {
            CasePatternValue::Bool => CasePatternValueBuilder::Bool,
            CasePatternValue::Int(value) => CasePatternValueBuilder::Int(value),
            CasePatternValue::IntRange(range) => {
                CasePatternValueBuilder::IntRange((*range.0.start(), *range.0.end()))
            }
            CasePatternValue::Float(value) => CasePatternValueBuilder::Float(value.into_inner()),
            CasePatternValue::FloatRange(range) => CasePatternValueBuilder::FloatRange((
                range.0.start().into_inner(),
                range.0.end().into_inner(),
            )),
            CasePatternValue::Ip(value) => CasePatternValueBuilder::Ip(value),
            CasePatternValue::IpRange(range) => {
                CasePatternValueBuilder::IpRange(IpRangeBuilder::parse_ast(range)?)
            }
            CasePatternValue::Bytes(value) => {
                CasePatternValueBuilder::Bytes(BytesBuilder::parse_ast(value)?)
            }
            _ => {
                return Err(BuilderError::UnsupportedCasePatternValue(
                    case_pattern_value.get_type().unwrap_or(Type::Bool),
                ))
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, RhsValue> for RhsValueBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<RhsValue> {
        Ok(match self {
            RhsValueBuilder::Int(value) => RhsValue::Int(value),
            RhsValueBuilder::Float(value) => RhsValue::Float(OrderedFloat(value)),
            RhsValueBuilder::Ip(value) => RhsValue::Ip(value),
            RhsValueBuilder::Bytes(value) => RhsValue::Bytes(value.build(scheme, variables)?),
        })
    }

    fn parse_ast(rhs_value: RhsValue) -> Result<Self> {
        Ok(match rhs_value {
            RhsValue::Int(value) => RhsValueBuilder::Int(value),
            RhsValue::Float(value) => RhsValueBuilder::Float(value.into_inner()),
            RhsValue::Ip(value) => RhsValueBuilder::Ip(value),
            RhsValue::Bytes(value) => RhsValueBuilder::Bytes(BytesBuilder::parse_ast(value)?),
            _ => return Err(BuilderError::UnsupportedRhsValue(rhs_value.get_type())),
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, RhsValues> for RhsValuesBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<RhsValues> {
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
                    .map(|value| value.build(scheme, variables))
                    .collect::<Result<Vec<_>>>()?,
            ),
            RhsValuesBuilder::Bytes(values) => RhsValues::Bytes(
                values
                    .into_iter()
                    .map(|value| value.build(scheme, variables))
                    .collect::<Result<Vec<_>>>()?,
            ),
        })
    }

    fn parse_ast(rhs_values: RhsValues) -> Result<Self> {
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
                    .map(IpRangeBuilder::parse_ast)
                    .collect::<Result<Vec<_>>>()?,
            ),
            RhsValues::Bytes(values) => RhsValuesBuilder::Bytes(
                values
                    .into_iter()
                    .map(BytesBuilder::parse_ast)
                    .collect::<Result<_>>()?,
            ),
            _ => return Err(BuilderError::UnsupportedRhsValue(rhs_values.get_type())),
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, IpRange> for IpRangeBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<IpRange> {
        Ok(match self {
            IpRangeBuilder::Explicit(builder) => {
                IpRange::Explicit(builder.build(scheme, variables)?)
            }
            IpRangeBuilder::Cidr(builder) => IpRange::Cidr(builder.build(scheme, variables)?),
        })
    }

    fn parse_ast(ip_range: IpRange) -> Result<Self> {
        Ok(match ip_range {
            IpRange::Explicit(range) => {
                IpRangeBuilder::Explicit(ExplicitIpRangeBuilder::parse_ast(range)?)
            }
            IpRange::Cidr(cidr) => IpRangeBuilder::Cidr(IpCidrBuilder::parse_ast(cidr)?),
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, ExplicitIpRange> for ExplicitIpRangeBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<ExplicitIpRange> {
        Ok(match self {
            ExplicitIpRangeBuilder::V4((first, last)) => ExplicitIpRange::V4(first..=last),
            ExplicitIpRangeBuilder::V6((first, last)) => ExplicitIpRange::V6(first..=last),
        })
    }

    fn parse_ast(explicit_ip_range: ExplicitIpRange) -> Result<Self> {
        Ok(match explicit_ip_range {
            ExplicitIpRange::V4(range) => {
                ExplicitIpRangeBuilder::V4((*range.start(), *range.end()))
            }
            ExplicitIpRange::V6(range) => {
                ExplicitIpRangeBuilder::V6((*range.start(), *range.end()))
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, IpCidr> for IpCidrBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<IpCidr> {
        Ok(IpCidr::new(self.0, self.1)?)
    }

    fn parse_ast(ip_cidr: IpCidr) -> Result<Self> {
        Ok(IpCidrBuilder::new(
            ip_cidr.first_address(),
            ip_cidr.network_length(),
        ))
    }
}

impl IpCidrBuilder {
    /// Creates a new `IpCidrBuilder` with the given `addr` and `len`.
    pub fn new(addr: IpAddr, len: u8) -> Self {
        Self(addr, len)
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, ComparisonOpExpr<'s>> for ComparisonOpExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<ComparisonOpExpr<'s>> {
        Ok(match self {
            ComparisonOpExprBuilder::IsTrue => ComparisonOpExpr::IsTrue,
            ComparisonOpExprBuilder::Ordering { op, rhs } => ComparisonOpExpr::Ordering {
                op: op.build(scheme, variables)?,
                rhs: rhs.build(scheme, variables)?,
            },
            ComparisonOpExprBuilder::OrderingVariable { op, var } => {
                ComparisonOpExpr::OrderingVariable {
                    op: op.build(scheme, variables)?,
                    var: var.build(scheme, variables)?,
                }
            }
            ComparisonOpExprBuilder::Cases(cases) => {
                ComparisonOpExpr::Cases(cases.build(scheme, variables)?)
            }
            ComparisonOpExprBuilder::Int { op, rhs } => ComparisonOpExpr::Int {
                op: op.build(scheme, variables)?,
                rhs,
            },
            ComparisonOpExprBuilder::IntVariable { op, var } => ComparisonOpExpr::IntVariable {
                op: op.build(scheme, variables)?,
                var: var.build(scheme, variables)?,
            },
            ComparisonOpExprBuilder::Contains { rhs } => ComparisonOpExpr::Contains {
                rhs: rhs.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::ContainsVariable { var } => {
                ComparisonOpExpr::ContainsVariable {
                    var: var.build(scheme, variables)?,
                    variant: 0,
                }
            }
            ComparisonOpExprBuilder::Matches { rhs } => ComparisonOpExpr::Matches {
                rhs: rhs.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::MatchesVariable { var } => ComparisonOpExpr::MatchesVariable {
                var: var.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::OneOf { rhs } => ComparisonOpExpr::OneOf {
                rhs: rhs.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::OneOfVariable { var } => ComparisonOpExpr::OneOfVariable {
                var: var.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAny { rhs } => ComparisonOpExpr::HasAny {
                rhs: rhs.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAnyVariable { var } => ComparisonOpExpr::HasAnyVariable {
                var: var.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAll { rhs } => ComparisonOpExpr::HasAll {
                rhs: rhs.build(scheme, variables)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAllVariable { var } => ComparisonOpExpr::HasAllVariable {
                var: var.build(scheme, variables)?,
                variant: 0,
            },
        })
    }

    fn parse_ast(comparison_op_expr: ComparisonOpExpr) -> Result<Self> {
        Ok(match comparison_op_expr {
            ComparisonOpExpr::IsTrue => ComparisonOpExprBuilder::IsTrue,
            ComparisonOpExpr::Ordering { op, rhs } => ComparisonOpExprBuilder::Ordering {
                op: OrderingOpBuilder::parse_ast(op)?,
                rhs: RhsValueBuilder::parse_ast(rhs)?,
            },
            ComparisonOpExpr::OrderingVariable { op, var } => {
                ComparisonOpExprBuilder::OrderingVariable {
                    op: OrderingOpBuilder::parse_ast(op)?,
                    var: VariableBuilder::parse_ast(var)?,
                }
            }
            ComparisonOpExpr::Cases(cases) => {
                ComparisonOpExprBuilder::Cases(CasesBuilder::parse_ast(cases)?)
            }
            ComparisonOpExpr::Int { op, rhs } => ComparisonOpExprBuilder::Int {
                op: IntOpBuilder::parse_ast(op)?,
                rhs,
            },
            ComparisonOpExpr::IntVariable { op, var } => ComparisonOpExprBuilder::IntVariable {
                op: IntOpBuilder::parse_ast(op)?,
                var: VariableBuilder::parse_ast(var)?,
            },
            ComparisonOpExpr::Contains { rhs, variant: _ } => ComparisonOpExprBuilder::Contains {
                rhs: BytesBuilder::parse_ast(rhs)?,
            },
            ComparisonOpExpr::ContainsVariable { var, variant: _ } => {
                ComparisonOpExprBuilder::ContainsVariable {
                    var: VariableBuilder::parse_ast(var)?,
                }
            }
            ComparisonOpExpr::Matches { rhs, .. } => ComparisonOpExprBuilder::Matches {
                rhs: RegexBuilder::parse_ast(rhs)?,
            },
            ComparisonOpExpr::MatchesVariable { var, .. } => {
                ComparisonOpExprBuilder::MatchesVariable {
                    var: VariableBuilder::parse_ast(var)?,
                }
            }
            ComparisonOpExpr::OneOf { rhs, .. } => ComparisonOpExprBuilder::OneOf {
                rhs: RhsValuesBuilder::parse_ast(rhs)?,
            },
            ComparisonOpExpr::OneOfVariable { var, .. } => ComparisonOpExprBuilder::OneOfVariable {
                var: VariableBuilder::parse_ast(var)?,
            },
            ComparisonOpExpr::HasAny { rhs, .. } => ComparisonOpExprBuilder::HasAny {
                rhs: RhsValuesBuilder::parse_ast(rhs)?,
            },
            ComparisonOpExpr::HasAnyVariable { var, .. } => {
                ComparisonOpExprBuilder::HasAnyVariable {
                    var: VariableBuilder::parse_ast(var)?,
                }
            }
            ComparisonOpExpr::HasAll { rhs, .. } => ComparisonOpExprBuilder::HasAll {
                rhs: RhsValuesBuilder::parse_ast(rhs)?,
            },
            ComparisonOpExpr::HasAllVariable { var, .. } => {
                ComparisonOpExprBuilder::HasAllVariable {
                    var: VariableBuilder::parse_ast(var)?,
                }
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Cases<LogicalExpr<'s>>> for CasesBuilder<LogicalExprBuilder> {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<Cases<LogicalExpr<'s>>> {
        Ok(Cases {
            patterns: self
                .patterns
                .into_iter()
                .map(|(patterns, expr)| {
                    Ok((
                        patterns
                            .into_iter()
                            .map(|pattern| pattern.build(scheme, variables))
                            .collect::<Result<Vec<_>>>()?,
                        expr.build(scheme, variables)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
            variant: 0,
        })
    }

    fn parse_ast(cases: Cases<LogicalExpr<'s>>) -> Result<Self> {
        Ok(Self {
            patterns: cases
                .patterns
                .into_iter()
                .map(|(patterns, expr)| {
                    Ok((
                        patterns
                            .into_iter()
                            .map(CasePatternValueBuilder::parse_ast)
                            .collect::<Result<Vec<_>>>()?,
                        LogicalExprBuilder::parse_ast(expr)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Cases<IndexExpr<'s>>> for CasesBuilder<IndexExprBuilder> {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<Cases<IndexExpr<'s>>> {
        Ok(Cases {
            patterns: self
                .patterns
                .into_iter()
                .map(|(patterns, expr)| {
                    Ok((
                        patterns
                            .into_iter()
                            .map(|pattern| pattern.build(scheme, variables))
                            .collect::<Result<Vec<_>>>()?,
                        expr.build(scheme, variables)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
            variant: 0,
        })
    }

    fn parse_ast(cases: Cases<IndexExpr<'s>>) -> Result<Self> {
        Ok(Self {
            patterns: cases
                .patterns
                .into_iter()
                .map(|(patterns, expr)| {
                    Ok((
                        patterns
                            .into_iter()
                            .map(CasePatternValueBuilder::parse_ast)
                            .collect::<Result<Vec<_>>>()?,
                        IndexExprBuilder::parse_ast(expr)?,
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        })
    }
}

impl<'s, 'v, E: AstBuilder<'s, 'v, E>> CasesBuilder<E> {
    /// Creates a new `CasesBuilder` with the given `patterns`.
    pub fn new(patterns: Vec<(Vec<CasePatternValueBuilder>, E)>) -> Self {
        Self { patterns }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, OrderingOp> for OrderingOpBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<OrderingOp> {
        Ok(match self {
            OrderingOpBuilder::Equal => OrderingOp::Equal(0),
            OrderingOpBuilder::NotEqual => OrderingOp::NotEqual(0),
            OrderingOpBuilder::GreaterThanEqual => OrderingOp::GreaterThanEqual(0),
            OrderingOpBuilder::LessThanEqual => OrderingOp::LessThanEqual(0),
            OrderingOpBuilder::GreaterThan => OrderingOp::GreaterThan(0),
            OrderingOpBuilder::LessThan => OrderingOp::LessThan(0),
        })
    }

    fn parse_ast(ordering_op: OrderingOp) -> Result<Self> {
        Ok(match ordering_op {
            OrderingOp::Equal(_) => OrderingOpBuilder::Equal,
            OrderingOp::NotEqual(_) => OrderingOpBuilder::NotEqual,
            OrderingOp::GreaterThanEqual(_) => OrderingOpBuilder::GreaterThanEqual,
            OrderingOp::LessThanEqual(_) => OrderingOpBuilder::LessThanEqual,
            OrderingOp::GreaterThan(_) => OrderingOpBuilder::GreaterThan,
            OrderingOp::LessThan(_) => OrderingOpBuilder::LessThan,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, IndexExpr<'s>> for IndexExprBuilder {
    /// Builds a `IndexExpr` from the `IndexExprBuilder`.
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<IndexExpr<'s>> {
        Ok(IndexExpr {
            lhs: self.lhs.build(scheme, variables)?,
            indexes: self
                .indexes
                .into_iter()
                .map(|f| f.build(scheme, variables))
                .collect::<Result<_>>()?,
        })
    }

    /// Creates a new `IndexExprBuilder` from the given `IndexExpr`.
    fn parse_ast(index_expr: IndexExpr<'_>) -> Result<Self> {
        Ok(Self {
            lhs: LhsFieldExprBuilder::parse_ast(index_expr.lhs)?,
            indexes: index_expr
                .indexes
                .into_iter()
                .map(FieldIndexBuilder::parse_ast)
                .collect::<Result<_>>()?,
        })
    }
}

impl IndexExprBuilder {
    /// Creates a new `IndexExprBuilder` with the given `lhs` and `indexes`.
    pub fn new(lhs: LhsFieldExprBuilder, indexes: Vec<FieldIndexBuilder>) -> Self {
        Self { lhs, indexes }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, FieldIndex> for FieldIndexBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<FieldIndex> {
        Ok(match self {
            FieldIndexBuilder::ArrayIndex(index) => FieldIndex::ArrayIndex(index),
            FieldIndexBuilder::MapKey(key) => FieldIndex::MapKey(key),
            FieldIndexBuilder::MapEach => FieldIndex::MapEach,
        })
    }

    fn parse_ast(field_index: FieldIndex) -> Result<Self> {
        Ok(match field_index {
            FieldIndex::ArrayIndex(index) => FieldIndexBuilder::ArrayIndex(index),
            FieldIndex::MapKey(key) => FieldIndexBuilder::MapKey(key),
            FieldIndex::MapEach => FieldIndexBuilder::MapEach,
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, LhsFieldExpr<'s>> for LhsFieldExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<LhsFieldExpr<'s>> {
        match self {
            LhsFieldExprBuilder::Field(builder) => {
                Ok(LhsFieldExpr::Field(builder.build(scheme, variables)?))
            }
            LhsFieldExprBuilder::FunctionCallExpr(builder) => Ok(LhsFieldExpr::FunctionCallExpr(
                builder.build(scheme, variables)?,
            )),
        }
    }

    fn parse_ast(lhs_field_expr: LhsFieldExpr<'_>) -> Result<Self> {
        Ok(match lhs_field_expr {
            LhsFieldExpr::Field(field) => {
                LhsFieldExprBuilder::Field(FieldBuilder::parse_ast(field)?)
            }
            LhsFieldExpr::FunctionCallExpr(expr) => {
                LhsFieldExprBuilder::FunctionCallExpr(FunctionCallExprBuilder::parse_ast(expr)?)
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, FunctionCallExpr<'s>> for FunctionCallExprBuilder {
    fn build(self, scheme: &'s Scheme, variables: &'v Variables) -> Result<FunctionCallExpr<'s>> {
        Ok(FunctionCallExpr {
            function: self.function.build(scheme, variables)?,
            return_type: self.return_type.build(scheme, variables)?,
            args: self
                .args
                .into_iter()
                .map(|a| a.build(scheme, variables))
                .collect::<Result<Vec<_>>>()?,
            context: None,
        })
    }

    fn parse_ast(expr: FunctionCallExpr<'_>) -> Result<Self> {
        Ok(Self {
            function: FunctionBuilder::parse_ast(expr.function)?,
            return_type: TypeBuilder::parse_ast(expr.return_type)?,
            args: expr
                .args
                .into_iter()
                .map(FunctionCallArgExprBuilder::parse_ast)
                .collect::<Result<Vec<_>>>()?,
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
}

impl<'s, 'v> AstBuilder<'s, 'v, Type> for TypeBuilder {
    fn build(self, _scheme: &'s Scheme, _variables: &'v Variables) -> Result<Type> {
        Ok(match self {
            TypeBuilder::Bool => Type::Bool,
            TypeBuilder::Int => Type::Int,
            TypeBuilder::Float => Type::Float,
            TypeBuilder::Ip => Type::Ip,
            TypeBuilder::Bytes => Type::Bytes,
            TypeBuilder::Array(inner) => Type::Array(Box::new(inner.build(_scheme, _variables)?)),
            TypeBuilder::Map(inner) => Type::Map(Box::new(inner.build(_scheme, _variables)?)),
        })
    }

    fn parse_ast(ty: Type) -> Result<Self> {
        Ok(match ty {
            Type::Bool => TypeBuilder::Bool,
            Type::Int => TypeBuilder::Int,
            Type::Float => TypeBuilder::Float,
            Type::Ip => TypeBuilder::Ip,
            Type::Bytes => TypeBuilder::Bytes,
            Type::Array(inner) => TypeBuilder::Array(Box::new(TypeBuilder::parse_ast(*inner)?)),
            Type::Map(inner) => TypeBuilder::Map(Box::new(TypeBuilder::parse_ast(*inner)?)),
            _ => return Err(BuilderError::UnsupportedType(ty)),
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, FunctionCallArgExpr<'s>> for FunctionCallArgExprBuilder {
    fn build(
        self,
        scheme: &'s Scheme,
        variables: &'v Variables,
    ) -> Result<FunctionCallArgExpr<'s>> {
        Ok(match self {
            FunctionCallArgExprBuilder::IndexExpr(builder) => {
                FunctionCallArgExpr::IndexExpr(builder.build(scheme, variables)?)
            }
            FunctionCallArgExprBuilder::Literal(value) => {
                FunctionCallArgExpr::Literal(value.build(scheme, variables)?)
            }
            FunctionCallArgExprBuilder::SimpleExpr(builder) => {
                FunctionCallArgExpr::SimpleExpr(builder.build(scheme, variables)?)
            }
            FunctionCallArgExprBuilder::Variable(builder) => {
                FunctionCallArgExpr::Variable(builder.build(scheme, variables)?)
            }
        })
    }

    fn parse_ast(arg: FunctionCallArgExpr<'_>) -> Result<Self> {
        Ok(match arg {
            FunctionCallArgExpr::IndexExpr(expr) => {
                FunctionCallArgExprBuilder::IndexExpr(IndexExprBuilder::parse_ast(expr)?)
            }
            FunctionCallArgExpr::Literal(value) => {
                FunctionCallArgExprBuilder::Literal(RhsValueBuilder::parse_ast(value)?)
            }
            FunctionCallArgExpr::SimpleExpr(expr) => {
                FunctionCallArgExprBuilder::SimpleExpr(SimpleExprBuilder::parse_ast(expr)?)
            }
            FunctionCallArgExpr::Variable(variable) => {
                FunctionCallArgExprBuilder::Variable(VariableBuilder::parse_ast(variable)?)
            }
        })
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Function<'s>> for FunctionBuilder {
    fn build(self, scheme: &'s Scheme, _variables: &'v Variables) -> Result<Function<'s>> {
        Ok(scheme.get_function(&self.name)?)
    }

    fn parse_ast(function: Function<'_>) -> Result<Self> {
        Ok(Self {
            name: function.name().to_string(),
        })
    }
}

impl FunctionBuilder {
    /// Creates a new `FunctionBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Variable> for VariableBuilder {
    fn build(self, _scheme: &'s Scheme, variables: &'v Variables) -> Result<Variable> {
        if let Some(variable_value) = variables.get(&self.name) {
            Ok(Variable::new_with_type(
                self.name,
                variable_value.get_variable_type(),
            ))
        } else {
            Err(BuilderError::VariableNotFound(UnknownVariableError))
        }
    }

    fn parse_ast(variable: Variable) -> Result<Self> {
        Ok(Self {
            name: variable.take_name().to_string(),
        })
    }
}

impl VariableBuilder {
    /// Creates a new `VariableBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl<'s, 'v> AstBuilder<'s, 'v, Field<'s>> for FieldBuilder {
    fn build(self, scheme: &'s Scheme, _variables: &Variables) -> Result<Field<'s>> {
        Ok(scheme.get_field(&self.name)?)
    }

    fn parse_ast(field: Field<'s>) -> Result<Self> {
        Ok(Self {
            name: field.name().to_string(),
        })
    }
}

impl FieldBuilder {
    /// Creates a new `FieldBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }
}
