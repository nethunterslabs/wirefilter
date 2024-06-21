//! AST builder implementations for WireFilter.

use std::net::IpAddr;

use cidr::IpCidr;
use wirefilter::{
    ByteSeparator, Bytes, ComparisonExpr, ComparisonOpExpr, ExplicitIpRange, FieldIndex, FilterAst,
    FloatRange, Function, FunctionCallArgExpr, FunctionCallExpr, IndexExpr, IntOp, IntRange,
    IpRange, LhsFieldExpr, LogicalExpr, LogicalOp, OrderedFloat, OrderingOp, Regex, RhsValue,
    RhsValues, Scheme, SimpleExpr, SingleValueExprAst, StrType, Type, UnaryOp, VariableRef,
};

use crate::ast::*;
use crate::Result;

impl FilterAstBuilder {
    /// Creates a new `FilterAstBuilder` with the given root `LogicalExprBuilder`.
    pub fn new(op: LogicalExprBuilder) -> Self {
        Self { op }
    }

    /// Builds a `FilterAst` from the `FilterAstBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<FilterAst<'_>> {
        Ok(FilterAst {
            scheme,
            op: self.op.build(scheme)?,
        })
    }
}

impl SingleValueExprAstBuilder {
    /// Creates a new `SingleValueExprAstBuilder` with the given root `LhsFieldExprBuilder`.
    pub fn new(op: LhsFieldExprBuilder) -> Self {
        Self { op }
    }

    /// Builds a `SingleValueExprAst` from the `SingleValueExprAstBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<SingleValueExprAst<'_>> {
        Ok(SingleValueExprAst {
            scheme,
            op: self.op.build(scheme)?,
        })
    }
}

impl LogicalExprBuilder {
    /// Builds a `LogicalExprAst` from the `LogicalExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<LogicalExpr<'_>> {
        match self {
            LogicalExprBuilder::Simple(builder) => Ok(LogicalExpr::Simple(builder.build(scheme)?)),
            LogicalExprBuilder::Combining(builder) => builder.build(scheme),
        }
    }
}

impl CombiningExprBuilder {
    /// Creates a new `CombiningExprBuilder` with the given `op` and `items`.
    pub fn new(op: LogicalOpBuilder, items: Vec<LogicalExprBuilder>) -> Self {
        Self { op, items }
    }

    /// Builds a `CombiningExpr` from the `CombiningExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<LogicalExpr<'_>> {
        Ok(LogicalExpr::Combining {
            op: self.op.build(),
            items: self
                .items
                .into_iter()
                .map(|i| i.build(scheme))
                .collect::<Result<Vec<_>>>()?,
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
}

impl SimpleExprBuilder {
    /// Builds a `SimpleExprAst` from the `SimpleExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<SimpleExpr> {
        match self {
            SimpleExprBuilder::Comparison(builder) => {
                Ok(SimpleExpr::Comparison(builder.build(scheme)?))
            }
            SimpleExprBuilder::Parenthesized(builder) => {
                Ok(SimpleExpr::Parenthesized(Box::new(builder.build(scheme)?)))
            }
            SimpleExprBuilder::Unary(builder) => builder.build(scheme),
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

    /// Builds a `UnaryExpr` from the `UnaryExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<SimpleExpr> {
        Ok(SimpleExpr::Unary {
            op: self.op.build(),
            arg: Box::new(self.arg.build(scheme)?),
        })
    }
}

impl UnaryOpBuilder {
    /// Builds a `UnaryOp` from the `UnaryOpBuilder`.
    pub fn build(self) -> UnaryOp {
        match self {
            UnaryOpBuilder::Not => UnaryOp::Not(0),
        }
    }
}

impl ComparisonExprBuilder {
    /// Creates a new `ComparisonExprBuilder` with the given `lhs` and `op`.
    pub fn new(lhs: IndexExprBuilder, op: ComparisonOpExprBuilder) -> Self {
        Self { lhs, op }
    }

    /// Builds a `ComparisonExpr` from the `ComparisonExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<ComparisonExpr> {
        Ok(ComparisonExpr {
            lhs: self.lhs.build(scheme)?,
            op: self.op.build(scheme)?,
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
        Ok(Regex::parse_str_with_str_type(&self.value, self.ty.build())?)
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
}

impl StrTypeBuilder {
    /// Builds a `StrType` from the `StrTypeBuilder`.
    pub fn build(self) -> StrType {
        match self {
            StrTypeBuilder::Raw { hash_count } => StrType::Raw { hash_count },
            StrTypeBuilder::Escaped => StrType::Escaped,
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
}

impl IntOpBuilder {
    /// Builds a `IntOp` from the `IntOpBuilder`.
    pub fn build(self) -> IntOp {
        match self {
            IntOpBuilder::BitwiseAnd => IntOp::BitwiseAnd(0),
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
}

impl IpRangeBuilder {
    /// Builds a `IpRange` from the `IpRangeBuilder`.
    pub fn build(self) -> Result<IpRange> {
        Ok(match self {
            IpRangeBuilder::Explicit(builder) => IpRange::Explicit(builder.build()),
            IpRangeBuilder::Cidr(builder) => IpRange::Cidr(builder.build()?),
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
}

impl ComparisonOpExprBuilder {
    /// Builds a `ComparisonOpExpr` from the `ComparisonOpExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<ComparisonOpExpr<'_>> {
        Ok(match self {
            ComparisonOpExprBuilder::IsTrue => ComparisonOpExpr::IsTrue,
            ComparisonOpExprBuilder::Ordering { op, rhs } => ComparisonOpExpr::Ordering {
                op: op.build(),
                rhs: rhs.build(),
            },
            ComparisonOpExprBuilder::OrderingVariable { op, var } => {
                ComparisonOpExpr::OrderingVariable {
                    op: op.build(),
                    var: var.build(scheme)?,
                }
            }
            ComparisonOpExprBuilder::Int { op, rhs } => ComparisonOpExpr::Int {
                op: op.build(),
                rhs,
            },
            ComparisonOpExprBuilder::IntVariable { op, var } => ComparisonOpExpr::IntVariable {
                op: op.build(),
                var: var.build(scheme)?,
            },
            ComparisonOpExprBuilder::Contains { rhs } => ComparisonOpExpr::Contains {
                rhs: rhs.build(),
                variant: 0,
            },
            ComparisonOpExprBuilder::ContainsVariable { var } => {
                ComparisonOpExpr::ContainsVariable {
                    var: var.build(scheme)?,
                    variant: 0,
                }
            }
            ComparisonOpExprBuilder::Matches { rhs } => ComparisonOpExpr::Matches {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::MatchesVariable { var } => ComparisonOpExpr::MatchesVariable {
                var: var.build(scheme)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::OneOf { rhs } => ComparisonOpExpr::OneOf {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::OneOfVariable { var } => ComparisonOpExpr::OneOfVariable {
                var: var.build(scheme)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAny { rhs } => ComparisonOpExpr::HasAny {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAnyVariable { var } => ComparisonOpExpr::HasAnyVariable {
                var: var.build(scheme)?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAll { rhs } => ComparisonOpExpr::HasAll {
                rhs: rhs.build()?,
                variant: 0,
            },
            ComparisonOpExprBuilder::HasAllVariable { var } => ComparisonOpExpr::HasAllVariable {
                var: var.build(scheme)?,
                variant: 0,
            },
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
}

impl IndexExprBuilder {
    /// Creates a new `IndexExprBuilder` with the given `lhs` and `indexes`.
    pub fn new(lhs: LhsFieldExprBuilder, indexes: Vec<FieldIndexBuilder>) -> Self {
        Self { lhs, indexes }
    }

    /// Builds a `IndexExpr` from the `IndexExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<IndexExpr<'_>> {
        Ok(IndexExpr {
            lhs: self.lhs.build(scheme)?,
            indexes: self
                .indexes
                .into_iter()
                .map(FieldIndexBuilder::build)
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
}

impl LhsFieldExprBuilder {
    /// Builds a `LhsFieldExpr` from the `LhsFieldExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<LhsFieldExpr<'_>> {
        match self {
            LhsFieldExprBuilder::Field(builder) => Ok(LhsFieldExpr::Field(builder.build(scheme)?)),
            LhsFieldExprBuilder::FunctionCallExpr(builder) => {
                Ok(LhsFieldExpr::FunctionCallExpr(builder.build(scheme)?))
            }
        }
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
    pub fn build(self, scheme: &Scheme) -> Result<FunctionCallExpr<'_>> {
        Ok(FunctionCallExpr {
            function: self.function.build(scheme)?,
            return_type: self.return_type.build(),
            args: self
                .args
                .into_iter()
                .map(|a| a.build(scheme))
                .collect::<Result<Vec<_>>>()?,
            context: None,
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
}

impl FunctionCallArgExprBuilder {
    /// Builds a `FunctionCallArgExpr` from the `FunctionCallArgExprBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<FunctionCallArgExpr<'_>> {
        Ok(match self {
            FunctionCallArgExprBuilder::IndexExpr(builder) => {
                FunctionCallArgExpr::IndexExpr(builder.build(scheme)?)
            }
            FunctionCallArgExprBuilder::Literal(value) => {
                FunctionCallArgExpr::Literal(value.build())
            }
            FunctionCallArgExprBuilder::SimpleExpr(builder) => {
                FunctionCallArgExpr::SimpleExpr(builder.build(scheme)?)
            }
            FunctionCallArgExprBuilder::Variable(builder) => {
                FunctionCallArgExpr::Variable(builder.build(scheme)?)
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
}

impl VariableBuilder {
    /// Creates a new `VariableBuilder` with the given `name`.
    pub fn new(name: String) -> Self {
        Self { name }
    }

    /// Builds a `Function` from the `VariableBuilder`.
    pub fn build(self, scheme: &Scheme) -> Result<VariableRef<'_>> {
        Ok(scheme.get_variable_ref(&self.name)?)
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
}
