import enum
from typing import List, Tuple, Union, Dict, Any


class FilterAstBuilder:
    """
    Builder for `FilterAst`.
    """

    def __init__(self, op: "LogicalExprBuilder"):
        self.op = op

    def to_json(self) -> Dict[str, Any]:
        return {"op": self.op.to_json()}


class SingleValueExprAstBuilder:
    """
    Builder for `SingleValueExprAst`.
    """

    def __init__(self, op: "LhsFieldExprBuilder"):
        self.op = op

    def to_json(self) -> Dict[str, Any]:
        return {"op": self.op.to_json()}


class LogicalExprBuilder:
    """
    Builder for `LogicalExprAst`.
    pub enum LogicalExprBuilder {
        /// Sub-expression
        Simple(SimpleExprBuilder),
        /// Logical conjunction expression
        Combining(CombiningExprBuilder),
    }
    """

    def __init__(
        self,
        Simple: "None | SimpleExprBuilder" = None,
        Combining: "None | CombiningExprBuilder" = None,
    ):
        self.Simple = Simple
        self.Combining = Combining

    def to_json(self) -> Dict[str, Any]:
        if self.Simple is not None:
            return {"Simple": self.Simple.to_json()}
        elif self.Combining is not None:
            return {"Combining": self.Combining.to_json()}
        else:
            raise ValueError("No valid field set")


class CombiningExprBuilder:
    """
    Builder for `CombiningExpr`.
    pub struct CombiningExprBuilder {
        /// Logical operator
        pub(crate) op: LogicalOpBuilder,
        /// List of sub-expressions
        pub(crate) items: Vec<LogicalExprBuilder>,
    }
    """

    def __init__(self, op: "LogicalOpBuilder", items: List["LogicalExprBuilder"]):
        self.op = op
        self.items = items

    def to_json(self) -> Dict[str, Any]:
        return {
            "op": self.op.to_json(),
            "items": [item.to_json() for item in self.items],
        }


class LogicalOpBuilder(enum.Enum):
    """
    Builder for `LogicalOp`.
    pub enum LogicalOpBuilder {
        /// Logical OR
        Or,
        /// Logical XOR
        Xor,
        /// Logical AND
        And,
    }
    """

    Or = "Or"
    Xor = "Xor"
    And = "And"

    def to_json(self) -> str:
        return self.value


class SimpleExprBuilder:
    """
    Builder for `SimpleExpr`.
    pub enum SimpleExprBuilder {
        /// A comparison expression.
        Comparison(ComparisonExprBuilder),
        /// A parenthisized expression.
        Parenthesized(Box<LogicalExprBuilder>),
        /// A unary expression.
        Unary(UnaryExprBuilder),
    }
    """

    def __init__(
        self,
        Comparison: "None | ComparisonExprBuilder" = None,
        Parenthesized: "None | LogicalExprBuilder" = None,
        Unary: "None | UnaryExprBuilder" = None,
    ):
        self.Comparison = Comparison
        self.Parenthesized = Parenthesized
        self.Unary = Unary

    def to_json(self) -> Dict[str, Any]:
        if self.Comparison is not None:
            return {"Comparison": self.Comparison.to_json()}
        elif self.Parenthesized is not None:
            return {"Parenthesized": self.Parenthesized.to_json()}
        elif self.Unary is not None:
            return {"Unary": self.Unary.to_json()}
        else:
            raise ValueError("No valid field set")


class UnaryExprBuilder:
    """
    Builder for `UnaryExpr`.
    pub struct UnaryExprBuilder {
        /// Unary operator.
        pub(crate) op: UnaryOpBuilder,
        /// Sub-expression.
        pub(crate) arg: Box<SimpleExprBuilder>,
    }
    """

    def __init__(self, op: "UnaryOpBuilder", arg: "SimpleExprBuilder"):
        self.op = op
        self.arg = arg

    def to_json(self) -> Dict[str, Any]:
        return {"op": self.op.to_json(), "arg": self.arg.to_json()}


class UnaryOpBuilder(enum.Enum):
    """
    Builder for `UnaryOp`.
    pub enum UnaryOpBuilder {
        /// Logical NOT
        Not,
    }
    """

    Not = "Not"

    def to_json(self) -> str:
        return self.value


class ComparisonExprBuilder:
    """
    Builder for `ComparisonExpr`.
    pub struct ComparisonExprBuilder {
        pub(crate) lhs: IndexExprBuilder,
        pub(crate) op: ComparisonOpExprBuilder,
    }
    """

    def __init__(self, lhs: "IndexExprBuilder", op: "ComparisonOpExprBuilder"):
        self.lhs = lhs
        self.op = op

    def to_json(self) -> Dict[str, Any]:
        return {"lhs": self.lhs.to_json(), "op": self.op.to_json()}


class ComparisonOpExprBuilder:
    """
    Builder for `ComparisonOpExpr`.
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

        /// "cases {...}" / "CASES {...}" / "=> {...}" comparison
        Cases {
            /// Cases patterns
            patterns: Vec<(Vec<CasePatternValueBuilder>, LogicalExprBuilder)>,
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
    """

    def __init__(
        self,
        IsTrue: None | bool = None,
        Ordering: None | Tuple["OrderingOpBuilder", "RhsValueBuilder"] = None,
        OrderingVariable: None | Tuple["OrderingOpBuilder", "VariableBuilder"] = None,
        Cases: (
            None | List[Tuple[List["CasePatternValueBuilder"], "LogicalExprBuilder"]]
        ) = None,
        Int: None | Tuple["IntOpBuilder", int] = None,
        IntVariable: None | Tuple["IntOpBuilder", "VariableBuilder"] = None,
        Contains: "None | BytesBuilder" = None,
        ContainsVariable: "None | VariableBuilder" = None,
        Matches: "None | RegexBuilder" = None,
        MatchesVariable: "None | VariableBuilder" = None,
        OneOf: "None | RhsValuesBuilder" = None,
        OneOfVariable: "None | VariableBuilder" = None,
        HasAny: "None | RhsValuesBuilder" = None,
        HasAnyVariable: "None | VariableBuilder" = None,
        HasAll: "None | RhsValuesBuilder" = None,
        HasAllVariable: "None | VariableBuilder" = None,
    ):
        self.IsTrue = IsTrue
        self.Ordering = Ordering
        self.OrderingVariable = OrderingVariable
        self.Cases = Cases
        self.Int = Int
        self.IntVariable = IntVariable
        self.Contains = Contains
        self.ContainsVariable = ContainsVariable
        self.Matches = Matches
        self.MatchesVariable = MatchesVariable
        self.OneOf = OneOf
        self.OneOfVariable = OneOfVariable
        self.HasAny = HasAny
        self.HasAnyVariable = HasAnyVariable
        self.HasAll = HasAll
        self.HasAllVariable = HasAllVariable

    def to_json(self) -> Dict[str, Any] | str:
        if self.IsTrue is not None:
            return "IsTrue"
        elif self.Ordering is not None:
            return {
                "Ordering": {
                    "op": self.Ordering[0].to_json(),
                    "rhs": self.Ordering[1].to_json(),
                }
            }
        elif self.OrderingVariable is not None:
            return {
                "OrderingVariable": {
                    "op": self.OrderingVariable[0].to_json(),
                    "var": self.OrderingVariable[1].to_json(),
                }
            }
        elif self.Cases is not None:
            return {
                "Cases": {
                    "patterns": [
                        ([pattern.to_json() for pattern in patterns], expr.to_json())
                        for patterns, expr in self.Cases
                    ]
                }
            }
        elif self.Int is not None:
            return {"Int": {"op": self.Int[0].to_json(), "rhs": self.Int[1]}}
        elif self.IntVariable is not None:
            return {
                "IntVariable": {
                    "op": self.IntVariable[0].to_json(),
                    "var": self.IntVariable[1].to_json(),
                }
            }
        elif self.Contains is not None:
            return {
                "Contains": {
                    "rhs": self.Contains.to_json(),
                }
            }
        elif self.ContainsVariable is not None:
            return {
                "ContainsVariable": {
                    "var": self.ContainsVariable.to_json(),
                }
            }
        elif self.Matches is not None:
            return {
                "Matches": {
                    "rhs": self.Matches.to_json(),
                }
            }
        elif self.MatchesVariable is not None:
            return {
                "MatchesVariable": {
                    "var": self.MatchesVariable.to_json(),
                }
            }
        elif self.OneOf is not None:
            return {"OneOf": {"rhs": self.OneOf.to_json()}}
        elif self.OneOfVariable is not None:
            return {"OneOfVariable": {"var": self.OneOfVariable.to_json()}}
        elif self.HasAny is not None:
            return {"HasAny": {"rhs": self.HasAny.to_json()}}
        elif self.HasAnyVariable is not None:
            return {"HasAnyVariable": {"var": self.HasAnyVariable.to_json()}}
        elif self.HasAll is not None:
            return {"HasAll": {"rhs": self.HasAll.to_json()}}
        elif self.HasAllVariable is not None:
            return {"HasAllVariable": {"var": self.HasAllVariable.to_json()}}
        else:
            raise ValueError("No valid field set")


class RegexBuilder:
    """
    Builder for `Regex`.
    pub struct RegexBuilder {
        /// Regex value.
        pub(crate) value: String,
        /// Type of string literal.
        pub(crate) ty: StrTypeBuilder,
    }
    """

    def __init__(self, value: str, ty: "StrTypeBuilder"):
        self.value = value
        self.ty = ty

    def to_json(self) -> Dict[str, Any]:
        return {"value": self.value, "ty": self.ty.to_json()}


class BytesBuilder:
    """
    Builder for `Bytes`.
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
    """

    def __init__(
        self,
        Str: None | Tuple[str, "StrTypeBuilder"] = None,
        Raw: None | Tuple[List[int], "ByteSeparatorBuilder"] = None,
    ):
        self.Str = Str
        self.Raw = Raw

    def to_json(self) -> Dict[str, Any]:
        if self.Str is not None:
            return {"Str": {"value": self.Str[0], "ty": self.Str[1].to_json()}}
        elif self.Raw is not None:
            return {"Raw": {"value": self.Raw[0], "separator": self.Raw[1].to_json()}}
        else:
            raise ValueError("No valid field set")


class StrTypeBuilder:
    """
    Builder for `StrType`.
    pub enum StrTypeBuilder {
        /// Raw string literal.
        Raw {
            /// Number of `#` characters in the opening and closing delimiter.
            hash_count: usize,
        },
        /// Escaped string literal.
        Escaped,
    }
    """

    def __init__(self, Raw: None | int = None, Escaped: None | bool = None):
        self.Raw = Raw
        self.Escaped = Escaped

    def to_json(self) -> Dict | str:
        if self.Raw is not None:
            return {"Raw": {"hash_count": self.Raw}}
        elif self.Escaped is not None:
            return "Escaped"
        else:
            raise ValueError("No valid field set")


class ByteSeparatorBuilder(enum.Enum):
    """
    Builder for `ByteSeparator`.
    pub enum ByteSeparatorBuilder {
        /// Colon separator.
        Colon,
        /// Dash separator.
        Dash,
        /// Dot separator.
        Dot,
    }
    """

    Colon = "Colon"
    Dash = "Dash"
    Dot = "Dot"

    def to_json(self) -> str:
        return self.value


class IntOpBuilder(enum.Enum):
    """
    Builder for `IntOp`.
    pub enum IntOpBuilder {
        /// "&" | "bitwise_and" | "BITWISE_AND"
        BitwiseAnd,
    }
    """

    BitwiseAnd = "BitwiseAnd"

    def to_json(self) -> str:
        return self.value


class RhsValueBuilder:
    """
    Builder for `RhsValue`.
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
    """

    def __init__(
        self,
        Int: None | int = None,
        Float: None | float = None,
        Ip: None | str = None,
        Bytes: "None | BytesBuilder" = None,
    ):
        self.Int = Int
        self.Float = Float
        self.Ip = Ip
        self.Bytes = Bytes

    def to_json(self) -> Dict[str, Any]:
        if self.Int is not None:
            return {"Int": self.Int}
        elif self.Float is not None:
            return {"Float": self.Float}
        elif self.Ip is not None:
            return {"Ip": self.Ip}
        elif self.Bytes is not None:
            return {"Bytes": self.Bytes.to_json()}
        else:
            raise ValueError("No valid field set")


class RhsValuesBuilder:
    """
    Builder for `RhsValues`.
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
    """

    def __init__(
        self,
        Int: None | List[Tuple[int, int]] = None,
        Float: None | List[Tuple[float, float]] = None,
        Ip: None | List["IpRangeBuilder"] = None,
        Bytes: None | List["BytesBuilder"] = None,
    ):
        self.Int = Int
        self.Float = Float
        self.Ip = Ip
        self.Bytes = Bytes

    def to_json(self) -> Dict[str, Any]:
        if self.Int is not None:
            return {"Int": [(start, end) for start, end in self.Int]}
        elif self.Float is not None:
            return {"Float": [(start, end) for start, end in self.Float]}
        elif self.Ip is not None:
            return {"Ip": [ip.to_json() for ip in self.Ip]}
        elif self.Bytes is not None:
            return {"Bytes": [bytes.to_json() for bytes in self.Bytes]}
        else:
            raise ValueError("No valid field set")


class CasePatternValueBuilder:
    """
    /// Builder for `CasePatternValue`.
    pub enum CasePatternValueBuilder {
        /// A boolean.
        Bool,
        /// A 32-bit integer number.
        Int(i32),
        /// Represents a range of integers.
        IntRange((i32, i32)),
        /// A 64-bit floating point number.
        Float(f64),
        /// Represents a range of floating point numbers.
        FloatRange((f64, f64)),
        /// An IPv4 or IPv6 address.
        ///
        /// These are represented as a single type to allow interop comparisons.
        Ip(IpAddr),
        /// Represents a range of IP addresses.
        IpRange(IpRangeBuilder),
        /// A raw bytes or a string field.
        ///
        /// These are completely interchangeable in runtime and differ only in
        /// syntax representation, so we represent them as a single type.
        Bytes(BytesBuilder),
    }
    """

    def __init__(
        self,
        Bool: None | bool = None,
        Int: None | int = None,
        IntRange: None | Tuple[int, int] = None,
        Float: None | float = None,
        FloatRange: None | Tuple[float, float] = None,
        Ip: None | str = None,
        IpRange: "None | IpRangeBuilder" = None,
        Bytes: "None | BytesBuilder" = None,
    ):
        self.Bool = Bool
        self.Int = Int
        self.IntRange = IntRange
        self.Float = Float
        self.FloatRange = FloatRange
        self.Ip = Ip
        self.IpRange = IpRange
        self.Bytes = Bytes

    def to_json(self) -> str | Dict[str, Any]:
        if self.Bool is not None:
            return "Bool"
        elif self.Int is not None:
            return {"Int": self.Int}
        elif self.IntRange is not None:
            return {"IntRange": self.IntRange}
        elif self.Float is not None:
            return {"Float": self.Float}
        elif self.FloatRange is not None:
            return {"FloatRange": self.FloatRange}
        elif self.Ip is not None:
            return {"Ip": self.Ip}
        elif self.IpRange is not None:
            return {"IpRange": self.IpRange.to_json()}
        elif self.Bytes is not None:
            return {"Bytes": self.Bytes.to_json()}
        else:
            raise ValueError("No valid field set")


class IpRangeBuilder:
    """
    Builder for `IpRange`.
    pub enum IpRangeBuilder {
        /// Explicit range of IP addresses.
        Explicit(ExplicitIpRangeBuilder),
        /// CIDR range of IP addresses.
        Cidr(IpCidrBuilder),
    }
    """

    def __init__(
        self,
        Explicit: "None | ExplicitIpRangeBuilder" = None,
        Cidr: "None | IpCidrBuilder" = None,
    ):
        self.Explicit = Explicit
        self.Cidr = Cidr

    def to_json(self) -> Dict[str, Any]:
        if self.Explicit is not None:
            return {"Explicit": self.Explicit.to_json()}
        elif self.Cidr is not None:
            return {"Cidr": self.Cidr.to_json()}
        else:
            raise ValueError("No valid field set")


class ExplicitIpRangeBuilder:
    """
    Builder for `ExplicitIpRange`.
    pub enum ExplicitIpRangeBuilder {
        /// An explicit range of IPv4 addresses.
        V4((Ipv4Addr, Ipv4Addr)),
        /// An explicit range of IPv6 addresses.
        V6((Ipv6Addr, Ipv6Addr)),
    }
    """

    def __init__(
        self, V4: None | Tuple[str, str] = None, V6: None | Tuple[str, str] = None
    ):
        self.V4 = V4
        self.V6 = V6

    def to_json(self) -> Dict[str, Any]:
        if self.V4 is not None:
            return {"V4": self.V4}
        elif self.V6 is not None:
            return {"V6": self.V6}
        else:
            raise ValueError("No valid field set")


class IpCidrBuilder:
    """
    Builder for `IpCidr`.
    pub struct IpCidrBuilder(pub IpAddr, pub u8);
    """

    def __init__(self, IpAddr: str, u8: int):
        self.IpAddr = IpAddr
        self.u8 = u8

    def to_json(self) -> tuple[str, int]:
        return (self.IpAddr, self.u8)


class OrderingOpBuilder(enum.Enum):
    """
    Builder for `OrderingOp`.
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
    """

    Equal = "Equal"
    NotEqual = "NotEqual"
    GreaterThanEqual = "GreaterThanEqual"
    LessThanEqual = "LessThanEqual"
    GreaterThan = "GreaterThan"
    LessThan = "LessThan"

    def to_json(self) -> str:
        return self.value


class IndexExprBuilder:
    """
    Builder for `IndexExpr`.
    pub struct IndexExprBuilder {
        /// Left-hand side of the index expression.
        pub lhs: LhsFieldExprBuilder,
        /// Indexes to access the value.
        pub indexes: Vec<FieldIndexBuilder>,
    }
    """

    def __init__(self, lhs: "LhsFieldExprBuilder", indexes: List["FieldIndexBuilder"]):
        self.lhs = lhs
        self.indexes = indexes

    def to_json(self) -> Dict[str, Any]:
        return {
            "lhs": self.lhs.to_json(),
            "indexes": [index.to_json() for index in self.indexes],
        }


class FieldIndexBuilder:
    """
    Builder for `FieldIndex`.
    pub enum FieldIndexBuilder {
        /// Index into an Array
        ArrayIndex(u32),
        /// Key into a Map
        MapKey(String),
        /// Map each element by applying a function or a comparison
        MapEach,
    }
    """

    def __init__(
        self,
        ArrayIndex: None | int = None,
        MapKey: None | str = None,
        MapEach: None | bool = None,
    ):
        self.ArrayIndex = ArrayIndex
        self.MapKey = MapKey
        self.MapEach = MapEach

    def to_json(self) -> Dict | str:
        if self.ArrayIndex is not None:
            return {"ArrayIndex": self.ArrayIndex}
        elif self.MapKey is not None:
            return {"MapKey": self.MapKey}
        elif self.MapEach is not None:
            return "MapEach"
        else:
            raise ValueError("No valid field set")


class LhsFieldExprBuilder:
    """
    Builder for `LhsFieldExpr`.
    pub enum LhsFieldExprBuilder {
        /// Field expression
        Field(FieldBuilder),
        /// Function call expression
        FunctionCallExpr(FunctionCallExprBuilder),
    }
    """

    def __init__(
        self,
        Field: "None | FieldBuilder" = None,
        FunctionCallExpr: "None | FunctionCallExprBuilder" = None,
    ):
        self.Field = Field
        self.FunctionCallExpr = FunctionCallExpr

    def to_json(self) -> Dict[str, Any]:
        if self.Field is not None:
            return {"Field": self.Field.to_json()}
        elif self.FunctionCallExpr is not None:
            return {"FunctionCallExpr": self.FunctionCallExpr.to_json()}
        else:
            raise ValueError("No valid field set")


class FunctionCallExprBuilder:
    """
    Builder for `FunctionCallExpr`.
    pub struct FunctionCallExprBuilder {
        /// Function being called.
        pub function: FunctionBuilder,
        /// Return type of the function.
        pub return_type: TypeBuilder,
        /// Arguments of the function.
        pub args: Vec<FunctionCallArgExprBuilder>,
    }
    """

    def __init__(
        self,
        function: "FunctionBuilder",
        return_type: "TypeBuilder",
        args: List["FunctionCallArgExprBuilder"],
    ):
        self.function = function
        self.return_type = return_type
        self.args = args

    def to_json(self) -> Dict[str, Any]:
        return {
            "function": self.function.to_json(),
            "return_type": self.return_type.to_json(),
            "args": [arg.to_json() for arg in self.args],
        }


class TypeBuilder:
    """
    Builder for `Type`.
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
    """

    def __init__(
        self,
        Bool: None | bool = None,
        Int: None | bool = None,
        Float: None | bool = None,
        Ip: None | bool = None,
        Bytes: None | bool = None,
        Array: "None | TypeBuilder" = None,
        Map: "None | TypeBuilder" = None,
    ):
        self.Bool = Bool
        self.Int = Int
        self.Float = Float
        self.Ip = Ip
        self.Bytes = Bytes
        self.Array = Array
        self.Map = Map

    def to_json(self) -> Dict | str:
        if self.Bool is not None:
            return "Bool"
        elif self.Int is not None:
            return "Int"
        elif self.Float is not None:
            return "Float"
        elif self.Ip is not None:
            return "Ip"
        elif self.Bytes is not None:
            return "Bytes"
        elif self.Array is not None:
            return {"Array": self.Array.to_json()}
        elif self.Map is not None:
            return {"Map": self.Map.to_json()}
        else:
            raise ValueError("No valid field set")


class FunctionCallArgExprBuilder:
    """
    Builder for `FunctionCallArgExpr`.
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
    """

    def __init__(
        self,
        IndexExpr: "None | IndexExprBuilder" = None,
        Literal: "None | RhsValueBuilder" = None,
        SimpleExpr: "None | SimpleExprBuilder" = None,
        Variable: "None | VariableBuilder" = None,
    ):
        self.IndexExpr = IndexExpr
        self.Literal = Literal
        self.SimpleExpr = SimpleExpr
        self.Variable = Variable

    def to_json(self) -> Dict[str, Any]:
        if self.IndexExpr is not None:
            return {"IndexExpr": self.IndexExpr.to_json()}
        elif self.Literal is not None:
            return {"Literal": self.Literal.to_json()}
        elif self.SimpleExpr is not None:
            return {"SimpleExpr": self.SimpleExpr.to_json()}
        elif self.Variable is not None:
            return {"Variable": self.Variable.to_json()}
        else:
            raise ValueError("No valid field set")


class VariableBuilder:
    """
    Builder for `Variable`.
    pub struct VariableBuilder {
        /// Name of the variable.
        pub name: String,
    }
    """

    def __init__(self, name: str):
        self.name = name

    def to_json(self) -> Dict[str, Any]:
        return {"name": self.name}


class FunctionBuilder:
    """
    Builder for `Function`.
    pub struct FunctionBuilder {
        /// Name of the function.
        pub name: String,
    }
    """

    def __init__(self, name: str):
        self.name = name

    def to_json(self) -> Dict[str, Any]:
        return {"name": self.name}


class FieldBuilder:
    """
    Builder for `Field`.
    pub struct FieldBuilder {
        /// Name of the field.
        pub name: String,
    }
    """

    def __init__(self, name: str):
        self.name = name

    def to_json(self) -> Dict[str, Any]:
        return {"name": self.name}
