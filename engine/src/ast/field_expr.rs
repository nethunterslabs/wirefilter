use super::{
    function_expr::FunctionCallExpr,
    visitor::{Visitor, VisitorMut},
    Expr, ValueExpr,
};
use crate::{
    ast::{index_expr::IndexExpr, logical_expr::LogicalExpr},
    compiler::Compiler,
    execution_context::{ExecutionContext, State, Variables},
    filter::{CompiledExpr, CompiledValueExpr, CompiledValueResult},
    lex::{expect, skip_space, span, Lex, LexErrorKind, LexResult, LexWith, LexWith2},
    like::Like,
    range_set::{RangeSet, RangeSetWithId},
    rhs_types::{Bytes, ExplicitIpRange, Regex, Variable},
    scheme::{Field, Identifier, Scheme},
    searcher::{EmptySearcher, TwoWaySearcher},
    strict_partial_ord::StrictPartialOrd,
    types::{
        CasePatternValue, GetType, LhsValue, RhsValue, RhsValues, Type, TypeMismatchError,
        VariableValue,
    },
};
use aho_corasick::AhoCorasickBuilder;
use fnv::FnvBuildHasher;
use indexmap::IndexSet;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use lazy_static::lazy_static;
use serde::{Serialize, Serializer};
use sliceslice::MemchrSearcher;
use std::{
    cmp::Ordering,
    net::{IpAddr, Ipv4Addr, Ipv6Addr},
};

const LESS: u8 = 0b001;
const GREATER: u8 = 0b010;
const EQUAL: u8 = 0b100;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
lazy_static! {
    static ref USE_AVX2: bool = {
        use std::env;

        const NO_VALUES: &[&str] = &["0", "no", "false"];

        let use_avx2 = env::var("WIREFILTER_USE_AVX2").unwrap_or_default();
        is_x86_feature_detected!("avx2") && !NO_VALUES.contains(&use_avx2.as_str())
    };
}

lex_enum!(
    /// OrderingOp is an operator for an ordering [`ComparisonOpExpr`].
    #[repr(u8)] OrderingOp {
        /// `eq` / `EQ` / `==` operator
        "eq" | "EQ" | "==" => Equal = EQUAL,
        /// `ne`/ `NE` / `!=` operator
        "ne" | "NE" | "!=" => NotEqual = LESS | GREATER,
        /// `ge` / `GE` / `>=` operator
        "ge" | "GE" | ">=" => GreaterThanEqual = GREATER | EQUAL,
        /// `le` / `LE` / `<=` operator
        "le" | "LE" | "<=" => LessThanEqual = LESS | EQUAL,
        /// `gt` / `GT` / `>` operator
        "gt" | "GT" | ">" => GreaterThan = GREATER,
        /// `lt` / `LT` / `<` operator
        "lt" | "LT" | "<" => LessThan = LESS,
    }
);

impl OrderingOp {
    /// Determines whether the operator matches a given ordering.
    pub fn matches(self, ordering: Ordering) -> bool {
        let mask = match self {
            OrderingOp::Equal(_) => EQUAL,
            OrderingOp::NotEqual(_) => LESS | GREATER,
            OrderingOp::GreaterThanEqual(_) => GREATER | EQUAL,
            OrderingOp::LessThanEqual(_) => LESS | EQUAL,
            OrderingOp::GreaterThan(_) => GREATER,
            OrderingOp::LessThan(_) => LESS,
        };
        let flag = match ordering {
            Ordering::Less => LESS,
            Ordering::Greater => GREATER,
            Ordering::Equal => EQUAL,
        };
        mask & flag != 0
    }

    /// Same as `matches` but accepts an optional ordering for incomparable
    /// types.
    pub fn matches_opt(self, ordering: Option<Ordering>) -> bool {
        match ordering {
            Some(ordering) => self.matches(ordering),
            // only `!=` should be true for incomparable types
            None => self == OrderingOp::NotEqual(0),
        }
    }
}

lex_enum!(IntOp {
    "&" | "bitwise_and" | "BITWISE_AND" => BitwiseAnd,
});

lex_enum!(BytesOp {
    "contains" | "CONTAINS" => Contains,
    "~" | "matches" | "MATCHES" => Matches,
    "like_case_insensitive" | "like_ci" | "LIKE_CASE_INSENSITIVE" | "LIKE_CI" => LikeCaseInsensitive,
    "like" | "LIKE" => Like,
});

lex_enum!(ComparisonOp {
    "in" | "IN" => In,
    "has_any_case_insensitive" | "has_any_ci" | "HAS_ANY_CASE_INSENSITIVE" | "HAS_ANY_CI" => HasAnyCaseInsensitive,
    "has_any" | "HAS_ANY" => HasAny,
    "has_all_case_insensitive" | "has_all_ci" | "HAS_ALL_CASE_INSENSITIVE" | "HAS_ALL_CI" => HasAllCaseInsensitive,
    "has_all" | "HAS_ALL" => HasAll,
    "cases" | "CASES" | "=>" => Cases,
    OrderingOp => Ordering,
    IntOp => Int,
    BytesOp => Bytes,
});

lex_enum!(CasesOp {
    "cases" | "CASES" | "=>" => Cases,
});

/// Operator and right-hand side expression of a
/// comparison expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum ComparisonOpExpr<'s> {
    /// Boolean field verification
    #[serde(serialize_with = "serialize_is_true")]
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
        op: OrderingOp,
        /// Right-hand side literal
        rhs: RhsValue,
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
        op: OrderingOp,
        /// `Variable` from the `Scheme`
        var: Variable,
    },

    /// "cases {...}" / "CASES {...}" / "=>" comparison
    #[serde(serialize_with = "serialize_cases")]
    Cases(Cases<LogicalExpr<'s>>),

    /// Integer comparison
    Int {
        /// Integer comparison operator:
        /// * "&" | "bitwise_and" | "BITWISE_AND"
        op: IntOp,
        /// Right-hand side integer value
        rhs: i32,
    },

    /// Integer comparison with a variable
    IntVariable {
        /// Integer comparison operator:
        /// * "&" | "bitwise_and" | "BITWISE_AND"
        op: IntOp,
        /// `Variable` from the `Scheme`
        var: Variable,
    },

    /// "contains" / "CONTAINS" comparison
    #[serde(serialize_with = "serialize_contains")]
    Contains {
        /// Right-hand side bytes value
        rhs: Bytes,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "contains" / "CONTAINS" comparison with a variable
    ContainsVariable {
        /// `Variable` from the `Scheme`
        var: Variable,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "matches / MATCHES / ~" comparison
    #[serde(serialize_with = "serialize_matches")]
    Matches {
        /// Right-hand side regex value
        rhs: Regex,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "matches / MATCHES / ~" comparison with a variable
    MatchesVariable {
        /// `Variable` from the `Scheme`
        var: Variable,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "like" / "LIKE" / "like_ci" / "LIKE_CI" comparison
    #[serde(serialize_with = "serialize_like")]
    Like {
        /// Right-hand side pattern value
        rhs: Like,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "like" / "LIKE" / "like_ci" / "LIKE_CI" comparison with a variable
    LikeVariable {
        /// `Variable` from the `Scheme`
        var: Variable,
        /// Case-insensitive comparison
        case_insensitive: bool,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "in [...]" / "IN [...]" comparison
    #[serde(serialize_with = "serialize_one_of")]
    OneOf {
        /// Right-hand side values
        rhs: RhsValues,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "in $..." | "IN $..." comparison with a variable
    OneOfVariable {
        /// `Variable` from the `Scheme`
        var: Variable,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "has_any [...]" / "HAS_ANY [...]" / "has_any_ci [...]" / "HAS_ANY_CI [...]" comparison
    #[serde(serialize_with = "serialize_has_any")]
    HasAny {
        /// Right-hand side values
        rhs: RhsValues,
        /// Case-insensitive comparison
        case_insensitive: bool,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "has_any $..." / "HAS_ANY $..." / "has_any_ci $..." / "HAS_ANY_CI $..." comparison with a variable
    HasAnyVariable {
        /// `Variable` from the `Scheme`
        var: Variable,
        /// Case-insensitive comparison
        case_insensitive: bool,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "has_all [...]" / "HAS_ALL [...]" / "has_all_ci [...]" / "HAS_ALL_CI [...]" comparison
    #[serde(serialize_with = "serialize_has_all")]
    HasAll {
        /// Right-hand side values
        rhs: RhsValues,
        /// Case-insensitive comparison
        case_insensitive: bool,
        /// Variant, used for formatting
        variant: u8,
    },

    /// "has_all $..." / "HAS_ALL $..." / "has_all_ci $..." / "HAS_ALL_CI $..." comparison with a variable
    HasAllVariable {
        /// `Variable` from the `Scheme`
        var: Variable,
        /// Case-insensitive comparison
        case_insensitive: bool,
        /// Variant, used for formatting
        variant: u8,
    },
}

fn serialize_op_rhs<T, S>(op: &'static str, rhs: &T, ser: S) -> Result<S::Ok, S::Error>
where
    T: Serialize + ?Sized,
    S: Serializer,
{
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("ComparisonOpExpr", 2)?;
    out.serialize_field("op", op)?;
    out.serialize_field("rhs", rhs)?;
    out.end()
}

fn serialize_is_true<S: Serializer>(ser: S) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("ComparisonOpExpr", 1)?;
    out.serialize_field("op", "IsTrue")?;
    out.end()
}

fn serialize_cases<S: Serializer>(
    cases: &Cases<LogicalExpr<'_>>,
    ser: S,
) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("ComparisonOpExpr", 2)?;
    out.serialize_field("op", "Cases")?;
    out.serialize_field("patterns", &cases.patterns)?;
    out.end()
}

fn serialize_contains<S: Serializer>(rhs: &Bytes, _: &u8, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Contains", rhs, ser)
}

fn serialize_matches<S: Serializer>(rhs: &Regex, _: &u8, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Matches", &rhs, ser)
}

fn serialize_like<S: Serializer>(rhs: &Like, _: &u8, ser: S) -> Result<S::Ok, S::Error> {
    if rhs.is_case_insensitive() {
        serialize_op_rhs("LikeCaseInsensitive", rhs, ser)
    } else {
        serialize_op_rhs("Like", rhs, ser)
    }
}

fn serialize_one_of<S: Serializer>(rhs: &RhsValues, _: &u8, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("OneOf", rhs, ser)
}

fn serialize_has_any<S: Serializer>(
    rhs: &RhsValues,
    case_insensitive: &bool,
    _: &u8,
    ser: S,
) -> Result<S::Ok, S::Error> {
    if *case_insensitive {
        serialize_op_rhs("HasAnyCaseInsensitive", rhs, ser)
    } else {
        serialize_op_rhs("HasAny", rhs, ser)
    }
}

fn serialize_has_all<S: Serializer>(
    rhs: &RhsValues,
    case_insensitive: &bool,
    _: &u8,
    ser: S,
) -> Result<S::Ok, S::Error> {
    if *case_insensitive {
        serialize_op_rhs("HasAllCaseInsensitive", rhs, ser)
    } else {
        serialize_op_rhs("HasAll", rhs, ser)
    }
}

/// "cases {...}" / "CASES {...}" / "=>"
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub struct Cases<E> {
    /// Cases patterns
    pub patterns: Vec<(Vec<CasePatternValue>, E)>,
    /// Variant, used for formatting
    pub variant: u8,
}

pub struct CompiledCases<E> {
    pub patterns: Vec<(Vec<CasePatternValue>, E)>,
    ty: Type,
}

impl<E> CompiledCases<E> {
    pub fn new(patterns: Vec<(Vec<CasePatternValue>, E)>, ty: Type) -> Self {
        Self { patterns, ty }
    }
}

impl<'s, U> CompiledCases<CompiledExpr<'s, U>> {
    pub fn execute(
        &self,
        value: &LhsValue<'_>,
        default: bool,
        ctx: &ExecutionContext<'_, U>,
        variables: &Variables,
        state: &State<'_>,
    ) -> bool {
        for (patterns, compiled_expr) in &self.patterns {
            for pattern in patterns {
                if pattern.matches(value) {
                    return compiled_expr.execute_one(ctx, variables, state);
                }
            }
        }

        default
    }
}

impl<'s, U> CompiledCases<CompiledValueExpr<'s, U>> {
    pub fn execute<'e>(
        &self,
        value: &LhsValue<'_>,
        ctx: &'e ExecutionContext<'e, U>,
        variables: &Variables,
        state: &State<'e>,
    ) -> CompiledValueResult<'e> {
        for (patterns, compiled_expr) in &self.patterns {
            for pattern in patterns {
                if pattern.matches(value) {
                    return compiled_expr.execute(ctx, variables, state);
                }
            }
        }

        Err(self.ty.clone())
    }
}

impl<'s> Cases<LogicalExpr<'s>> {
    pub(crate) fn compile_exprs_with_compiler<U: 's, C: Compiler<'s, U>>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledCases<CompiledExpr<'s, U>> {
        let ty = self.get_type();
        CompiledCases::new(
            self.patterns
                .into_iter()
                .map(|(patterns, expr)| {
                    let compiled_expr = expr.compile_with_compiler(compiler, variables);
                    (patterns, compiled_expr)
                })
                .collect(),
            ty,
        )
    }
}

impl<'s> Cases<IndexExpr<'s>> {
    pub(crate) fn compile_value_exprs_with_compiler<U: 's, C: Compiler<'s, U>>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledCases<CompiledValueExpr<'s, U>> {
        let ty = self.get_type();
        CompiledCases::new(
            self.patterns
                .into_iter()
                .map(|(patterns, expr)| {
                    let compiled_expr = expr.compile_with_compiler(compiler, variables);
                    (patterns, compiled_expr)
                })
                .collect(),
            ty,
        )
    }
}

impl<E: GetType> GetType for Cases<E> {
    fn get_type(&self) -> Type {
        self.patterns.first().unwrap().1.get_type()
    }
}

impl<'i, 's, 'v, E: LexWith2<'i, &'s Scheme, &'v Variables> + GetType> Cases<E> {
    pub(crate) fn lex_with_lhs_type(
        input: &'i str,
        scheme: &'s Scheme,
        variant: Option<u8>,
        lhs_type: Type,
        expected_type: Option<Type>,
        variables: &'v Variables,
    ) -> LexResult<'i, Self> {
        let input = skip_space(input);
        let initial_input = input;

        let (variant, input) = if let Some(variant) = variant {
            (variant, input)
        } else {
            let (op, input) = CasesOp::lex(initial_input)?;
            match op {
                CasesOp::Cases(variant) => (variant, input),
            }
        };

        let input = skip_space(input);
        let input = expect(input, "{")?;
        let mut input = skip_space(input);
        let mut all_patterns = Vec::new();
        let mut uses_catch_all_pattern = false;
        let mut first_cases_arm_type = None;
        loop {
            let mut patterns = IndexSet::new();
            let mut index = 0;
            loop {
                let (pattern, rest) = CasePatternValue::lex_with_lhs_type(input, &lhs_type)?;
                if pattern == CasePatternValue::Bool {
                    if uses_catch_all_pattern {
                        return Err((LexErrorKind::DuplicateCatchAllPattern, span(input, rest)));
                    } else {
                        uses_catch_all_pattern = true;
                    }
                } else if uses_catch_all_pattern {
                    return Err((
                        LexErrorKind::NonCatchAllPatternAfterCatchAll,
                        span(input, rest),
                    ));
                } else if !pattern.is_supported_lhs_value_match(&lhs_type) {
                    return Err((
                        LexErrorKind::TypeMismatch(TypeMismatchError {
                            expected: pattern.get_type().unwrap_or(Type::Bool).into(),
                            actual: lhs_type,
                        }),
                        span(input, rest),
                    ));
                }

                input = skip_space(rest);

                let len = patterns.len();
                patterns.insert(pattern);
                if len == patterns.len() {
                    return Err((
                        LexErrorKind::DuplicateCasePattern { index },
                        span(input, rest),
                    ));
                }

                if let Ok(rest) = expect(input, "|") {
                    input = skip_space(rest);
                } else {
                    break;
                }

                index += 1;
            }

            if patterns.is_empty() {
                return Err((
                    LexErrorKind::ExpectedCasePatterns,
                    span(initial_input, input),
                ));
            }

            input = skip_space(input);
            input = expect(input, "=>")?;
            input = skip_space(input);

            let (expr, rest) = E::lex_with_2(input, scheme, variables)?;
            let ty = expr.get_type();
            if let Some(expected_type) = &expected_type {
                if &ty != expected_type {
                    return Err((
                        LexErrorKind::TypeMismatch(TypeMismatchError {
                            expected: expected_type.clone().into(),
                            actual: ty,
                        }),
                        input,
                    ));
                }
            } else if first_cases_arm_type.is_none() {
                first_cases_arm_type = Some(ty);
            } else if let Some(first_cases_arm_type) = &first_cases_arm_type {
                if first_cases_arm_type != &ty {
                    return Err((
                        LexErrorKind::TypeMismatch(TypeMismatchError {
                            expected: first_cases_arm_type.clone().into(),
                            actual: ty,
                        }),
                        input,
                    ));
                }
            }
            all_patterns.push((patterns.into_iter().collect::<Vec<_>>(), expr));

            input = skip_space(rest);
            if expect(input, "}").is_ok() {
                break;
            }
            if let Ok(new_input) = expect(input, ",") {
                input = skip_space(new_input);
            }
            if expect(input, "}").is_ok() {
                break;
            }
            input = skip_space(input);
        }

        if all_patterns.is_empty() {
            return Err((
                LexErrorKind::ExpectedCasePatterns,
                span(initial_input, input),
            ));
        } else if all_patterns.len() == 1 {
            return Err((LexErrorKind::SingleCasePattern, span(initial_input, input)));
        } else {
            let mut duplicate_case_pattern = None;
            for (i, (patterns, _)) in all_patterns.iter().enumerate() {
                for (j, (other_patterns, _)) in all_patterns.iter().enumerate() {
                    if i != j && patterns == other_patterns {
                        duplicate_case_pattern = Some(i);
                        break;
                    }
                }
                if duplicate_case_pattern.is_some() {
                    break;
                }
            }

            if let Some(i) = duplicate_case_pattern {
                return Err((
                    LexErrorKind::DuplicateCasePattern { index: i },
                    span(initial_input, input),
                ));
            }

            let mut duplicate_case_expr = None;
            for (i, (patterns, _)) in all_patterns.iter().enumerate() {
                for (j, (other_patterns, _)) in all_patterns.iter().enumerate() {
                    if i != j && patterns == other_patterns {
                        duplicate_case_expr = Some(i);
                        break;
                    }
                }
                if duplicate_case_expr.is_some() {
                    break;
                }
            }

            if let Some(i) = duplicate_case_expr {
                return Err((
                    LexErrorKind::DuplicateCaseExpression { index: i },
                    span(initial_input, input),
                ));
            }

            match lhs_type {
                Type::Bytes => {
                    if let Some((last_pattern, _)) = all_patterns.last() {
                        if !last_pattern.iter().any(|p| p.is_catch_all()) {
                            return Err((
                                LexErrorKind::ExpectedCatchAllPattern,
                                span(initial_input, input),
                            ));
                        }
                    }
                }
                Type::Int => {
                    let mut has_catch_all = false;
                    if let Some((last_pattern, _)) = all_patterns.last() {
                        if last_pattern.iter().any(|p| p.is_catch_all()) {
                            has_catch_all = true;
                        }
                    }

                    let all_patterns_flat =
                        RangeSetWithId::from_iter(all_patterns.iter().enumerate().flat_map(
                            |(index, (patterns, _))| {
                                patterns
                                    .iter()
                                    .filter_map(|p| match p {
                                        CasePatternValue::Int(value) => {
                                            Some((*value..=*value, index))
                                        }
                                        CasePatternValue::IntRange(int_range) => {
                                            Some((int_range.0.clone(), index))
                                        }
                                        CasePatternValue::Bool => None,
                                        _ => unreachable!(),
                                    })
                                    .collect::<Vec<_>>()
                            },
                        ));

                    for i in 0..all_patterns_flat.len() - 1 {
                        if let Some((pattern, pattern_index)) = all_patterns_flat.get(i) {
                            if let Some((next_pattern, _)) = all_patterns_flat.get(i + 1) {
                                if pattern.end() >= next_pattern.start() {
                                    return Err((
                                        LexErrorKind::OverlappingCasePattern {
                                            index: *pattern_index,
                                        },
                                        span(initial_input, input),
                                    ));
                                }
                            }
                        }
                    }

                    if !has_catch_all {
                        if !all_patterns_flat.is_continuous() {
                            return Err((
                                LexErrorKind::NonExhaustiveCasePatterns,
                                span(initial_input, input),
                            ));
                        }

                        if let Some(min_start) = all_patterns_flat.get_min_start() {
                            if min_start != i32::MIN {
                                return Err((
                                    LexErrorKind::NonExhaustiveCasePatterns,
                                    span(initial_input, input),
                                ));
                            }

                            if let Some(max_end) = all_patterns_flat.get_max_end() {
                                if max_end != i32::MAX {
                                    return Err((
                                        LexErrorKind::NonExhaustiveCasePatterns,
                                        span(initial_input, input),
                                    ));
                                }
                            } else {
                                return Err((
                                    LexErrorKind::NonExhaustiveCasePatterns,
                                    span(initial_input, input),
                                ));
                            }
                        } else {
                            return Err((
                                LexErrorKind::NonExhaustiveCasePatterns,
                                span(initial_input, input),
                            ));
                        }
                    }
                }
                Type::Float => {
                    let mut has_catch_all = false;
                    if let Some((last_pattern, _)) = all_patterns.last() {
                        if last_pattern.iter().any(|p| p.is_catch_all()) {
                            has_catch_all = true;
                        }
                    }

                    let all_patterns_flat =
                        RangeSetWithId::from_iter(all_patterns.iter().enumerate().flat_map(
                            |(index, (patterns, _))| {
                                patterns
                                    .iter()
                                    .filter_map(|p| match p {
                                        CasePatternValue::Float(value) => {
                                            Some((*value..=*value, index))
                                        }
                                        CasePatternValue::FloatRange(float_range) => {
                                            Some((float_range.0.clone(), index))
                                        }
                                        CasePatternValue::Bool => None,
                                        _ => unreachable!(),
                                    })
                                    .collect::<Vec<_>>()
                            },
                        ));

                    for i in 0..all_patterns_flat.len() - 1 {
                        if let Some((pattern, pattern_index)) = all_patterns_flat.get(i) {
                            if let Some((next_pattern, _)) = all_patterns_flat.get(i + 1) {
                                if pattern.end() >= next_pattern.start() {
                                    return Err((
                                        LexErrorKind::OverlappingCasePattern {
                                            index: *pattern_index,
                                        },
                                        span(initial_input, input),
                                    ));
                                }
                            }
                        }
                    }

                    if !has_catch_all {
                        if !all_patterns_flat.is_continuous() {
                            return Err((
                                LexErrorKind::NonExhaustiveCasePatterns,
                                span(initial_input, input),
                            ));
                        }

                        if let Some(min_start) = all_patterns_flat.get_min_start() {
                            if min_start != f64::MIN {
                                return Err((
                                    LexErrorKind::NonExhaustiveCasePatterns,
                                    span(initial_input, input),
                                ));
                            }

                            if let Some(max_end) = all_patterns_flat.get_max_end() {
                                if max_end != f64::MAX {
                                    return Err((
                                        LexErrorKind::NonExhaustiveCasePatterns,
                                        span(initial_input, input),
                                    ));
                                }
                            } else {
                                return Err((
                                    LexErrorKind::NonExhaustiveCasePatterns,
                                    span(initial_input, input),
                                ));
                            }
                        } else {
                            return Err((
                                LexErrorKind::NonExhaustiveCasePatterns,
                                span(initial_input, input),
                            ));
                        }
                    }
                }
                Type::Ip => {
                    let mut has_catch_all = false;
                    if let Some((last_pattern, _)) = all_patterns.last() {
                        if last_pattern.iter().any(|p| p.is_catch_all()) {
                            has_catch_all = true;
                        }
                    }

                    let all_patterns_flat =
                        RangeSetWithId::from_iter(all_patterns.iter().enumerate().flat_map(
                            |(index, (patterns, _))| {
                                patterns
                                    .iter()
                                    .filter_map(|p| match p {
                                        CasePatternValue::Ip(value) => {
                                            Some((*value..=*value, index))
                                        }
                                        CasePatternValue::IpRange(ip_range) => {
                                            Some((ip_range.as_range(), index))
                                        }
                                        CasePatternValue::Bool => None,
                                        _ => unreachable!(),
                                    })
                                    .collect::<Vec<_>>()
                            },
                        ));

                    for i in 0..all_patterns_flat.len() - 1 {
                        if let Some((pattern, pattern_index)) = all_patterns_flat.get(i) {
                            if let Some((next_pattern, _)) = all_patterns_flat.get(i + 1) {
                                if pattern.end() >= next_pattern.start() {
                                    return Err((
                                        LexErrorKind::OverlappingCasePattern {
                                            index: *pattern_index,
                                        },
                                        span(initial_input, input),
                                    ));
                                }

                                if pattern.end() == next_pattern.start() {
                                    return Err((
                                        LexErrorKind::OverlappingCasePattern {
                                            index: *pattern_index,
                                        },
                                        span(initial_input, input),
                                    ));
                                }
                            }
                        }
                    }

                    if !has_catch_all {
                        if !all_patterns_flat.is_continuous() {
                            return Err((
                                LexErrorKind::NonExhaustiveCasePatterns,
                                span(initial_input, input),
                            ));
                        }

                        if let (Some(min_start_v4), Some(min_start_v6)) = (
                            all_patterns_flat.get_min_start_with_condition(IpAddr::is_ipv4),
                            all_patterns_flat.get_min_start_with_condition(IpAddr::is_ipv6),
                        ) {
                            if min_start_v4 != IpAddr::V4(Ipv4Addr::UNSPECIFIED)
                                && min_start_v6 != IpAddr::V6(Ipv6Addr::UNSPECIFIED)
                            {
                                return Err((
                                    LexErrorKind::NonExhaustiveCasePatterns,
                                    span(initial_input, input),
                                ));
                            }

                            if let (Some(max_end_v4), Some(max_end_v6)) = (
                                all_patterns_flat.get_max_end_with_condition(IpAddr::is_ipv4),
                                all_patterns_flat.get_max_end_with_condition(IpAddr::is_ipv6),
                            ) {
                                if max_end_v4 != IpAddr::V4(Ipv4Addr::new(255, 255, 255, 255))
                                    && max_end_v6
                                        != IpAddr::V6(Ipv6Addr::new(
                                            65535, 65535, 65535, 65535, 65535, 65535, 65535, 65535,
                                        ))
                                {
                                    return Err((
                                        LexErrorKind::NonExhaustiveCasePatterns,
                                        span(initial_input, input),
                                    ));
                                }
                            } else {
                                return Err((
                                    LexErrorKind::NonExhaustiveCasePatterns,
                                    span(initial_input, input),
                                ));
                            }
                        } else {
                            return Err((
                                LexErrorKind::NonExhaustiveCasePatterns,
                                span(initial_input, input),
                            ));
                        }
                    }

                    if let Some((last_pattern, _)) = all_patterns.last() {
                        if !last_pattern.iter().any(|p| p.is_catch_all()) {
                            return Err((
                                LexErrorKind::ExpectedCatchAllPattern,
                                span(initial_input, input),
                            ));
                        }
                    }

                    if all_patterns.len() == 1 {
                        return Err((LexErrorKind::SingleCasePattern, span(initial_input, input)));
                    }
                }
                _ => {
                    return Err((
                        LexErrorKind::CasePatternsNotSupported(lhs_type),
                        span(initial_input, input),
                    ));
                }
            }
        }

        input = expect(input, "}")?;
        input = skip_space(input);

        Ok((
            Self {
                patterns: all_patterns,
                variant,
            },
            input,
        ))
    }
}

/// Left-hand side of a field expression
///
/// This can be either a field or a function call.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum LhsFieldExpr<'s> {
    /// Field expression
    Field(Field<'s>),
    /// Function call expression
    FunctionCallExpr(FunctionCallExpr<'s>),
}

impl<'s> LhsFieldExpr<'s> {
    /// Compiles a [`LhsFieldExpr`] into a [`CompiledValueExpr`] using a specific
    /// [`Compiler`].
    pub fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        match self {
            LhsFieldExpr::Field(f) => CompiledValueExpr::new(move |ctx, _, _| {
                Ok(ctx.get_field_value_unchecked(f).as_ref())
            }),
            LhsFieldExpr::FunctionCallExpr(call) => {
                compiler.compile_function_call_expr(call, variables)
            }
        }
    }
}

impl<'i, 's> LexWith2<'i, &'s Scheme, &Variables> for LhsFieldExpr<'s> {
    fn lex_with_2(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> LexResult<'i, Self> {
        let (item, input) = Identifier::lex_with(input, scheme)?;
        match item {
            Identifier::Field(field) => Ok((LhsFieldExpr::Field(field), input)),
            Identifier::Function(function) => {
                FunctionCallExpr::lex_with_function(input, function, variables)
                    .map(|(call, input)| (LhsFieldExpr::FunctionCallExpr(call), input))
            }
        }
    }
}

impl<'s> GetType for LhsFieldExpr<'s> {
    fn get_type(&self) -> Type {
        match self {
            LhsFieldExpr::Field(field) => field.get_type(),
            LhsFieldExpr::FunctionCallExpr(call) => call.get_type(),
        }
    }
}

/// Comparison expression
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub struct ComparisonExpr<'s> {
    /// Left-hand side of the comparison expression
    pub lhs: IndexExpr<'s>,

    /// Operator + right-hand side of the comparison expression
    #[serde(flatten)]
    pub op: ComparisonOpExpr<'s>,
}

impl<'s> GetType for ComparisonExpr<'s> {
    fn get_type(&self) -> Type {
        if self.lhs.map_each_count() > 0 {
            Type::Array(Box::new(Type::Bool))
        } else if self.op == ComparisonOpExpr::IsTrue {
            // Bool or Array(Bool)
            self.lhs.get_type()
        } else {
            Type::Bool
        }
    }
}

impl<'i, 's> LexWith2<'i, &'s Scheme, &Variables> for ComparisonExpr<'s> {
    fn lex_with_2(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> LexResult<'i, Self> {
        let (lhs, input) = IndexExpr::lex_with_2(input, scheme, variables)?;

        Self::lex_with_lhs(input, scheme, lhs, variables)
    }
}

impl<'s> ComparisonExpr<'s> {
    pub(crate) fn lex_with_lhs<'i>(
        input: &'i str,
        scheme: &'s Scheme,
        lhs: IndexExpr<'s>,
        variables: &Variables,
    ) -> LexResult<'i, Self> {
        let lhs_type = lhs.get_type();

        let (op, input) = if lhs_type == Type::Bool {
            (ComparisonOpExpr::IsTrue, input)
        } else if lhs_type.next() == Some(Type::Bool) {
            // Invalid because this would produce an Array(Array(Bool))
            // which cannot be coerced to an Array(Bool)
            if lhs.map_each_count() > 0 {
                return Err((
                    LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Array(Box::new(Type::Array(Box::new(Type::Bool)))),
                    },
                    span(input, input),
                ));
            } else {
                (ComparisonOpExpr::IsTrue, input)
            }
        } else {
            let initial_input = skip_space(input);
            let (op, input) = ComparisonOp::lex(initial_input)?;

            let input_after_op = input;

            let input = skip_space(input);

            let rhs = input;

            match (&lhs_type, op) {
                (Type::Ip, ComparisonOp::In(variant))
                | (Type::Bytes, ComparisonOp::In(variant))
                | (Type::Int, ComparisonOp::In(variant))
                | (Type::Float, ComparisonOp::In(variant)) => {
                    if expect(input, "$").is_ok() {
                        let (mut variable, input) = Variable::lex(input)?;
                        let variable_value = variables.get(variable.name_as_str()).ok_or((
                            LexErrorKind::UnknownVariable {
                                name: variable.name_as_str().into(),
                            },
                            span(rhs, input),
                        ))?;
                        variable.set_type(variable_value.get_variable_type());

                        if !variable_value.is_supported_lhs_value_match(&lhs_type) {
                            return Err((
                                LexErrorKind::VariableTypeMismatch {
                                    name: variable.take_name(),
                                    expected: lhs_type,
                                    actual: variable_value.get_variable_type(),
                                },
                                span(rhs, input),
                            ));
                        }
                        (
                            ComparisonOpExpr::OneOfVariable {
                                var: variable,
                                variant,
                            },
                            input,
                        )
                    } else {
                        let (rhs, input) = RhsValues::lex_with(input, lhs_type)?;
                        (ComparisonOpExpr::OneOf { rhs, variant }, input)
                    }
                }
                (Type::Bytes, ComparisonOp::HasAny(_))
                | (Type::Bytes, ComparisonOp::HasAll(_))
                | (Type::Bytes, ComparisonOp::HasAnyCaseInsensitive(_))
                | (Type::Bytes, ComparisonOp::HasAllCaseInsensitive(_)) => {
                    if expect(input, "$").is_ok() {
                        let (mut variable, input) = Variable::lex(input)?;
                        let variable_value = variables.get(variable.name_as_str()).ok_or((
                            LexErrorKind::UnknownVariable {
                                name: variable.name_as_str().into(),
                            },
                            span(rhs, input),
                        ))?;
                        variable.set_type(variable_value.get_variable_type());

                        if !variable_value.is_supported_lhs_value_match(&lhs_type) {
                            return Err((
                                LexErrorKind::VariableTypeMismatch {
                                    name: variable.take_name(),
                                    expected: lhs_type,
                                    actual: variable_value.get_variable_type(),
                                },
                                span(rhs, input),
                            ));
                        }
                        (
                            match op {
                                ComparisonOp::HasAny(variant) => ComparisonOpExpr::HasAnyVariable {
                                    var: variable,
                                    case_insensitive: false,
                                    variant,
                                },
                                ComparisonOp::HasAnyCaseInsensitive(variant) => {
                                    ComparisonOpExpr::HasAnyVariable {
                                        var: variable,
                                        case_insensitive: true,
                                        variant,
                                    }
                                }
                                ComparisonOp::HasAll(variant) => ComparisonOpExpr::HasAllVariable {
                                    var: variable,
                                    case_insensitive: false,
                                    variant,
                                },
                                ComparisonOp::HasAllCaseInsensitive(variant) => {
                                    ComparisonOpExpr::HasAllVariable {
                                        var: variable,
                                        case_insensitive: true,
                                        variant,
                                    }
                                }
                                _ => unreachable!(),
                            },
                            input,
                        )
                    } else {
                        let (rhs, input) = RhsValues::lex_with(input, lhs_type)?;
                        (
                            match op {
                                ComparisonOp::HasAny(variant) => ComparisonOpExpr::HasAny {
                                    rhs,
                                    case_insensitive: false,
                                    variant,
                                },
                                ComparisonOp::HasAnyCaseInsensitive(variant) => {
                                    ComparisonOpExpr::HasAny {
                                        rhs,
                                        case_insensitive: true,
                                        variant,
                                    }
                                }
                                ComparisonOp::HasAll(variant) => ComparisonOpExpr::HasAll {
                                    rhs,
                                    case_insensitive: false,
                                    variant,
                                },
                                ComparisonOp::HasAllCaseInsensitive(variant) => {
                                    ComparisonOpExpr::HasAll {
                                        rhs,
                                        case_insensitive: true,
                                        variant,
                                    }
                                }
                                _ => unreachable!(),
                            },
                            input,
                        )
                    }
                }
                (Type::Ip, ComparisonOp::Ordering(op))
                | (Type::Bytes, ComparisonOp::Ordering(op))
                | (Type::Int, ComparisonOp::Ordering(op))
                | (Type::Float, ComparisonOp::Ordering(op)) => {
                    if expect(input, "$").is_ok() {
                        let (mut variable, input) = Variable::lex(input)?;
                        let variable_value = variables.get(variable.name_as_str()).ok_or((
                            LexErrorKind::UnknownVariable {
                                name: variable.name_as_str().into(),
                            },
                            span(rhs, input),
                        ))?;
                        variable.set_type(variable_value.get_variable_type());

                        if !variable_value.is_supported_lhs_value_match(&lhs_type) {
                            return Err((
                                LexErrorKind::VariableTypeMismatch {
                                    name: variable.take_name(),
                                    expected: lhs_type,
                                    actual: variable_value.get_variable_type(),
                                },
                                span(rhs, input),
                            ));
                        }
                        (
                            ComparisonOpExpr::OrderingVariable { op, var: variable },
                            input,
                        )
                    } else {
                        let (rhs, input) = RhsValue::lex_with(input, lhs_type)?;
                        (ComparisonOpExpr::Ordering { op, rhs }, input)
                    }
                }
                (Type::Int, ComparisonOp::Int(op)) => {
                    if expect(input, "$").is_ok() {
                        let (mut variable, input) = Variable::lex(input)?;
                        let variable_value = variables.get(variable.name_as_str()).ok_or((
                            LexErrorKind::UnknownVariable {
                                name: variable.name_as_str().into(),
                            },
                            span(rhs, input),
                        ))?;
                        variable.set_type(variable_value.get_variable_type());

                        if !variable_value.is_supported_lhs_value_match(&lhs_type) {
                            return Err((
                                LexErrorKind::VariableTypeMismatch {
                                    name: variable.take_name(),
                                    expected: lhs_type,
                                    actual: variable_value.get_variable_type(),
                                },
                                span(rhs, input),
                            ));
                        }
                        (ComparisonOpExpr::IntVariable { op, var: variable }, input)
                    } else {
                        let (rhs, input) = i32::lex(input)?;
                        (ComparisonOpExpr::Int { op, rhs }, input)
                    }
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => {
                    if expect(input, "$").is_ok() {
                        let (mut variable, input) = Variable::lex(input)?;
                        let variable_value = variables.get(variable.name_as_str()).ok_or((
                            LexErrorKind::UnknownVariable {
                                name: variable.name_as_str().into(),
                            },
                            span(rhs, input),
                        ))?;
                        variable.set_type(variable_value.get_variable_type());

                        if !variable_value.is_supported_lhs_value_match(&lhs_type) {
                            return Err((
                                LexErrorKind::VariableTypeMismatch {
                                    name: variable.take_name(),
                                    expected: lhs_type,
                                    actual: variable_value.get_variable_type(),
                                },
                                span(rhs, input),
                            ));
                        }

                        match op {
                            BytesOp::Contains(variant) => (
                                ComparisonOpExpr::ContainsVariable {
                                    var: variable,
                                    variant,
                                },
                                input,
                            ),
                            BytesOp::Matches(variant) => (
                                ComparisonOpExpr::MatchesVariable {
                                    var: variable,
                                    variant,
                                },
                                input,
                            ),
                            BytesOp::Like(variant) => (
                                ComparisonOpExpr::LikeVariable {
                                    var: variable,
                                    case_insensitive: false,
                                    variant,
                                },
                                input,
                            ),
                            BytesOp::LikeCaseInsensitive(variant) => (
                                ComparisonOpExpr::LikeVariable {
                                    var: variable,
                                    case_insensitive: true,
                                    variant,
                                },
                                input,
                            ),
                        }
                    } else {
                        {
                            match op {
                                BytesOp::Contains(variant) => {
                                    let (bytes, input) = Bytes::lex(input)?;
                                    (
                                        ComparisonOpExpr::Contains {
                                            rhs: bytes,
                                            variant,
                                        },
                                        input,
                                    )
                                }
                                BytesOp::Matches(variant) => {
                                    let (regex, input) = Regex::lex(input)?;
                                    (
                                        ComparisonOpExpr::Matches {
                                            rhs: regex,
                                            variant,
                                        },
                                        input,
                                    )
                                }
                                BytesOp::Like(variant) => {
                                    let (like, input) = Like::lex_with(input, false)?;
                                    (ComparisonOpExpr::Like { rhs: like, variant }, input)
                                }
                                BytesOp::LikeCaseInsensitive(variant) => {
                                    let (like, input) = Like::lex_with(input, true)?;
                                    (ComparisonOpExpr::Like { rhs: like, variant }, input)
                                }
                            }
                        }
                    }
                }
                (Type::Bytes, ComparisonOp::Cases(variant))
                | (Type::Int, ComparisonOp::Cases(variant))
                | (Type::Float, ComparisonOp::Cases(variant))
                | (Type::Ip, ComparisonOp::Cases(variant)) => {
                    // LogicalExpr::lex_with can return an AST where the root is an
                    // LogicalExpr::Combining of type [`Array(Bool)`].
                    //
                    // It must do this because we need to be able to use
                    // LogicalExpr::Combining of type [`Array(Bool)`]
                    // as arguments to functions, however it should not be valid as a
                    // case expression in a comparison expression.
                    //
                    // Here we enforce the constraint that the case expression of the AST, a
                    // LogicalExpr, must evaluate to type [`Bool`].
                    let (cases, input) = Cases::lex_with_lhs_type(
                        input,
                        scheme,
                        Some(variant),
                        lhs_type,
                        Some(Type::Bool),
                        variables,
                    )?;

                    (ComparisonOpExpr::Cases(cases), input)
                }
                _ => {
                    return Err((
                        LexErrorKind::UnsupportedOp { lhs_type },
                        span(initial_input, input_after_op),
                    ));
                }
            }
        };

        Ok((ComparisonExpr { lhs, op }, input))
    }
}

impl<'s> Expr<'s> for ComparisonExpr<'s> {
    #[inline]
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        visitor.visit_index_expr(&self.lhs)
    }

    #[inline]
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        visitor.visit_index_expr(&mut self.lhs)
    }

    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        let lhs = self.lhs;

        macro_rules! cast_lhs_rhs_value {
            ($value:expr, $ty:ident) => {
                match $value {
                    LhsValue::$ty(value) => value,
                    _ => unreachable!(),
                }
            };
        }

        macro_rules! cast_rhs_values {
            ($values:expr, $ty:ident) => {
                match $values {
                    RhsValues::$ty(values) => values,
                    _ => unreachable!(),
                }
            };
        }

        macro_rules! cast_variable_value {
            ($value:expr, $ty:ident) => {
                match $value {
                    VariableValue::$ty(value) => value,
                    _ => unreachable!(),
                }
            };
        }

        match self.op {
            ComparisonOpExpr::IsTrue => {
                if lhs.get_type() == Type::Bool {
                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| *cast_lhs_rhs_value!(x, Bool),
                        variables,
                    )
                } else if lhs.get_type().next() == Some(Type::Bool) {
                    // MapEach is impossible in this case, thus call `compile_vec_with` directly
                    // to coerce LhsValue to Vec<bool>
                    CompiledExpr::Vec(lhs.compile_vec_with(
                        compiler,
                        move |x, _ctx, _, _| *cast_lhs_rhs_value!(x, Bool),
                        variables,
                    ))
                } else {
                    unreachable!()
                }
            }

            ComparisonOpExpr::Ordering { op, rhs } => match op {
                OrderingOp::NotEqual(_) => lhs.compile_with(
                    compiler,
                    true,
                    move |x, _ctx, _, _| op.matches_opt(x.strict_partial_cmp(&rhs)),
                    variables,
                ),
                _ => lhs.compile_with(
                    compiler,
                    false,
                    move |x, _ctx, _, _| op.matches_opt(x.strict_partial_cmp(&rhs)),
                    variables,
                ),
            },
            ComparisonOpExpr::OrderingVariable { op, var: variable } => match op {
                OrderingOp::NotEqual(_) => lhs.compile_with(
                    compiler,
                    true,
                    move |x, _ctx, variables, _| {
                        variables
                            .get(variable.name_as_str())
                            .map_or(false, |variable| {
                                op.matches_opt(x.strict_partial_cmp(variable))
                            })
                    },
                    variables,
                ),
                _ => lhs.compile_with(
                    compiler,
                    false,
                    move |x, _ctx, variables, _| {
                        variables
                            .get(variable.name_as_str())
                            .map_or(false, |variable| {
                                op.matches_opt(x.strict_partial_cmp(variable))
                            })
                    },
                    variables,
                ),
            },

            ComparisonOpExpr::Cases(cases) => {
                let compiled_patterns = cases.compile_exprs_with_compiler(compiler, variables);

                lhs.compile_with(
                    compiler,
                    false,
                    move |x, ctx, variables, state| {
                        compiled_patterns.execute(x, false, ctx, variables, state)
                    },
                    variables,
                )
            }

            ComparisonOpExpr::Int {
                op: IntOp::BitwiseAnd(_),
                rhs,
            } => lhs.compile_with(
                compiler,
                false,
                move |x, _ctx, _, _| cast_lhs_rhs_value!(x, Int) & rhs != 0,
                variables,
            ),
            ComparisonOpExpr::IntVariable {
                op: IntOp::BitwiseAnd(_),
                var,
            } => lhs.compile_with(
                compiler,
                false,
                move |x, _ctx, variables, _| {
                    variables.get(var.name_as_str()).map_or(false, |var| {
                        cast_lhs_rhs_value!(x, Int) & cast_variable_value!(var, Int) != 0
                    })
                },
                variables,
            ),

            ComparisonOpExpr::Contains {
                rhs: bytes,
                variant: _,
            } => {
                macro_rules! search {
                    ($searcher:expr) => {{
                        let searcher = $searcher;
                        lhs.compile_with(
                            compiler,
                            false,
                            move |x, _ctx, _, _| {
                                searcher.search_in(cast_lhs_rhs_value!(x, Bytes).as_ref())
                            },
                            variables,
                        )
                    }};
                }

                let bytes = bytes.into_boxed_bytes();

                if bytes.is_empty() {
                    return search!(EmptySearcher);
                }

                if let [byte] = *bytes {
                    return search!(MemchrSearcher::new(byte));
                }

                #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
                if *USE_AVX2 {
                    use rand::{thread_rng, Rng};
                    use sliceslice::x86::*;

                    let position = thread_rng().gen_range(1..bytes.len());
                    return unsafe { search!(DynamicAvx2Searcher::with_position(bytes, position)) };
                }

                search!(TwoWaySearcher::new(bytes))
            }
            ComparisonOpExpr::ContainsVariable { var, variant: _ } => {
                macro_rules! search {
                    ($searcher:expr) => {{
                        let searcher = $searcher;
                        lhs.compile_with(
                            compiler,
                            false,
                            move |x, _ctx, _, _| {
                                searcher.search_in(cast_lhs_rhs_value!(x, Bytes).as_ref())
                            },
                            variables,
                        )
                    }};
                }

                if let Some(var) = variables.get(var.name_as_str()) {
                    let bytes = cast_variable_value!(var, Bytes).clone().into_boxed_slice();

                    if bytes.is_empty() {
                        return search!(EmptySearcher);
                    }

                    if let [byte] = *bytes {
                        return search!(MemchrSearcher::new(byte));
                    }

                    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
                    if *USE_AVX2 {
                        use rand::{thread_rng, Rng};
                        use sliceslice::x86::*;

                        let position = thread_rng().gen_range(1..bytes.len());
                        return unsafe {
                            search!(DynamicAvx2Searcher::with_position(bytes, position))
                        };
                    }

                    search!(TwoWaySearcher::new(bytes))
                } else {
                    lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                }
            }

            ComparisonOpExpr::Matches {
                rhs: regex,
                variant: _,
            } => lhs.compile_with(
                compiler,
                false,
                move |x, _ctx, _, _| regex.is_match(cast_lhs_rhs_value!(x, Bytes)),
                variables,
            ),
            ComparisonOpExpr::MatchesVariable { var, variant: _ } => lhs.compile_with(
                compiler,
                false,
                move |x, _ctx, variables, _| {
                    variables.get(var.name_as_str()).map_or(false, |variable| {
                        cast_variable_value!(variable, Regex)
                            .is_match(cast_lhs_rhs_value!(x, Bytes))
                    })
                },
                variables,
            ),

            ComparisonOpExpr::Like {
                rhs: like,
                variant: _,
            } => lhs.compile_with(
                compiler,
                false,
                move |x, _ctx, _, _| like.is_match(cast_lhs_rhs_value!(x, Bytes)),
                variables,
            ),
            ComparisonOpExpr::LikeVariable {
                var,
                case_insensitive: _,
                variant: _,
            } => lhs.compile_with(
                compiler,
                false,
                move |x, _ctx, variables, _| {
                    variables.get(var.name_as_str()).map_or(false, |variable| {
                        cast_variable_value!(variable, Like).is_match(cast_lhs_rhs_value!(x, Bytes))
                    })
                },
                variables,
            ),

            ComparisonOpExpr::OneOf {
                rhs: values,
                variant: _,
            } => match values {
                RhsValues::Ip(ranges) => {
                    let mut v4 = Vec::new();
                    let mut v6 = Vec::new();
                    for range in ranges {
                        match range.clone().into() {
                            ExplicitIpRange::V4(range) => v4.push(range),
                            ExplicitIpRange::V6(range) => v6.push(range),
                        }
                    }
                    let v4 = RangeSet::from(v4);
                    let v6 = RangeSet::from(v6);

                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| match cast_lhs_rhs_value!(x, Ip) {
                            IpAddr::V4(addr) => v4.contains(addr),
                            IpAddr::V6(addr) => v6.contains(addr),
                        },
                        variables,
                    )
                }
                RhsValues::Int(values) => {
                    let values: RangeSet<_> = values.into_iter().map(Into::into).collect();

                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| values.contains(cast_lhs_rhs_value!(x, Int)),
                        variables,
                    )
                }
                RhsValues::Float(values) => {
                    let values: RangeSet<_> = values.into_iter().map(Into::into).collect();

                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| values.contains(cast_lhs_rhs_value!(x, Float)),
                        variables,
                    )
                }
                RhsValues::Bytes(values) => {
                    let values: IndexSet<Box<[u8]>, FnvBuildHasher> =
                        values.into_iter().map(Into::into).collect();

                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| {
                            values.contains(cast_lhs_rhs_value!(x, Bytes) as &[u8])
                        },
                        variables,
                    )
                }
                RhsValues::Bool(_)
                | RhsValues::Map(_)
                | RhsValues::Array(_)
                | RhsValues::Regex(_)
                | RhsValues::Like(_) => unreachable!(),
            },
            ComparisonOpExpr::OneOfVariable { var, variant: _ } => lhs.compile_with(
                compiler,
                false,
                move |val, _, variables, _| {
                    variables
                        .get(var.name_as_str())
                        .map_or(false, |variable| variable.matches_lhs_value(val))
                },
                variables,
            ),

            ComparisonOpExpr::HasAny {
                rhs: values,
                case_insensitive,
                variant: _,
            } => {
                let values = cast_rhs_values!(values, Bytes);
                if let Ok(searcher) = AhoCorasickBuilder::new()
                    .ascii_case_insensitive(case_insensitive)
                    .build(values)
                {
                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| searcher.is_match(cast_lhs_rhs_value!(x, Bytes)),
                        variables,
                    )
                } else {
                    lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                }
            }
            ComparisonOpExpr::HasAnyVariable {
                var,
                case_insensitive,
                variant: _,
            } => {
                if let Some(var) = variables.get(var.name_as_str()) {
                    let variable_values = cast_variable_value!(var, BytesList);
                    if let Ok(searcher) = AhoCorasickBuilder::new()
                        .ascii_case_insensitive(case_insensitive)
                        .build(variable_values)
                    {
                        lhs.compile_with(
                            compiler,
                            false,
                            move |x, _ctx, _, _| searcher.is_match(cast_lhs_rhs_value!(x, Bytes)),
                            variables,
                        )
                    } else {
                        lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                    }
                } else {
                    lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                }
            }
            ComparisonOpExpr::HasAll {
                rhs: values,
                case_insensitive,
                variant: _,
            } => {
                let values = cast_rhs_values!(values, Bytes);
                if let Ok(searcher) = AhoCorasickBuilder::new()
                    .ascii_case_insensitive(case_insensitive)
                    .build(&values)
                {
                    lhs.compile_with(
                        compiler,
                        false,
                        move |x, _ctx, _, _| {
                            let text = cast_lhs_rhs_value!(x, Bytes);
                            let mut found = vec![false; values.len()];
                            if let Ok(find_iter) = searcher.try_find_iter(text) {
                                for mat in find_iter {
                                    found[mat.pattern()] = true;
                                }
                                found.into_iter().all(|f| f)
                            } else {
                                false
                            }
                        },
                        variables,
                    )
                } else {
                    lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                }
            }
            ComparisonOpExpr::HasAllVariable {
                var,
                case_insensitive,
                variant: _,
            } => {
                if let Some(var) = variables.get(var.name_as_str()) {
                    let variable_values = cast_variable_value!(var, BytesList);
                    let variable_values_len = variable_values.len();
                    if let Ok(searcher) = AhoCorasickBuilder::new()
                        .ascii_case_insensitive(case_insensitive)
                        .build(variable_values)
                    {
                        lhs.compile_with(
                            compiler,
                            false,
                            move |x, _ctx, _, _| {
                                let text = cast_lhs_rhs_value!(x, Bytes);
                                let mut found = vec![false; variable_values_len];
                                if let Ok(find_iter) = searcher.try_find_iter(text) {
                                    for mat in find_iter {
                                        found[mat.pattern()] = true;
                                    }
                                    found.into_iter().all(|f| f)
                                } else {
                                    false
                                }
                            },
                            variables,
                        )
                    } else {
                        lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                    }
                } else {
                    lhs.compile_with(compiler, false, move |_x, _ctx, _, _| false, variables)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{
            function_expr::{FunctionCallArgExpr, FunctionCallExpr},
            simple_expr::SimpleExpr,
        },
        execution_context::{ExecutionContext, State, Variables},
        functions::{
            FunctionArgKind, FunctionArgs, FunctionDefinition, FunctionDefinitionContext,
            FunctionParam, FunctionParamError, SimpleFunctionDefinition, SimpleFunctionImpl,
            SimpleFunctionOptParam, SimpleFunctionParam,
        },
        lhs_types::{Array, Map},
        rhs_types::{IntRange, IpRange},
        scheme::{FieldIndex, IndexAccessError},
        types::{ExpectedType, RhsValues},
        VariableType,
    };
    use cidr::IpCidr;
    use lazy_static::lazy_static;
    use std::{convert::TryFrom, iter::once, net::IpAddr};

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

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    fn lowercase_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        let input = args.next()?.ok()?;
        match input {
            LhsValue::Bytes(bytes) => Some(LhsValue::Bytes(bytes.to_ascii_lowercase().into())),
            _ => panic!("Invalid type: expected Bytes, got {:?}", input),
        }
    }

    fn concat_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        let mut output = Vec::new();
        for (index, arg) in args.enumerate() {
            match arg.unwrap() {
                LhsValue::Bytes(bytes) => {
                    output.extend_from_slice(&bytes);
                }
                arg => panic!(
                    "Invalid type for argument {:?}: expected Bytes, got {:?}",
                    index, arg
                ),
            }
        }
        Some(LhsValue::Bytes(output.into()))
    }

    #[derive(Debug)]
    struct FilterFunction {}

    impl FilterFunction {
        fn new() -> Self {
            Self {}
        }
    }

    impl FunctionDefinition for FilterFunction {
        fn check_param(
            &self,
            params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            next_param: &FunctionParam<'_>,
            _: Option<&mut FunctionDefinitionContext>,
        ) -> Result<(), FunctionParamError> {
            match params.len() {
                0 => {
                    next_param.expect_arg_kind(FunctionArgKind::Complex)?;
                    next_param.expect_val_type(once(ExpectedType::Array))?;
                }
                1 => {
                    next_param.expect_arg_kind(FunctionArgKind::Complex)?;
                    next_param.expect_val_type(once(ExpectedType::Type(Type::Array(Box::new(
                        Type::Bool,
                    )))))?;
                }
                _ => unreachable!(),
            }
            Ok(())
        }

        fn return_type(
            &self,
            params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<&FunctionDefinitionContext>,
        ) -> Type {
            params.next().unwrap().get_type()
        }

        /// Number of arguments needed by the function.
        fn arg_count(&self) -> (usize, Option<usize>) {
            (2, Some(0))
        }

        fn arg_type(&self, index: usize) -> Option<Type> {
            match index {
                0 => Some(Type::Array(Box::new(Type::Bytes))),
                1 => Some(Type::Array(Box::new(Type::Bool))),
                _ => None,
            }
        }

        fn compile<'s>(
            &'s self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<FunctionDefinitionContext>,
        ) -> Box<
            dyn for<'a> Fn(FunctionArgs<'_, 'a>, &State<'a>) -> Option<LhsValue<'a>>
                + Sync
                + Send
                + 's,
        > {
            Box::new(|args, _| {
                let value_array = Array::try_from(args.next().unwrap().unwrap()).unwrap();
                let keep_array = Array::try_from(args.next().unwrap().unwrap()).unwrap();
                let mut output = Array::new(value_array.value_type().clone());
                let mut i = 0;
                for (value, keep) in value_array.into_iter().zip(keep_array) {
                    if bool::try_from(keep).unwrap() {
                        output.insert(i, value).unwrap();
                        i += 1;
                    }
                }
                Some(LhsValue::Array(output))
            })
        }
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme: Scheme = Scheme! {
                http.cookies: Array(Bytes),
                http.headers: Map(Bytes),
                http.host: Bytes,
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
                tcp.ports: Array(Int),
                array.of.bool: Array(Bool),
                http.parts: Array(Array(Bytes)),
            };
            scheme
                .add_function(
                    "any".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Complex,
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
                            arg_kind: FunctionArgKind::Complex,
                            val_type: Type::Bytes,
                        }],
                        opt_params: Some(vec![]),
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(echo_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "lowercase".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Complex,
                            val_type: Type::Bytes,
                        }],
                        opt_params: Some(vec![]),
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(lowercase_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "concat".into(),
                    SimpleFunctionDefinition {
                        params: vec![],
                        opt_params: Some(vec![
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Complex,
                                default_value: "".into(),
                            },
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: "".into(),
                            },
                        ]),
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(concat_function),
                    },
                )
                .unwrap();
            scheme
                .add_function("filter".into(), FilterFunction::new())
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
            variables.add("int_list".to_string(), vec![1000].into());
            variables
        };
    }

    fn field(name: &'static str) -> Field<'static> {
        SCHEME.get_field(name).unwrap()
    }

    #[test]
    fn test_is_true() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2("ssl", &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ssl")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::IsTrue
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "ssl",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("ssl"), true).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("ssl"), false).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_ip_compare() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2("ip.addr <= 10:20:30:40:50:60:70:80", &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ip.addr")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThanEqual(1),
                    rhs: RhsValue::Ip(IpAddr::from([
                        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80
                    ]))
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "ip.addr",
                "op": "LessThanEqual",
                "rhs": "10:20:30:40:50:60:70:80"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]))
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(
            field("ip.addr"),
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]),
        )
        .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(
            field("ip.addr"),
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x81]),
        )
        .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("ip.addr"), IpAddr::from([127, 0, 0, 1]))
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_compare() {
        // just check that parsing doesn't conflict with IPv6
        {
            let expr = assert_ok!(
                ComparisonExpr::lex_with_2(
                    "http.host >= 10:20:30:40:50:60:70:80",
                    &SCHEME,
                    &VARIABLES
                ),
                ComparisonExpr {
                    lhs: IndexExpr {
                        lhs: LhsFieldExpr::Field(field("http.host")),
                        indexes: vec![],
                    },
                    op: ComparisonOpExpr::Ordering {
                        op: OrderingOp::GreaterThanEqual(1),
                        rhs: RhsValue::Bytes(
                            vec![0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into()
                        ),
                    },
                }
            );

            assert_json!(
                expr,
                {
                    "lhs": "http.host",
                    "op": "GreaterThanEqual",
                    "rhs": [0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]
                }
            );
        }

        // just check that parsing doesn't conflict with regular numbers
        {
            let expr = assert_ok!(
                ComparisonExpr::lex_with_2(r#"http.host < 12"#, &SCHEME, &VARIABLES),
                ComparisonExpr {
                    lhs: IndexExpr {
                        lhs: LhsFieldExpr::Field(field("http.host")),
                        indexes: vec![],
                    },
                    op: ComparisonOpExpr::Ordering {
                        op: OrderingOp::LessThan(1),
                        rhs: RhsValue::Bytes(vec![0x12].into()),
                    },
                }
            );

            assert_json!(
                expr,
                {
                    "lhs": "http.host",
                    "op": "LessThan",
                    "rhs": [0x12]
                }
            );
        }

        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.host == "example.org""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bitwise_and() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2("tcp.port & 1", &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Int {
                    op: IntOp::BitwiseAnd(0),
                    rhs: 1,
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "BitwiseAnd",
                "rhs": 1
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 443).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_int_cases() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"tcp.port cases {
                    80 => http.host == "example.org",
                    443
                    | 8000..8080 => http.host == "example.com",
                    _ => http.host == "example.net",
                }"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Cases(Cases {
                    patterns: vec![
                        (
                            vec![CasePatternValue::IntRange(IntRange(80..=80))],
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(field("http.host")),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::Ordering {
                                    op: OrderingOp::Equal(2),
                                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                                }
                            }))
                        ),
                        (
                            vec![
                                CasePatternValue::IntRange(IntRange(443..=443)),
                                CasePatternValue::IntRange(IntRange(8000..=8080))
                            ],
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(field("http.host")),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::Ordering {
                                    op: OrderingOp::Equal(2),
                                    rhs: RhsValue::Bytes("example.com".to_owned().into())
                                }
                            }))
                        ),
                        (
                            vec![CasePatternValue::Bool],
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(field("http.host")),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::Ordering {
                                    op: OrderingOp::Equal(2),
                                    rhs: RhsValue::Bytes("example.net".to_owned().into())
                                }
                            }))
                        ),
                    ],
                    variant: 0,
                }),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "Cases",
                "patterns": [
                    [
                        [
                            { "IntRange": { "start": 80, "end": 80 } },
                        ],
                        {
                            "lhs": "http.host",
                            "op": "Equal",
                            "rhs": "example.org"
                        },
                    ],
                    [
                        [
                            { "IntRange": { "start": 443, "end": 443 } },
                            { "IntRange": { "start": 8000, "end": 8080 } },

                        ],
                        {
                            "lhs": "http.host",
                            "op": "Equal",
                            "rhs": "example.com"
                        },
                    ],
                    [
                        [
                            "Bool",
                        ],
                        {
                            "lhs": "http.host",
                            "op": "Equal",
                            "rhs": "example.net"
                        },
                    ]
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 443).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 8080).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_int_in() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"tcp.port in [ 80, 443, 2082..2083 ]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf {
                    rhs: RhsValues::Int(vec![80.into(), 443.into(), (2082..=2083).into()]),
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "OneOf",
                "rhs": [
                    { "start": 80, "end": 80 },
                    { "start": 443, "end": 443 },
                    { "start": 2082, "end": 2083 },
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 8080).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 443).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 2081).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 2082).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 2083).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 2084).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_in() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.host in [ "example.org", "example.com" ]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf {
                    rhs: RhsValues::Bytes(
                        ["example.org", "example.com",]
                            .iter()
                            .map(|s| (*s).to_string().into())
                            .collect()
                    ),
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "OneOf",
                "rhs": [
                    "example.org",
                    "example.com",
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.net")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_has_all() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.host has_all [ "exam", "ple" ]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::HasAll {
                    rhs: RhsValues::Bytes(
                        ["exam", "ple",]
                            .iter()
                            .map(|s| (*s).to_string().into())
                            .collect()
                    ),
                    case_insensitive: false,
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "HasAll",
                "rhs": [
                    "exam",
                    "ple",
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "test.net").unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_has_any() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.host has_any [ "com", "org", ]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::HasAny {
                    rhs: RhsValues::Bytes(
                        ["com", "org",]
                            .iter()
                            .map(|s| (*s).to_string().into())
                            .collect()
                    ),
                    case_insensitive: false,
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "HasAny",
                "rhs": [
                    "com",
                    "org",
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.net")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_has_any_case_insensitive() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.host has_any_ci [ "CoM", "oRg", ]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::HasAny {
                    rhs: RhsValues::Bytes(
                        ["CoM", "oRg",]
                            .iter()
                            .map(|s| (*s).to_string().into())
                            .collect()
                    ),
                    case_insensitive: true,
                    variant: 1,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "HasAnyCaseInsensitive",
                "rhs": [
                    "CoM",
                    "oRg",
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.coM")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.Org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.net")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_ip_in() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"ip.addr in [ 127.0.0.0/8, ::1, 10.0.0.0..10.0.255.255 ]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ip.addr")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf {
                    rhs: RhsValues::Ip(vec![
                        IpRange::Cidr(IpCidr::new([127, 0, 0, 0].into(), 8).unwrap()),
                        IpRange::Cidr(IpCidr::new_host([0, 0, 0, 0, 0, 0, 0, 1].into())),
                        IpRange::Explicit(ExplicitIpRange::V4(
                            [10, 0, 0, 0].into()..=[10, 0, 255, 255].into()
                        )),
                    ]),
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "ip.addr",
                "op": "OneOf",
                "rhs": [
                    "127.0.0.0/8",
                    "::1",
                    { "start": "10.0.0.0", "end": "10.0.255.255" },
                ]
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([127, 0, 0, 1]))
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("ip.addr"), IpAddr::from([127, 0, 0, 3]))
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("ip.addr"), IpAddr::from([255, 255, 255, 255]))
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("ip.addr"), IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]))
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("ip.addr"), IpAddr::from([0, 0, 0, 0, 0, 0, 0, 2]))
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_contains_str() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.host contains "abc""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Contains {
                    rhs: "abc".to_owned().into(),
                    variant: 0,
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Contains",
                "rhs": "abc",
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "abc.net.au")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_contains_bytes() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.host contains 6F:72:67"#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Contains {
                    rhs: vec![0x6F, 0x72, 0x67].into(),
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Contains",
                "rhs": [0x6F, 0x72, 0x67],
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn like_str() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.host like "abc.*""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Like {
                    rhs: Like::parse_str("abc.*"),
                    variant: 0,
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Like",
                "rhs": {
                    "matcher": {
                        "case_insensitive": false,
                        "pattern": ["a", "b", "c", ".", "*"]
                    }
                },
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "abc.net.au")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_int_compare() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"tcp.port < 8000"#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThan(1),
                    rhs: RhsValue::Int(8000)
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "LessThan",
                "rhs": 8000,
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 8080).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_array_contains_str() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.cookies[0] contains "abc""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Contains {
                    rhs: "abc".to_owned().into(),
                    variant: 0,
                },
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "abc".into()).unwrap();
            arr
        });

        ctx.set_field_value(field("http.cookies"), cookies).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "def".into()).unwrap();
            arr
        });

        ctx.set_field_value(field("http.cookies"), cookies).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_map_of_bytes_contains_str() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.headers["host"] contains "abc""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapKey("host".to_string())],
                },
                op: ComparisonOpExpr::Contains {
                    rhs: "abc".to_owned().into(),
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.headers",
                    {"kind": "MapKey", "value": "host"}
                ],
                "op": "Contains",
                "rhs": "abc",
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"host", "example.org".into()).unwrap();
            map
        });

        ctx.set_field_value(field("http.headers"), headers).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"host", "abc.net.au".into()).unwrap();
            map
        });

        ctx.set_field_value(field("http.headers"), headers).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_compare_with_echo_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"echo(http.host) == "example.org""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "echo",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_compare_with_lowercase_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"lowercase(http.host) == "example.org""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("lowercase").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "lowercase",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "EXAMPLE.COM")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "EXAMPLE.ORG")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_missing_array_value_equal() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.cookies[0] == "example.org""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.cookies",
                    {"kind": "ArrayIndex", "value": 0}
                ],
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.cookies"), Array::new(Type::Bytes))
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_missing_array_value_not_equal() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.cookies[0] != "example.org""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::NotEqual(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.cookies",
                    {"kind": "ArrayIndex", "value": 0}
                ],
                "op": "NotEqual",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.cookies"), Array::new(Type::Bytes))
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_missing_map_value_equal() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.headers["missing"] == "example.org""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapKey("missing".into())],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.headers",
                    {"kind": "MapKey", "value": "missing"}
                ],
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.headers"), Map::new(Type::Bytes))
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_missing_map_value_not_equal() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"http.headers["missing"] != "example.org""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapKey("missing".into())],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::NotEqual(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.headers",
                    {"kind": "MapKey", "value": "missing"}
                ],
                "op": "NotEqual",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.headers"), Map::new(Type::Bytes))
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_bytes_compare_with_concat_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"concat(http.host) == "example.org""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "concat",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "example.co.uk")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));

        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"concat(http.host, ".org") == "example.org""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.host")),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                ".org".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "concat",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        },
                        {
                            "kind": "Literal",
                            "value": ".org"
                        },
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example").unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("http.host"), "cloudflare")
            .unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_filter_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"filter(http.cookies, array.of.bool)[0] == "three""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("filter").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.cookies")),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("array.of.bool")),
                                indexes: vec![],
                            }),
                        ],
                        return_type: Type::Array(Box::new(Type::Bytes)),
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("three".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "filter",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": "http.cookies"
                            },
                            {
                                "kind": "IndexExpr",
                                "value": "array.of.bool"
                            }
                        ]
                    },
                    {"kind": "ArrayIndex", "value": 0},
                ],
                "op": "Equal",
                "rhs": "three"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        let booleans = LhsValue::Array({
            let mut arr = Array::new(Type::Bool);
            arr.insert(0, false.into()).unwrap();
            arr.insert(1, false.into()).unwrap();
            arr.insert(2, true.into()).unwrap();
            arr
        });
        ctx.set_field_value(field("array.of.bool"), booleans)
            .unwrap();

        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_map_each_on_array_with_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"concat(http.cookies[*], "-cf")[2] == "three-cf""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.cookies")),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(2)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("three-cf".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "concat",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.cookies", {"kind": "MapEach"}],
                            },
                            {
                                "kind": "Literal",
                                "value": "-cf"
                            }
                        ]
                    },
                    {"kind": "ArrayIndex", "value": 2},
                ],
                "op": "Equal",
                "rhs": "three-cf"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_map_each_on_map_with_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"concat(http.headers[*], "-cf")[2] in ["one-cf", "two-cf", "three-cf"]"#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.headers")),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(2)],
                },
                op: ComparisonOpExpr::OneOf {
                    rhs: RhsValues::Bytes(vec![
                        "one-cf".to_owned().into(),
                        "two-cf".to_owned().into(),
                        "three-cf".to_owned().into()
                    ]),
                    variant: 0,
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "concat",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.headers", {"kind": "MapEach"}],
                            },
                            {
                                "kind": "Literal",
                                "value": "-cf"
                            }
                        ]
                    },
                    {"kind": "ArrayIndex", "value": 2},
                ],
                "op": "OneOf",
                "rhs": ["one-cf", "two-cf", "three-cf"],
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"0", "one".into()).unwrap();
            map.insert(b"1", "two".into()).unwrap();
            map.insert(b"2", "three".into()).unwrap();
            map
        });
        ctx.set_field_value(field("http.headers"), headers).unwrap();

        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_map_each_on_array_for_cmp() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.cookies[*] == "three""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("three".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": ["http.cookies", {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "three",
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(
            expr.execute_vec(ctx, &VARIABLES, &Default::default()),
            vec![false, false, true].into_boxed_slice()
        );
    }

    #[test]
    fn test_map_each_on_map_for_cmp() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.headers[*] == "three""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("three".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

        assert_json!(
            expr,
            {
                "lhs": ["http.headers", {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "three",
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"0", "one".into()).unwrap();
            map.insert(b"1", "two".into()).unwrap();
            map.insert(b"2", "three".into()).unwrap();
            map
        });
        ctx.set_field_value(field("http.headers"), headers).unwrap();

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr
            .execute_vec(ctx, &VARIABLES, &Default::default())
            .iter()
        {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 2);
        assert_eq!(true_count, 1);
    }

    #[test]
    fn test_map_each_on_array_full() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(
                r#"concat(http.cookies[*], "-cf")[*] == "three-cf""#,
                &SCHEME,
                &VARIABLES
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.cookies")),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("three-cf".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "concat",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.cookies", {"kind": "MapEach"}],
                            },
                            {
                                "kind": "Literal",
                                "value": "-cf"
                            }
                        ]
                    },
                    {"kind": "MapEach"},
                ],
                "op": "Equal",
                "rhs": "three-cf"
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(
            expr.execute_vec(ctx, &VARIABLES, &Default::default()),
            vec![false, false, true].into_boxed_slice()
        );
    }

    #[test]
    fn test_map_each_on_array_len_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"len(http.cookies[*])[*] > 3"#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("len").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.cookies")),
                            indexes: vec![FieldIndex::MapEach],
                        }),],
                        return_type: Type::Int,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::GreaterThan(1),
                    rhs: RhsValue::Int(3),
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "len",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.cookies", {"kind": "MapEach"}],
                            }
                        ]
                    },
                    {"kind": "MapEach"},
                ],
                "op": "GreaterThan",
                "rhs": 3
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(
            expr.execute_vec(ctx, &VARIABLES, &Default::default()),
            vec![false, false, true].into_boxed_slice()
        );
    }

    #[test]
    fn test_map_each_error() {
        assert_err!(
            ComparisonExpr::lex_with_2(r#"http.host[*] == "three""#, &SCHEME, &VARIABLES),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            ComparisonExpr::lex_with_2(r#"ip.addr[*] == 127.0.0.1"#, &SCHEME, &VARIABLES),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Ip,
            }),
            "[*]"
        );

        assert_err!(
            ComparisonExpr::lex_with_2(r#"ssl[*]"#, &SCHEME, &VARIABLES),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bool,
            }),
            "[*]"
        );

        assert_err!(
            ComparisonExpr::lex_with_2(r#"tcp.port[*] == 80"#, &SCHEME, &VARIABLES),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Int,
            }),
            "[*]"
        );
    }

    #[test]
    fn test_number_in_list() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"tcp.port in $int_list"#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOfVariable {
                    var: Variable {
                        name: "int_list".into(),
                        ty: Some(VariableType::IntList),
                    },
                    variant: 0
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "var": {
                    "name": "int_list",
                    "ty": "IntList"
                },
                "variant": 0
            }
        );

        let expr = expr.compile(&VARIABLES);
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 1000).unwrap();
        assert!(expr.execute_one(ctx, &VARIABLES, &Default::default()));

        ctx.set_field_value(field("tcp.port"), 1001).unwrap();
        assert!(!expr.execute_one(ctx, &VARIABLES, &Default::default()));
    }

    #[test]
    fn test_map_each_nested() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.parts[*][*] == "[5][5]""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.parts")),
                    indexes: vec![FieldIndex::MapEach, FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("[5][5]".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

        assert_json!(
            expr,
            {
                "lhs": ["http.parts", {"kind": "MapEach"}, {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "[5][5]",
            }
        );

        let expr1 = expr.compile(&VARIABLES);

        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.parts[5][*] == "[5][5]""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.parts")),
                    indexes: vec![FieldIndex::ArrayIndex(5), FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("[5][5]".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

        assert_json!(
            expr,
            {
                "lhs": ["http.parts", {"kind": "ArrayIndex", "value": 5}, {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "[5][5]",
            }
        );

        let expr2 = expr.compile(&VARIABLES);

        let expr = assert_ok!(
            ComparisonExpr::lex_with_2(r#"http.parts[*][5] == "[5][5]""#, &SCHEME, &VARIABLES),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.parts")),
                    indexes: vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(5)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("[5][5]".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

        assert_json!(
            expr,
            {
                "lhs": ["http.parts", {"kind": "MapEach"}, {"kind": "ArrayIndex", "value": 5}],
                "op": "Equal",
                "rhs": "[5][5]",
            }
        );

        let expr3 = expr.compile(&VARIABLES);

        let ctx = &mut ExecutionContext::new(&SCHEME);

        let mut parts = Array::new(Type::Array(Box::new(Type::Bytes)));
        for i in 0..10 {
            let mut nested_arr = Array::new(Type::Bytes);
            for j in 0..10 {
                nested_arr
                    .push(LhsValue::Bytes(
                        format!("[{}][{}]", i, j).into_bytes().into(),
                    ))
                    .unwrap();
            }
            parts.push(LhsValue::Array(nested_arr)).unwrap();
        }

        ctx.set_field_value(field("http.parts"), parts).unwrap();

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr1
            .execute_vec(ctx, &VARIABLES, &Default::default())
            .iter()
        {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 99);
        assert_eq!(true_count, 1);

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr2
            .execute_vec(ctx, &VARIABLES, &Default::default())
            .iter()
        {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 9);
        assert_eq!(true_count, 1);

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr3
            .execute_vec(ctx, &VARIABLES, &Default::default())
            .iter()
        {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 9);
        assert_eq!(true_count, 1);
    }
}
