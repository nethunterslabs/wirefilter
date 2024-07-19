use crate::{
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    lhs_types::{Array, ArrayIterator, Map, MapIter, MapValuesIntoIter},
    rhs_types::{
        Bytes, FloatRange, IntRange, IpRange, Regex, UninhabitedArray, UninhabitedBool,
        UninhabitedMap, UninhabitedRegex,
    },
    scheme::{FieldIndex, IndexAccessError},
    strict_partial_ord::StrictPartialOrd,
    LexErrorKind,
};
use ordered_float::OrderedFloat;
use serde::{
    de::{DeserializeSeed, Deserializer},
    Deserialize, Serialize, Serializer,
};
use sliceslice::Needle;
use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    convert::TryFrom,
    fmt::{self, Debug, Formatter},
    iter::once,
    net::{IpAddr, Ipv4Addr},
};
use thiserror::Error;

fn lex_rhs_values<'i, T: Lex<'i>>(input: &'i str) -> LexResult<'i, Vec<T>> {
    let mut input = expect(input, "[")?;
    let mut res = Vec::new();
    let mut index = 0;
    input = skip_space(input);
    loop {
        if let Ok(rest) = expect(input, "]") {
            input = rest;
            return Ok((res, input));
        } else {
            let (item, rest) = T::lex(input)?;
            res.push(item);
            input = rest;
            input = skip_space(input);

            match expect(input, ",") {
                Ok(rest) => {
                    input = rest;
                    input = skip_space(input);

                    if let Ok(rest) = expect(input, "]") {
                        input = rest;
                        return Ok((res, input));
                    }
                }
                Err(e) => {
                    if let Ok(rest) = expect(input, "]") {
                        input = rest;
                        return Ok((res, input));
                    } else if index > 0 {
                        return Err(e);
                    }
                }
            }
        }
        index += 1;
    }
}

/// An enum describing the expected type when a
/// TypeMismatchError occurs
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpectedType {
    /// Fully identified expected type
    Type(Type),
    /// Loosely identified array type
    /// Usefull when expecting an array without
    /// knowing of which specific value type
    Array,
    /// Loosely identified map type
    /// Usefull when expecting a map without
    /// knowing of which specific value type
    Map,
}

impl From<Type> for ExpectedType {
    fn from(ty: Type) -> Self {
        ExpectedType::Type(ty)
    }
}

type ExpectedTypeList = HashSet<ExpectedType>;

impl From<Type> for ExpectedTypeList {
    fn from(ty: Type) -> Self {
        once(ExpectedType::Type(ty)).collect()
    }
}

impl From<ExpectedType> for ExpectedTypeList {
    fn from(ty: ExpectedType) -> Self {
        once(ty).collect()
    }
}

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Error)]
#[error("expected value of type {expected:?}, but got {actual:?}")]
pub struct TypeMismatchError {
    /// Expected value type.
    pub expected: ExpectedTypeList,
    /// Provided value type.
    pub actual: Type,
}

/// An error that occurs when the inner value cannot be extracted
/// as the expected type from an LhsValue.
#[derive(Error, Debug)]
pub enum LhsValueAsError {
    #[error("{0}")]
    TypeMismatch(#[source] TypeMismatchError),
    #[error("Error parsing UTF-8: {0}")]
    Utf8Error(#[from] std::str::Utf8Error),
    #[error("Error parsing UTF-8: {0}")]
    FromUtf8Error(#[from] std::string::FromUtf8Error),
}

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Error)]
pub enum SetValueError {
    #[error("{0}")]
    TypeMismatch(#[source] TypeMismatchError),
    #[error("{0}")]
    IndexAccess(#[source] IndexAccessError),
}

macro_rules! replace_underscore {
    ($name:ident ($val_ty:ty)) => {
        Type::$name(_)
    };
    ($name:ident) => {
        Type::$name
    };
}

macro_rules! specialized_get_type {
    (Array, $value:ident) => {
        $value.get_type()
    };
    (Map, $value:ident) => {
        $value.get_type()
    };
    ($name:ident, $value:ident) => {
        Type::$name
    };
}

macro_rules! specialized_try_from {
    (Array) => {
        ExpectedType::Array
    };
    (Map) => {
        ExpectedType::Map
    };
    ($name:ident) => {
        ExpectedType::Type(Type::$name)
    };
}

/// This macro generates `Type`, `LhsValue`, `RhsValue`, `RhsValues`.
///
/// Before the parenthesis is the variant for the `Type` enum (`Type::Ip`).
/// First argument is the corresponding `LhsValue` variant
/// (`LhsValue::Ip(IpAddr)`). Second argument is the corresponding `RhsValue`
/// variant (`RhsValue::Ip(IpAddr)`). Third argument is the corresponding
/// `RhsValues` variant (`RhsValues::Ip(Vec<IpRange>)`) for the curly bracket
/// syntax. eg `num in [1, 5]`
///
/// ```ignore
/// declare_types! {
///     Ip(IpAddr | IpAddr | IpRange),
/// }
/// ```
macro_rules! declare_types {
    // This is just to be used by the other arm.
    ($(# $attrs:tt)* enum $name:ident $(<$lt:tt>)* { $($(# $vattrs:tt)* $variant:ident ( $ty:ty ) , )* }) => {
        $(# $attrs)*
        #[repr(u8)]
        pub enum $name $(<$lt>)* {
            $($(# $vattrs)* $variant($ty),)*
        }

        impl $(<$lt>)* GetType for $name $(<$lt>)* {
            fn get_type(&self) -> Type {
                match self {
                    $($name::$variant(_value) => specialized_get_type!($variant, _value),)*
                }
            }
        }

        impl $(<$lt>)* Debug for $name $(<$lt>)* {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                match self {
                    $($name::$variant(inner) => Debug::fmt(inner, f),)*
                }
            }
        }
    };

    // This is the entry point for the macro.
    ($($(# $attrs:tt)* $name:ident $([$val_ty:ty])? ( $(# $lhs_attrs:tt)* $lhs_ty:ty | $rhs_ty:ty | $multi_rhs_ty:ty| ( $( $(#[$variable_value_docs:meta])* $variable_value_ty_name:ident ($variable_value_ty:ty) , )* ) | ( $( $(#[$case_value_docs:meta])* $case_value_ty_name:ident $(($case_value_ty:ty))? , )* ) ) , )*) => {
        /// Enumeration of supported types for field values.
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize, Hash)]
        pub enum Type {
            $($(# $attrs)* $name$(($val_ty))?,)*
        }

        /// Enumeration of types for case values.
        ///
        /// These are used in case statements to store pattern values.
        #[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
        pub enum CasePatternValue {
            $(
                $(# $attrs)*
                $(
                    $(#[$case_value_docs])*
                    $case_value_ty_name $(($case_value_ty))?,
                )*
            )*
        }

        /// Enumeration of types for variable values.
        ///
        /// These are used in the [scheme](::Scheme) to store variable values
        /// which can then be used in [filters](::Filter) for comparisons.
        #[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
        pub enum VariableValue {
            $(
                $(# $attrs)*
                $(
                    $(#[$variable_value_docs])*
                    $variable_value_ty_name($variable_value_ty),
                )*
            )*
        }

        impl VariableValue {
            /// Returns the variable type of the variable value.
            pub fn get_variable_type(&self) -> VariableType {
                match self {
                    $(
                        $(
                            VariableValue::$variable_value_ty_name(_) => VariableType::$variable_value_ty_name,
                        )*
                    )*
                }
            }
        }

        /// Enumeration of supported types for variable values.
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Deserialize, Serialize, Hash)]
        pub enum VariableType {
            $(
                $(# $attrs)*
                $(
                    $(#[$variable_value_docs])*
                    $variable_value_ty_name,
                )*
            )*
        }

        $($(
            impl From<$variable_value_ty> for VariableValue {
                fn from(value: $variable_value_ty) -> Self {
                    VariableValue::$variable_value_ty_name(value)
                }
            }
        )*)*

        declare_types! {
            /// An LHS value provided for filter execution.
            ///
            /// These are passed to the [execution context](::ExecutionContext)
            /// and are used by [filters](::Filter)
            /// for execution and comparisons.
            #[derive(PartialEq, Eq, Hash, Clone, Deserialize)]
            #[serde(untagged)]
            enum LhsValue<'a> {
                $($(# $attrs)* $(# $lhs_attrs)* $name($lhs_ty),)*
            }
        }

        $(impl<'a> From<$lhs_ty> for LhsValue<'a> {
            fn from(value: $lhs_ty) -> Self {
                LhsValue::$name(value)
            }
        })*

        $(impl<'a> TryFrom<LhsValue<'a>> for $lhs_ty {
            type Error = TypeMismatchError;

            fn try_from(value: LhsValue<'a>) -> Result<$lhs_ty, TypeMismatchError> {
                match value {
                    LhsValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

        $(impl<'a> TryFrom<&'a LhsValue<'a>> for &'a $lhs_ty {
            type Error = TypeMismatchError;

            fn try_from(value: &'a LhsValue<'a>) -> Result<&'a $lhs_ty, TypeMismatchError> {
                match value {
                    LhsValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

        declare_types! {
            /// An RHS value parsed from a filter string.
            #[derive(PartialEq, Eq, Clone, Hash, Serialize)]
            #[serde(untagged)]
            enum RhsValue {
                $($(# $attrs)* $name($rhs_ty),)*
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValue {
            fn lex_with(input: &str, ty: Type) -> LexResult<'_, Self> {
                Ok(match ty {
                    $(replace_underscore!($name $(($val_ty))?) => {
                        let (value, input) = <$rhs_ty>::lex(input)?;
                        (RhsValue::$name(value), input)
                    })*
                })
            }
        }

        impl<'a> PartialOrd<RhsValue> for LhsValue<'a> {
            fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
                match (self, other) {
                    $((LhsValue::$name(lhs), RhsValue::$name(rhs)) => {
                        lhs.strict_partial_cmp(rhs)
                    },)*
                    _ => None,
                }
            }
        }

        declare_types! {
            /// A typed group of a list of values.
            ///
            /// This is used for `field in [... ]` operation that allows
            /// only same-typed values in a list.
            #[derive(PartialEq, Eq, Clone, Hash, Serialize)]
            #[serde(untagged)]
            enum RhsValues {
                $($(# $attrs)* $name(Vec<$multi_rhs_ty>),)*
            }
        }

        impl From<RhsValue> for RhsValues {
            fn from(rhs: RhsValue) -> Self {
                match rhs {
                    $(RhsValue::$name(rhs) => RhsValues::$name(vec![rhs.into()]),)*
                }
            }
        }

        impl RhsValues {
            /// Appends a value to the back of the collection.
            pub fn push(&mut self, rhs: RhsValue) -> Result<(), TypeMismatchError> {
                match self {
                    $(RhsValues::$name(vec) => match rhs {
                        RhsValue::$name(rhs) => Ok(vec.push(rhs.into())),
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: rhs.get_type(),
                        }),
                    },)*
                }
            }

            /// Moves all the values of `other` into `self`, leaving `other` empty.
            pub fn append(&mut self, other: &mut Self) -> Result<(), TypeMismatchError> {
                match self {
                    $(RhsValues::$name(vec) => match other {
                        RhsValues::$name(other) => Ok(vec.append(other)),
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: other.get_type(),
                        }),
                    },)*
                }
            }

            /// Extends the collection with the values of another collection.
            pub fn extend(&mut self, other: Self) -> Result<(), TypeMismatchError> {
                match self {
                    $(RhsValues::$name(vec) => match other {
                        RhsValues::$name(other) => Ok(vec.extend(other)),
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: other.get_type(),
                        }),
                    },)*
                }
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValues {
            fn lex_with(input: &str, ty: Type) -> LexResult<'_, Self> {
                Ok(match ty {
                    $(replace_underscore!($name $(($val_ty))?) => {
                        let (value, input) = lex_rhs_values(input)?;
                        (RhsValues::$name(value), input)
                    })*
                })
            }
        }
    };
}

impl Type {
    /// Returns the inner type when available (e.g: for a Map)
    pub fn next(&self) -> Option<Type> {
        match self {
            Type::Array(ty) => Some(*ty.clone()),
            Type::Map(ty) => Some(*ty.clone()),
            _ => None,
        }
    }
}

/// Provides a way to get a [`Type`] of the implementor.
pub trait GetType {
    /// Returns a type.
    fn get_type(&self) -> Type;
}

impl GetType for Type {
    fn get_type(&self) -> Type {
        self.clone()
    }
}

impl<'a> StrictPartialOrd<RhsValue> for LhsValue<'a> {}

impl<'a> PartialEq<RhsValue> for LhsValue<'a> {
    fn eq(&self, other: &RhsValue) -> bool {
        self.strict_partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl<'a> PartialOrd<VariableValue> for LhsValue<'a> {
    fn partial_cmp(&self, other: &VariableValue) -> Option<Ordering> {
        match (self, other) {
            (LhsValue::Int(lhs), VariableValue::Int(rhs)) => lhs.partial_cmp(rhs),
            (LhsValue::Float(lhs), VariableValue::Float(rhs)) => lhs.partial_cmp(rhs),
            (LhsValue::Bool(lhs), VariableValue::Bool(rhs)) => lhs.partial_cmp(rhs),
            (LhsValue::Bytes(lhs), VariableValue::Bytes(rhs)) => {
                lhs.as_bytes().partial_cmp(rhs.as_bytes())
            }
            (LhsValue::Ip(lhs), VariableValue::Ip(rhs)) => lhs.partial_cmp(rhs),
            _ => None,
        }
    }
}

impl<'a> StrictPartialOrd<VariableValue> for LhsValue<'a> {}

impl<'a> PartialEq<VariableValue> for LhsValue<'a> {
    fn eq(&self, other: &VariableValue) -> bool {
        self.strict_partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl VariableType {
    /// Checks if a Type is compatible with a VariableType.
    pub fn is_compatible(&self, ty: &Type) -> bool {
        matches!(
            (self, ty),
            (VariableType::Bool, Type::Bool)
                | (VariableType::BoolList, Type::Bool)
                | (VariableType::Int, Type::Int)
                | (VariableType::IntRange, Type::Int)
                | (VariableType::IntList, Type::Int)
                | (VariableType::IntRangeList, Type::Int)
                | (VariableType::Float, Type::Float)
                | (VariableType::FloatRange, Type::Float)
                | (VariableType::FloatList, Type::Float)
                | (VariableType::FloatRangeList, Type::Float)
                | (VariableType::Bytes, Type::Bytes)
                | (VariableType::BytesList, Type::Bytes)
                | (VariableType::Regex, Type::Bytes)
                | (VariableType::Ip, Type::Ip)
                | (VariableType::IpRange, Type::Ip)
                | (VariableType::IpList, Type::Ip)
                | (VariableType::IpRangeList, Type::Ip)
        )
    }

    /// Returns the Type of a VariableType.
    pub fn get_type(&self) -> Option<Type> {
        match self {
            VariableType::Bool => Some(Type::Bool),
            VariableType::Int => Some(Type::Int),
            VariableType::Float => Some(Type::Float),
            VariableType::Bytes => Some(Type::Bytes),
            VariableType::Ip => Some(Type::Ip),
            _ => None,
        }
    }
}

impl VariableValue {
    /// Returns the type of the variable.
    #[inline]
    pub fn get_type(&self) -> Option<Type> {
        self.get_variable_type().get_type()
    }

    /// Checks if a variable match is supported with a given [`Type`](enum@Type)
    /// for an [`LhsValue`](enum@LhsValue).
    pub fn is_supported_lhs_value_match(&self, ty: &Type) -> bool {
        matches!(
            (self, ty),
            (VariableValue::Bool(_), Type::Bool)
                | (VariableValue::BoolList(_), Type::Bool)
                | (VariableValue::Int(_), Type::Int)
                | (VariableValue::IntRange(_), Type::Int)
                | (VariableValue::IntList(_), Type::Int)
                | (VariableValue::IntRangeList(_), Type::Int)
                | (VariableValue::Float(_), Type::Float)
                | (VariableValue::FloatRange(_), Type::Float)
                | (VariableValue::FloatList(_), Type::Float)
                | (VariableValue::FloatRangeList(_), Type::Float)
                | (VariableValue::Bytes(_), Type::Bytes)
                | (VariableValue::BytesList(_), Type::Bytes)
                | (VariableValue::Regex(_), Type::Bytes)
                | (VariableValue::Ip(_), Type::Ip)
                | (VariableValue::IpRange(_), Type::Ip)
                | (VariableValue::IpList(_), Type::Ip)
                | (VariableValue::IpRangeList(_), Type::Ip)
        )
    }

    /// Checks if a variable matches a [`LhsValue`](enum@LhsValue).
    pub fn matches_lhs_value(&self, value: &LhsValue<'_>) -> bool {
        match (self, value) {
            (VariableValue::Bool(a), LhsValue::Bool(b)) => a == b,
            (VariableValue::BoolList(a), LhsValue::Bool(b)) => a.contains(b),

            (VariableValue::Int(a), LhsValue::Int(b)) => a == b,
            (VariableValue::IntRange(a), LhsValue::Int(b)) => a.0.contains(b),
            (VariableValue::IntList(a), LhsValue::Int(b)) => a.contains(b),
            (VariableValue::IntRangeList(a), LhsValue::Int(b)) => {
                a.iter().any(|range| range.0.contains(b))
            }

            (VariableValue::Float(a), LhsValue::Float(b)) => a == b,
            (VariableValue::FloatRange(a), LhsValue::Float(b)) => a.0.contains(b),
            (VariableValue::FloatList(a), LhsValue::Float(b)) => a.contains(b),
            (VariableValue::FloatRangeList(a), LhsValue::Float(b)) => {
                a.iter().any(|range| range.0.contains(b))
            }

            (VariableValue::Bytes(a), LhsValue::Bytes(b)) => a.as_bytes() == b.as_bytes(),
            (VariableValue::BytesList(a), LhsValue::Bytes(b)) => {
                a.iter().any(|x| x == b.as_bytes())
            }
            (VariableValue::Regex(a), LhsValue::Bytes(b)) => a.is_match(b),

            (VariableValue::Ip(a), LhsValue::Ip(b)) => a == b,
            (VariableValue::IpRange(a), LhsValue::Ip(b)) => a.contains(b),
            (VariableValue::IpList(a), LhsValue::Ip(b)) => a.contains(b),
            (VariableValue::IpRangeList(a), LhsValue::Ip(b)) => {
                a.iter().any(|range| range.contains(b))
            }

            _ => false,
        }
    }

    /// Checks if a variable type can be cast as a [`LhsValue`](enum@LhsValue).
    pub fn is_supported_as_lhs_value(&self, ty: &Type) -> bool {
        matches!(
            (self, ty),
            (VariableValue::Bool(_), Type::Bool)
                | (VariableValue::Int(_), Type::Int)
                | (VariableValue::Float(_), Type::Float)
                | (VariableValue::Bytes(_), Type::Bytes)
                | (VariableValue::Ip(_), Type::Ip)
        )
    }

    /// Casts a variable as a [`LhsValue`](enum@LhsValue).
    pub fn as_lhs_value(&self) -> Option<LhsValue<'static>> {
        match self {
            VariableValue::Bool(a) => Some(LhsValue::Bool(*a)),
            VariableValue::Int(a) => Some(LhsValue::Int(*a)),
            VariableValue::Float(a) => Some(LhsValue::Float(*a)),
            VariableValue::Bytes(a) => Some(LhsValue::Bytes(Cow::Owned(a.to_vec()))),
            VariableValue::Ip(a) => Some(LhsValue::Ip(*a)),
            _ => None,
        }
    }
}

impl CasePatternValue {
    /// Matches a case pattern value with a [`LhsValue`](enum@LhsValue).
    pub fn matches(&self, value: &LhsValue<'_>) -> bool {
        match (self, value) {
            (CasePatternValue::Bool, _) => true,
            (CasePatternValue::Int(a), LhsValue::Int(b)) => a == b,
            (CasePatternValue::IntRange(a), LhsValue::Int(b)) => a.0.contains(b),
            (CasePatternValue::Float(a), LhsValue::Float(b)) => a == b,
            (CasePatternValue::FloatRange(a), LhsValue::Float(b)) => a.0.contains(b),
            (CasePatternValue::Bytes(a), LhsValue::Bytes(b)) => a.as_bytes() == b.as_bytes(),
            (CasePatternValue::Ip(a), LhsValue::Ip(b)) => a == b,
            (CasePatternValue::IpRange(a), LhsValue::Ip(b)) => a.contains(b),
            _ => false,
        }
    }

    /// Checks if a case pattern value supports matching a [`Type`](enum@Type).
    pub fn is_supported_lhs_value_match(&self, ty: &Type) -> bool {
        matches!(
            (self, ty),
            (CasePatternValue::Int(_), Type::Int)
                | (CasePatternValue::IntRange(_), Type::Int)
                | (CasePatternValue::Float(_), Type::Float)
                | (CasePatternValue::FloatRange(_), Type::Float)
                | (CasePatternValue::Bytes(_), Type::Bytes)
                | (CasePatternValue::Ip(_), Type::Ip)
                | (CasePatternValue::IpRange(_), Type::Ip)
        )
    }

    pub(crate) fn lex_with_lhs_type<'i>(
        input: &'i str,
        ty: &Type,
    ) -> LexResult<'i, CasePatternValue> {
        if let Ok(rest) = expect(input, "_") {
            return Ok((CasePatternValue::Bool, rest));
        }

        match ty {
            Type::Int => {
                if let Ok((range, rest)) = IntRange::lex(input) {
                    Ok((CasePatternValue::IntRange(range), rest))
                } else {
                    let (value, rest) = i32::lex(input)?;
                    Ok((CasePatternValue::Int(value), rest))
                }
            }
            Type::Float => {
                if let Ok((range, rest)) = FloatRange::lex(input) {
                    Ok((CasePatternValue::FloatRange(range), rest))
                } else {
                    let (value, rest) = OrderedFloat::lex(input)?;
                    Ok((CasePatternValue::Float(value), rest))
                }
            }
            Type::Bytes => {
                let (value, rest) = Bytes::lex(input)?;
                Ok((CasePatternValue::Bytes(value), rest))
            }
            Type::Ip => {
                if let Ok((range, rest)) = IpRange::lex(input) {
                    Ok((CasePatternValue::IpRange(range), rest))
                } else {
                    let (value, rest) = IpAddr::lex(input)?;
                    Ok((CasePatternValue::Ip(value), rest))
                }
            }
            _ => Err((LexErrorKind::CasePatternsNotSupported(ty.clone()), input)),
        }
    }

    /// Returns the type of the case pattern value.
    pub fn get_type(&self) -> Option<Type> {
        match self {
            CasePatternValue::Bool => Some(Type::Bool),
            CasePatternValue::Int(_) => Some(Type::Int),
            CasePatternValue::IntRange(_) => Some(Type::Int),
            CasePatternValue::Float(_) => Some(Type::Float),
            CasePatternValue::FloatRange(_) => Some(Type::Float),
            CasePatternValue::Bytes(_) => Some(Type::Bytes),
            CasePatternValue::Ip(_) => Some(Type::Ip),
            CasePatternValue::IpRange(_) => Some(Type::Ip),
            CasePatternValue::Array(_) | CasePatternValue::Map(_) | CasePatternValue::Regex(_) => {
                None
            }
        }
    }

    /// Returns if it is a catch-all pattern.
    pub fn is_catch_all(&self) -> bool {
        matches!(self, CasePatternValue::Bool)
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
pub enum BytesOrString<'a> {
    BorrowedBytes(#[serde(borrow)] &'a [u8]),
    OwnedBytes(Vec<u8>),
    BorrowedString(#[serde(borrow)] &'a str),
    OwnedString(String),
}

impl<'a> BytesOrString<'a> {
    pub fn into_bytes(self) -> Cow<'a, [u8]> {
        match self {
            BytesOrString::BorrowedBytes(slice) => (*slice).into(),
            BytesOrString::OwnedBytes(vec) => vec.into(),
            BytesOrString::BorrowedString(str) => str.as_bytes().into(),
            BytesOrString::OwnedString(str) => str.into_bytes().into(),
        }
    }
}

// special case for simply passing bytes
impl<'a> From<&'a [u8]> for LhsValue<'a> {
    #[inline]
    fn from(b: &'a [u8]) -> Self {
        LhsValue::Bytes(Cow::Borrowed(b))
    }
}

impl From<Vec<u8>> for LhsValue<'static> {
    #[inline]
    fn from(b: Vec<u8>) -> Self {
        LhsValue::Bytes(Cow::Owned(b))
    }
}

// special cases for simply passing strings and string slices
impl<'a> From<&'a str> for LhsValue<'a> {
    #[inline]
    fn from(s: &'a str) -> Self {
        s.as_bytes().into()
    }
}

impl<'a> TryFrom<&'a LhsValue<'a>> for &'a [u8] {
    type Error = TypeMismatchError;

    fn try_from(value: &'a LhsValue<'_>) -> Result<Self, TypeMismatchError> {
        match value {
            LhsValue::Bytes(value) => Ok(value),
            _ => Err(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: value.get_type(),
            }),
        }
    }
}

impl<'a> From<&'a RhsValue> for LhsValue<'a> {
    fn from(rhs_value: &'a RhsValue) -> Self {
        match rhs_value {
            RhsValue::Ip(ip) => LhsValue::Ip(*ip),
            RhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Borrowed(bytes)),
            RhsValue::Int(integer) => LhsValue::Int(*integer),
            RhsValue::Float(float) => LhsValue::Float(*float),
            RhsValue::Bool(b) => match *b {},
            RhsValue::Array(a) => match *a {},
            RhsValue::Map(m) => match *m {},
            RhsValue::Regex(r) => match *r {},
        }
    }
}

impl<'a> From<RhsValue> for LhsValue<'a> {
    fn from(rhs_value: RhsValue) -> Self {
        match rhs_value {
            RhsValue::Ip(ip) => LhsValue::Ip(ip),
            RhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Owned(bytes.into())),
            RhsValue::Int(integer) => LhsValue::Int(integer),
            RhsValue::Float(float) => LhsValue::Float(float),
            RhsValue::Bool(b) => match b {},
            RhsValue::Array(a) => match a {},
            RhsValue::Map(m) => match m {},
            RhsValue::Regex(r) => match r {},
        }
    }
}

impl<'a> LhsValue<'a> {
    /// Converts a reference to an LhsValue to an LhsValue with an internal
    /// references
    pub fn as_ref(&'a self) -> Self {
        match self {
            LhsValue::Ip(ip) => LhsValue::Ip(*ip),
            LhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Borrowed(bytes)),
            LhsValue::Int(integer) => LhsValue::Int(*integer),
            LhsValue::Float(float) => LhsValue::Float(*float),
            LhsValue::Bool(b) => LhsValue::Bool(*b),
            LhsValue::Array(a) => LhsValue::Array(a.as_ref()),
            LhsValue::Map(m) => LhsValue::Map(m.as_ref()),
            LhsValue::Regex(r) => LhsValue::Regex(*r),
        }
    }

    /// Converts an `LhsValue` with borrowed data to a fully owned `LhsValue`.
    pub fn into_owned(self) -> LhsValue<'static> {
        match self {
            LhsValue::Ip(ip) => LhsValue::Ip(ip),
            LhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Owned(bytes.into_owned())),
            LhsValue::Int(i) => LhsValue::Int(i),
            LhsValue::Float(i) => LhsValue::Float(i),
            LhsValue::Bool(b) => LhsValue::Bool(b),
            LhsValue::Array(arr) => LhsValue::Array(arr.into_owned()),
            LhsValue::Map(map) => LhsValue::Map(map.into_owned()),
            LhsValue::Regex(r) => LhsValue::Regex(r),
        }
    }

    /// Retrieve an element from an LhsValue given a path item and a specified
    /// type.
    /// Returns a TypeMismatchError error if current type does not support it
    /// nested element.
    ///
    /// Both LhsValue::Array and LhsValue::Map support nested elements.
    pub fn get(&'a self, item: &FieldIndex) -> Result<Option<&'a LhsValue<'a>>, IndexAccessError> {
        match (self, item) {
            (LhsValue::Array(arr), FieldIndex::ArrayIndex(ref idx)) => Ok(arr.get(*idx as usize)),
            (_, FieldIndex::ArrayIndex(_)) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
            (LhsValue::Map(map), FieldIndex::MapKey(ref key)) => Ok(map.get(key.as_bytes())),
            (_, FieldIndex::MapKey(_)) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
            (_, FieldIndex::MapEach) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
        }
    }

    pub(crate) fn extract(
        self,
        item: &FieldIndex,
    ) -> Result<Option<LhsValue<'a>>, IndexAccessError> {
        match item {
            FieldIndex::ArrayIndex(idx) => match self {
                LhsValue::Array(arr) => Ok(arr.extract(*idx as usize)),
                _ => Err(IndexAccessError {
                    index: item.clone(),
                    actual: self.get_type(),
                }),
            },
            FieldIndex::MapKey(key) => match self {
                LhsValue::Map(map) => Ok(map.extract(key.as_bytes())),
                _ => Err(IndexAccessError {
                    index: item.clone(),
                    actual: self.get_type(),
                }),
            },
            FieldIndex::MapEach => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
        }
    }

    /// Set an element in an LhsValue given a path item and a specified value.
    /// Returns a TypeMismatchError error if current type does not support
    /// nested element or if value type is invalid.
    /// Only LhsValyue::Map supports nested elements for now.
    pub fn set<V: Into<LhsValue<'a>>>(
        &mut self,
        item: FieldIndex,
        value: V,
    ) -> Result<(), SetValueError> {
        let value = value.into();
        match item {
            FieldIndex::ArrayIndex(idx) => match self {
                LhsValue::Array(ref mut arr) => arr
                    .insert(idx as usize, value)
                    .map_err(SetValueError::TypeMismatch),
                _ => Err(SetValueError::IndexAccess(IndexAccessError {
                    index: item,
                    actual: self.get_type(),
                })),
            },
            FieldIndex::MapKey(name) => match self {
                LhsValue::Map(ref mut map) => map
                    .insert(name.as_bytes(), value)
                    .map_err(SetValueError::TypeMismatch),
                _ => Err(SetValueError::IndexAccess(IndexAccessError {
                    index: FieldIndex::MapKey(name),
                    actual: self.get_type(),
                })),
            },
            FieldIndex::MapEach => Err(SetValueError::IndexAccess(IndexAccessError {
                index: item,
                actual: self.get_type(),
            })),
        }
    }

    /// Returns an iterator over the Map or Array
    pub fn iter(&'a self) -> Option<Iter<'a>> {
        match self {
            LhsValue::Array(array) => Some(Iter::IterArray(array.as_slice().iter())),
            LhsValue::Map(map) => Some(Iter::IterMap(map.iter())),
            _ => None,
        }
    }

    /// Returns a default value for the type.
    pub fn default_value(ty: Type) -> LhsValue<'static> {
        match ty {
            Type::Bool => LhsValue::Bool(false),
            Type::Int => LhsValue::Int(0),
            Type::Float => LhsValue::Float(OrderedFloat(0.0)),
            Type::Bytes => LhsValue::Bytes(Cow::Owned(Vec::new())),
            Type::Ip => LhsValue::Ip(IpAddr::V4(Ipv4Addr::UNSPECIFIED)),
            Type::Array(inner_type) => LhsValue::Array(Array::new(*inner_type)),
            Type::Map(inner_type) => LhsValue::Map(Map::new(*inner_type)),
            Type::Regex => unreachable!(),
        }
    }

    /// Return the inner bytes of the LhsValue if it is Bytes.
    pub fn as_bytes(self) -> Result<Vec<u8>, LhsValueAsError> {
        match self {
            LhsValue::Bytes(bytes) => Ok(bytes.to_vec()),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a string slice if it is Bytes.
    pub fn as_str(&'a self) -> Result<&'a str, LhsValueAsError> {
        match self {
            LhsValue::Bytes(bytes) => {
                Ok(std::str::from_utf8(bytes).map_err(LhsValueAsError::Utf8Error)?)
            }
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a string if it is Bytes.
    pub fn as_string(self) -> Result<String, LhsValueAsError> {
        match self {
            LhsValue::Bytes(bytes) => {
                Ok(String::from_utf8(bytes.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?)
            }
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an i32 if it is Int.
    pub fn as_i32(&self) -> Result<i32, LhsValueAsError> {
        match self {
            LhsValue::Int(i) => Ok(*i),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Int.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an f64 if it is Float.
    pub fn as_f64(&self) -> Result<OrderedFloat<f64>, LhsValueAsError> {
        match self {
            LhsValue::Float(f) => Ok(*f),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Float.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a bool if it is Bool.
    pub fn as_bool(&self) -> Result<bool, LhsValueAsError> {
        match self {
            LhsValue::Bool(b) => Ok(*b),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an IpAddr if it is Ip.
    pub fn as_ip(&self) -> Result<IpAddr, LhsValueAsError> {
        match self {
            LhsValue::Ip(ip) => Ok(*ip),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Ip.into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an array of bytes if it is an Array of Bytes.
    pub fn as_array_bytes(self) -> Result<Vec<Vec<u8>>, LhsValueAsError> {
        match self {
            LhsValue::Array(array) => array
                .into_iter()
                .map(|value| match value {
                    LhsValue::Bytes(bytes) => Ok(bytes.to_vec()),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Bytes.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bytes)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an array of strings if it is an Array of Bytes.
    pub fn as_array_string(self) -> Result<Vec<String>, LhsValueAsError> {
        match self {
            LhsValue::Array(array) => array
                .into_iter()
                .map(|value| match value {
                    LhsValue::Bytes(bytes) => Ok(String::from_utf8(bytes.to_vec())
                        .map_err(LhsValueAsError::FromUtf8Error)?),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Bytes.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bytes)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an array of i32 if it is an Array of Int.
    pub fn as_array_i32(&self) -> Result<Vec<i32>, LhsValueAsError> {
        match self {
            LhsValue::Array(array) => array
                .as_slice()
                .iter()
                .map(|value| match value {
                    LhsValue::Int(i) => Ok(*i),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Int.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Int)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an array of f64 if it is an Array of Float.
    pub fn as_array_f64(&self) -> Result<Vec<OrderedFloat<f64>>, LhsValueAsError> {
        match self {
            LhsValue::Array(array) => array
                .as_slice()
                .iter()
                .map(|value| match value {
                    LhsValue::Float(f) => Ok(*f),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Float.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Float)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an array of bool if it is an Array of Bool.
    pub fn as_array_bool(&self) -> Result<Vec<bool>, LhsValueAsError> {
        match self {
            LhsValue::Array(array) => array
                .as_slice()
                .iter()
                .map(|value| match value {
                    LhsValue::Bool(b) => Ok(*b),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Bool.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as an array of IpAddr if it is an Array of Ip.
    pub fn as_array_ip(&self) -> Result<Vec<IpAddr>, LhsValueAsError> {
        match self {
            LhsValue::Array(array) => array
                .as_slice()
                .iter()
                .map(|value| match value {
                    LhsValue::Ip(ip) => Ok(*ip),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Ip.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Ip)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of bytes if it is a Map of Bytes.
    pub fn as_map_bytes(self) -> Result<HashMap<String, Vec<u8>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .into_iter()
                .map(|(key, value)| match value {
                    LhsValue::Bytes(bytes) => Ok((
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?,
                        bytes.to_vec(),
                    )),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Bytes.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Bytes)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of strings if it is a Map of Bytes.
    pub fn as_map_string(self) -> Result<HashMap<String, String>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .into_iter()
                .map(|(key, value)| match value {
                    LhsValue::Bytes(bytes) => Ok((
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?,
                        String::from_utf8(bytes.to_vec())
                            .map_err(LhsValueAsError::FromUtf8Error)?,
                    )),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Bytes.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Bytes)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of i32 if it is a Map of Int.
    pub fn as_map_i32(&self) -> Result<HashMap<String, i32>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| match value {
                    LhsValue::Int(i) => Ok((
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?,
                        *i,
                    )),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Int.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Int)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of f64 if it is a Map of Float.
    pub fn as_map_f64(&self) -> Result<HashMap<String, OrderedFloat<f64>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| match value {
                    LhsValue::Float(f) => Ok((
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?,
                        *f,
                    )),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Float.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Float)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of bool if it is a Map of Bool.
    pub fn as_map_bool(&self) -> Result<HashMap<String, bool>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| match value {
                    LhsValue::Bool(b) => Ok((
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?,
                        *b,
                    )),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Bool.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Bool)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of IpAddr if it is a Map of Ip.
    pub fn as_map_ip(&self) -> Result<HashMap<String, IpAddr>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| match value {
                    LhsValue::Ip(ip) => Ok((
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?,
                        *ip,
                    )),
                    _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                        expected: Type::Ip.into(),
                        actual: value.get_type(),
                    })),
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Ip)).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of arrays of bytes if it is a Map of Arrays of Bytes.
    pub fn as_map_array_bytes(self) -> Result<HashMap<String, Vec<Vec<u8>>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .into_iter()
                .map(|(key, value)| {
                    let key =
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?;
                    match value {
                        LhsValue::Array(array) => array
                            .into_iter()
                            .map(|value| match value {
                                LhsValue::Bytes(bytes) => Ok(bytes.to_vec()),
                                _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                                    expected: Type::Bytes.into(),
                                    actual: value.get_type(),
                                })),
                            })
                            .collect::<Result<Vec<Vec<u8>>, LhsValueAsError>>()
                            .map(|array| (key, array)),
                        _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                            expected: Type::Array(Box::new(Type::Bytes)).into(),
                            actual: value.get_type(),
                        })),
                    }
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Array(Box::new(Type::Bytes)))).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of arrays of strings if it is a Map of Arrays of Bytes.
    pub fn as_map_array_string(self) -> Result<HashMap<String, Vec<String>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .into_iter()
                .map(|(key, value)| {
                    let key =
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?;
                    match value {
                        LhsValue::Array(array) => array
                            .into_iter()
                            .map(|value| match value {
                                LhsValue::Bytes(bytes) => Ok(String::from_utf8(bytes.to_vec())
                                    .map_err(LhsValueAsError::FromUtf8Error)?),
                                _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                                    expected: Type::Bytes.into(),
                                    actual: value.get_type(),
                                })),
                            })
                            .collect::<Result<Vec<String>, LhsValueAsError>>()
                            .map(|array| (key, array)),
                        _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                            expected: Type::Array(Box::new(Type::Bytes)).into(),
                            actual: value.get_type(),
                        })),
                    }
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Array(Box::new(Type::Bytes)))).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of arrays of i32 if it is a Map of Arrays of Int.
    pub fn as_map_array_i32(&self) -> Result<HashMap<String, Vec<i32>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| {
                    let key =
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?;
                    match value {
                        LhsValue::Array(array) => array
                            .as_slice()
                            .iter()
                            .map(|value| match value {
                                LhsValue::Int(i) => Ok(*i),
                                _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                                    expected: Type::Int.into(),
                                    actual: value.get_type(),
                                })),
                            })
                            .collect::<Result<Vec<i32>, LhsValueAsError>>()
                            .map(|array| (key, array)),
                        _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                            expected: Type::Array(Box::new(Type::Int)).into(),
                            actual: value.get_type(),
                        })),
                    }
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Array(Box::new(Type::Int)))).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of arrays of f64 if it is a Map of Arrays of Float.
    pub fn as_map_array_f64(
        &self,
    ) -> Result<HashMap<String, Vec<OrderedFloat<f64>>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| {
                    let key =
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?;
                    match value {
                        LhsValue::Array(array) => array
                            .as_slice()
                            .iter()
                            .map(|value| match value {
                                LhsValue::Float(f) => Ok(*f),
                                _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                                    expected: Type::Float.into(),
                                    actual: value.get_type(),
                                })),
                            })
                            .collect::<Result<Vec<OrderedFloat<f64>>, LhsValueAsError>>()
                            .map(|array| (key, array)),
                        _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                            expected: Type::Array(Box::new(Type::Float)).into(),
                            actual: value.get_type(),
                        })),
                    }
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Array(Box::new(Type::Float)))).into(),
                actual: self.get_type(),
            })),
        }
    }

    /// Return as a map of arrays of bool if it is a Map of Arrays of Bool.
    pub fn as_map_array_bool(&self) -> Result<HashMap<String, Vec<bool>>, LhsValueAsError> {
        match self {
            LhsValue::Map(map) => map
                .iter()
                .map(|(key, value)| {
                    let key =
                        String::from_utf8(key.to_vec()).map_err(LhsValueAsError::FromUtf8Error)?;
                    match value {
                        LhsValue::Array(array) => array
                            .as_slice()
                            .iter()
                            .map(|value| match value {
                                LhsValue::Bool(b) => Ok(*b),
                                _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                                    expected: Type::Bool.into(),
                                    actual: value.get_type(),
                                })),
                            })
                            .collect::<Result<Vec<bool>, LhsValueAsError>>()
                            .map(|array| (key, array)),
                        _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                            expected: Type::Array(Box::new(Type::Bool)).into(),
                            actual: value.get_type(),
                        })),
                    }
                })
                .collect(),
            _ => Err(LhsValueAsError::TypeMismatch(TypeMismatchError {
                expected: Type::Map(Box::new(Type::Array(Box::new(Type::Bool)))).into(),
                actual: self.get_type(),
            })),
        }
    }
}

impl<'a> Serialize for LhsValue<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            LhsValue::Ip(ip) => ip.serialize(serializer),
            LhsValue::Bytes(bytes) => {
                if let Ok(s) = std::str::from_utf8(bytes) {
                    s.serialize(serializer)
                } else {
                    bytes.serialize(serializer)
                }
            }
            LhsValue::Int(num) => num.serialize(serializer),
            LhsValue::Float(float_num) => float_num.serialize(serializer),
            LhsValue::Bool(b) => b.serialize(serializer),
            LhsValue::Array(arr) => arr.serialize(serializer),
            LhsValue::Map(map) => map.serialize(serializer),
            LhsValue::Regex(regex) => regex.serialize(serializer),
        }
    }
}

pub(crate) struct LhsValueSeed<'a>(pub &'a Type);

impl<'de, 'a> DeserializeSeed<'de> for LhsValueSeed<'a> {
    type Value = LhsValue<'de>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        match self.0 {
            Type::Ip => Ok(LhsValue::Ip(std::net::IpAddr::deserialize(deserializer)?)),
            Type::Int => Ok(LhsValue::Int(i32::deserialize(deserializer)?)),
            Type::Float => Ok(LhsValue::Float(OrderedFloat::deserialize(deserializer)?)),
            Type::Bool => Ok(LhsValue::Bool(bool::deserialize(deserializer)?)),
            Type::Bytes => Ok(LhsValue::Bytes(
                BytesOrString::deserialize(deserializer)?.into_bytes(),
            )),
            Type::Array(ty) => Ok(LhsValue::Array({
                let mut arr = Array::new((**ty).clone());
                arr.deserialize(deserializer)?;
                arr
            })),
            Type::Map(ty) => Ok(LhsValue::Map({
                let mut map = Map::new((**ty).clone());
                map.deserialize(deserializer)?;
                map
            })),
            Type::Regex => Ok(LhsValue::Regex(UninhabitedRegex::deserialize(
                deserializer,
            )?)),
        }
    }
}

pub enum IntoIter<'a> {
    IntoArray(ArrayIterator<'a>),
    IntoMap(MapValuesIntoIter<'a>),
}

impl<'a> Iterator for IntoIter<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        match self {
            IntoIter::IntoArray(array) => array.next(),
            IntoIter::IntoMap(map) => map.next(),
        }
    }
}

impl<'a> IntoIterator for LhsValue<'a> {
    type Item = LhsValue<'a>;
    type IntoIter = IntoIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            LhsValue::Array(array) => IntoIter::IntoArray(array.into_iter()),
            LhsValue::Map(map) => IntoIter::IntoMap(map.values_into_iter()),
            _ => unreachable!(),
        }
    }
}

pub enum Iter<'a> {
    IterArray(std::slice::Iter<'a, LhsValue<'a>>),
    IterMap(MapIter<'a, 'a>),
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a LhsValue<'a>;

    fn next(&mut self) -> Option<&'a LhsValue<'a>> {
        match self {
            Iter::IterArray(array) => array.next(),
            Iter::IterMap(map) => map.next().map(|(_, v)| v),
        }
    }
}

declare_types!(
    /// A boolean.
    Bool(bool | UninhabitedBool | UninhabitedBool | (
        Bool(bool),
        /// Represents a list of booleans.
        BoolList(Vec<bool>),
    ) | (
        Bool,
    )),

    /// A 32-bit integer number.
    Int(i32 | i32 | IntRange | (
        Int(i32),
        /// Represents a range of integers.
        IntRange(IntRange),
        /// Represents a list of integers.
        IntList(Vec<i32>),
        /// Represents a list of integer ranges.
        IntRangeList(Vec<IntRange>),
    ) | (
        Int(i32),
        /// Represents a range of integers.
        IntRange(IntRange),
    )),

    /// A 64-bit floating point number.
    Float(OrderedFloat<f64> | OrderedFloat<f64> | FloatRange | (
        Float(OrderedFloat<f64>),
        /// Represents a range of floating point numbers.
        FloatRange(FloatRange),
        /// Represents a list of floating point numbers.
        FloatList(Vec<OrderedFloat<f64>>),
        /// Represents a list of floating point ranges.
        FloatRangeList(Vec<FloatRange>),
    ) | (
        Float(OrderedFloat<f64>),
        /// Represents a range of floating point numbers.
        FloatRange(FloatRange),
    )),

    /// An IPv4 or IPv6 address.
    ///
    /// These are represented as a single type to allow interop comparisons.
    Ip(IpAddr | IpAddr | IpRange | (
        Ip(IpAddr),
        /// Represents a range of IP addresses.
        IpRange(IpRange),
        /// Represents a list of IP addresses.
        IpList(Vec<IpAddr>),
        /// Represents a list of IP ranges.
        IpRangeList(Vec<IpRange>),
    ) | (
        Ip(IpAddr),
        /// Represents a range of IP addresses.
        IpRange(IpRange),
    )),

    /// A raw bytes or a string field.
    ///
    /// These are completely interchangeable in runtime and differ only in
    /// syntax representation, so we represent them as a single type.
    Bytes(#[serde(borrow)] Cow<'a, [u8]> | Bytes | Bytes | (
        Bytes(Vec<u8>),
        /// Represents a list of bytes.
        BytesList(Vec<Vec<u8>>),
    ) | (
        Bytes(Bytes),
    )),

    /// An Array of [`Type`].
    Array[Box<Type>](#[serde(skip_deserializing)] Array<'a> | UninhabitedArray | UninhabitedArray | (
        #[serde(skip)] Array(UninhabitedArray),
    ) | (
        #[serde(skip)] Array(UninhabitedArray),
    )),

    /// A Map of string to [`Type`].
    Map[Box<Type>](#[serde(skip_deserializing)] Map<'a> | UninhabitedMap | UninhabitedMap | (
        #[serde(skip)] Map(UninhabitedMap),
    ) | (
        #[serde(skip)] Map(UninhabitedMap),
    )),

    /// A regex pattern.
    Regex(UninhabitedRegex | UninhabitedRegex | UninhabitedRegex | (
        Regex(Regex),
    ) | (
        Regex(UninhabitedRegex),
    )),
);

#[test]
fn test_lhs_value_deserialize() {
    use std::str::FromStr;

    let ipv4: LhsValue<'_> = serde_json::from_str("\"127.0.0.1\"").unwrap();
    assert_eq!(ipv4, LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap()));

    let ipv6: LhsValue<'_> = serde_json::from_str("\"::1\"").unwrap();
    assert_eq!(ipv6, LhsValue::Ip(IpAddr::from_str("::1").unwrap()));

    let bytes: LhsValue<'_> = serde_json::from_str("\"a JSON string with unicode ❤\"").unwrap();
    assert_eq!(
        bytes,
        LhsValue::from(&b"a JSON string with unicode \xE2\x9D\xA4"[..])
    );

    let bytes =
        serde_json::from_str::<LhsValue<'_>>("\"a JSON string with escaped-unicode \\u2764\"")
            .unwrap();
    assert_eq!(
        bytes,
        LhsValue::from(&b"a JSON string with escaped-unicode \xE2\x9D\xA4"[..])
    );

    let bytes: LhsValue<'_> = serde_json::from_str("\"1337\"").unwrap();
    assert_eq!(bytes, LhsValue::from(&b"1337"[..]));

    let integer: LhsValue<'_> = serde_json::from_str("1337").unwrap();
    assert_eq!(integer, LhsValue::Int(1337));

    let b: LhsValue<'_> = serde_json::from_str("false").unwrap();
    assert_eq!(b, LhsValue::Bool(false));
}
