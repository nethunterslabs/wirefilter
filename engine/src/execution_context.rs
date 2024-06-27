use crate::{
    scheme::{Field, Scheme, SchemeMismatchError},
    types::{GetType, LhsValue, LhsValueSeed, TypeMismatchError, VariableValue},
};
use indexmap::IndexMap;
use serde::{
    de::{self, DeserializeSeed, Deserializer, MapAccess, Visitor},
    ser::{SerializeMap, Serializer},
    Serialize,
};
use std::{borrow::Cow, collections::HashMap, fmt, fmt::Debug};
use thiserror::Error;

/// An error that occurs when setting the field value in the
/// [`ExecutionContext`](struct@ExecutionContext)
#[derive(Debug, PartialEq, Error)]
pub enum SetFieldValueError {
    /// An error that occurs when trying to assign a value of the wrong type to
    /// a field.
    #[error("{0}")]
    TypeMismatchError(#[source] TypeMismatchError),

    /// An error that occurs when trying to set the value of a field from a
    /// different scheme.
    #[error("{0}")]
    SchemeMismatchError(#[source] SchemeMismatchError),
}

/// Variables that can be used in filters.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Variables {
    inner: IndexMap<String, VariableValue>,
}

impl Variables {
    /// Creates a new set of variables.
    pub fn new() -> Self {
        Variables {
            inner: IndexMap::new(),
        }
    }

    /// Inserts a variable into the set.
    pub fn add(&mut self, key: String, value: VariableValue) {
        self.inner.insert(key, value);
    }

    /// Extends the set with another set of variables.
    pub fn extend(&mut self, set: impl IntoIterator<Item = (String, VariableValue)>) {
        self.inner.extend(set);
    }

    /// Gets a variable from the set.
    pub fn get(&self, key: &str) -> Option<&VariableValue> {
        self.inner.get(key)
    }

    /// Checks if the set contains a variable.
    pub fn contains(&self, key: &str) -> bool {
        self.inner.contains_key(key)
    }

    /// Removes a variable from the set.
    /// Returns the value if it was present in the set.
    pub fn remove(&mut self, key: &str) -> Option<VariableValue> {
        self.inner.swap_remove(key)
    }

    /// Clears the set.
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Get the inner map.
    pub fn inner(&self) -> &IndexMap<String, VariableValue> {
        &self.inner
    }

    /// Get the mutable inner map.
    pub fn inner_mut(&mut self) -> &mut IndexMap<String, VariableValue> {
        &mut self.inner
    }
}

/// A state to be used to pass internal data to filters.
///
/// It is a map of keys to [`LhsValue`](::LhsValue) that can be used to pass data
/// to functions that aren't part of the execution context.
#[derive(Debug, Default, PartialEq)]
pub struct State<'e> {
    map: HashMap<String, LhsValue<'e>>,
}

impl<'e> State<'e> {
    /// Creates a new state.
    pub fn new() -> Self {
        State {
            map: HashMap::new(),
        }
    }

    /// Inserts a value into the state.
    pub fn insert(&mut self, key: String, value: LhsValue<'e>) {
        self.map.insert(key, value);
    }

    /// Gets a value from the state.
    pub fn get(&self, key: &str) -> Option<&LhsValue<'e>> {
        self.map.get(key)
    }

    /// Removes a value from the state.
    /// Returns the value if it was present in the state.
    pub fn remove(&mut self, key: &str) -> Option<LhsValue<'e>> {
        self.map.remove(key)
    }

    /// Clears the state.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Get the inner map.
    pub fn inner(&self) -> &HashMap<String, LhsValue<'e>> {
        &self.map
    }

    /// Get the mutable inner map.
    pub fn inner_mut(&mut self) -> &mut HashMap<String, LhsValue<'e>> {
        &mut self.map
    }
}

/// An execution context stores an associated [`Scheme`](struct@Scheme) and a
/// set of runtime values to execute [`Filter`](::Filter) against.
///
/// It acts as a map in terms of public API, but provides a constant-time
/// index-based access to values for a filter during execution.
#[derive(Debug, PartialEq)]
pub struct ExecutionContext<'e, U = ()> {
    scheme: &'e Scheme,
    values: Box<[Option<LhsValue<'e>>]>,
    user_data: U,
}

impl<'e, U> ExecutionContext<'e, U> {
    /// Creates an execution context associated with a given scheme.
    ///
    /// This scheme will be used for resolving any field names and indices.
    pub fn new<'s: 'e>(scheme: &'s Scheme) -> Self
    where
        U: Default,
    {
        Self::new_with(scheme, Default::default)
    }

    /// Creates an execution context associated with a given scheme.
    ///
    /// This scheme will be used for resolving any field names and indices.
    pub fn new_with<'s: 'e>(scheme: &'s Scheme, f: impl Fn() -> U) -> Self {
        let values_len = scheme.len();
        ExecutionContext {
            scheme,
            values: vec![None; values_len].into(),
            user_data: f(),
        }
    }

    /// Returns an associated scheme.
    pub fn scheme(&self) -> &'e Scheme {
        self.scheme
    }

    /// Sets a runtime value for a given field name.
    pub fn set_field_value<'v: 'e, V: Into<LhsValue<'v>>>(
        &mut self,
        field: Field<'e>,
        value: V,
    ) -> Result<(), SetFieldValueError> {
        if field.scheme() != self.scheme {
            return Err(SetFieldValueError::SchemeMismatchError(SchemeMismatchError));
        }
        let value = value.into();

        let field_type = field.get_type();
        let value_type = value.get_type();

        if field_type == value_type {
            self.values[field.index()] = Some(value);
            Ok(())
        } else {
            Err(SetFieldValueError::TypeMismatchError(TypeMismatchError {
                expected: field_type.into(),
                actual: value_type,
            }))
        }
    }

    #[inline]
    pub(crate) fn get_field_value_unchecked(&self, field: Field<'_>) -> &LhsValue<'_> {
        // This is safe because this code is reachable only from Filter::execute
        // which already performs the scheme compatibility check, but check that
        // invariant holds in the future at least in the debug mode.
        debug_assert!(self.scheme() == field.scheme());

        // For now we panic in this, but later we are going to align behaviour
        // with wireshark: resolve all subexpressions that don't have RHS value
        // to `false`.
        self.values[field.index()].as_ref().unwrap_or_else(|| {
            panic!(
                "Field {} was registered but not given a value",
                field.name()
            );
        })
    }

    /// Get the value of a field.
    pub fn get_field_value(&self, field: Field<'_>) -> Option<&LhsValue<'_>> {
        assert!(self.scheme() == field.scheme());

        self.values[field.index()].as_ref()
    }

    /// Get immutable reference to user data stored in
    /// this execution context with [`ExecutionContext::new_with`].
    #[inline]
    pub fn get_user_data(&self) -> &U {
        &self.user_data
    }

    /// Get mutable reference to user data stored in
    /// this execution context with [`ExecutionContext::new_with`].
    #[inline]
    pub fn get_user_data_mut(&mut self) -> &mut U {
        &mut self.user_data
    }

    /// Extract all values into a new [`ExecutionContext`].
    #[inline]
    pub fn take_with<T>(&mut self, default: impl Fn(&mut U) -> T) -> ExecutionContext<'e, T> {
        ExecutionContext {
            scheme: self.scheme,
            values: std::mem::take(&mut self.values),
            user_data: default(&mut self.user_data),
        }
    }
}

impl<'de, 'a, U> DeserializeSeed<'de> for &'a mut ExecutionContext<'de, U> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ExecutionContextVisitor<'de, 'a, U>(&'a mut ExecutionContext<'de, U>);

        impl<'de, 'a, U> Visitor<'de> for ExecutionContextVisitor<'de, 'a, U> {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a map of lhs value")
            }

            fn visit_map<M>(self, mut access: M) -> Result<(), M::Error>
            where
                M: MapAccess<'de>,
            {
                while let Some(key) = access.next_key::<Cow<'_, str>>()? {
                    let field = self
                        .0
                        .scheme
                        .get_field(&key)
                        .map_err(|_| de::Error::custom(format!("unknown field: {}", key)))?;
                    let value = access
                        .next_value_seed::<LhsValueSeed<'_>>(LhsValueSeed(&field.get_type()))?;
                    let field = self
                        .0
                        .scheme()
                        .get_field(&key)
                        .map_err(|_| de::Error::custom(format!("unknown field: {}", key)))?;
                    self.0.set_field_value(field, value).map_err(|e| match e {
                        SetFieldValueError::TypeMismatchError(e) => de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            e.actual, e.expected
                        )),
                        SetFieldValueError::SchemeMismatchError(_) => unreachable!(),
                    })?;
                }

                Ok(())
            }
        }

        deserializer.deserialize_map(ExecutionContextVisitor(self))
    }
}

impl<'e> Serialize for ExecutionContext<'e> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.values.len()))?;
        for (name, field) in self
            .scheme()
            .iter()
            .filter_map(|(name, item)| item.into_field().map(|f| (name, f)))
        {
            if let Some(Some(value)) = self.values.get(field.index()) {
                map.serialize_entry(name, value)?;
            }
        }

        map.end()
    }
}

#[test]
fn test_field_value_type_mismatch() {
    use crate::types::Type;

    let scheme = Scheme! { foo: Int };

    let mut ctx = ExecutionContext::<()>::new(&scheme);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("foo").unwrap(), LhsValue::Bool(false)),
        Err(SetFieldValueError::TypeMismatchError(TypeMismatchError {
            expected: Type::Int.into(),
            actual: Type::Bool,
        }))
    );
}

#[test]
fn test_scheme_mismatch() {
    let mut scheme = Scheme! { foo: Bool };

    let mut ctx = ExecutionContext::<()>::new(&scheme);

    let mut scheme2 = Scheme! { foo: Bool };

    assert_eq!(
        ctx.set_field_value(scheme2.get_field("foo").unwrap(), LhsValue::Bool(false)),
        Err(SetFieldValueError::SchemeMismatchError(
            SchemeMismatchError {}
        ))
    );

    scheme.set_relaxed_equality();
    scheme2.set_relaxed_equality();

    let mut ctx = ExecutionContext::<()>::new(&scheme);

    assert_eq!(
        ctx.set_field_value(scheme2.get_field("foo").unwrap(), LhsValue::Bool(false)),
        Ok(())
    );
}

#[test]
fn test_serde() {
    use crate::{
        lhs_types::{Array, Map},
        types::Type,
    };
    use std::{net::IpAddr, str::FromStr};

    let mut scheme = Scheme::new();
    scheme.add_field("bool".to_string(), Type::Bool).unwrap();
    scheme.add_field("ip".to_string(), Type::Ip).unwrap();
    scheme.add_field("str".to_string(), Type::Bytes).unwrap();
    scheme.add_field("bytes".to_string(), Type::Bytes).unwrap();
    scheme.add_field("num".to_string(), Type::Int).unwrap();
    scheme
        .add_field("arr".to_string(), Type::Array(Box::new(Type::Bool)))
        .unwrap();
    scheme
        .add_field("map".to_string(), Type::Map(Box::new(Type::Int)))
        .unwrap();

    let mut ctx = ExecutionContext::new(&scheme);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("bool").unwrap(), LhsValue::Bool(false)),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(
            scheme.get_field("ip").unwrap(),
            LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap())
        ),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("str").unwrap(), "a string"),
        Ok(()),
    );
    assert_eq!(
        ctx.set_field_value(scheme.get_field("bytes").unwrap(), &b"a\xFF\xFFb"[..]),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("num").unwrap(), 42),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("arr").unwrap(), {
            let mut arr = Array::new(Type::Bool);
            arr.push(false.into()).unwrap();
            arr.push(true.into()).unwrap();
            arr
        }),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("map").unwrap(), {
            let mut map = Map::new(Type::Int);
            map.insert(b"leet", 1337.into()).unwrap();
            map.insert(b"tabs", 25.into()).unwrap();
            map
        }),
        Ok(()),
    );

    let json = assert_json!(
        ctx,
        {
            "bool": false,
            "ip": "127.0.0.1",
            "str": "a string",
            "bytes": [97, 255, 255, 98],
            "num": 42,
            "arr": [false, true],
            "map": {
                "leet": 1337,
                "tabs": 25,
            }
        }
    )
    .to_string();

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_str(&json);
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_slice(json.as_bytes());
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx3 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_reader(json.as_bytes());
    ctx3.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx3);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("map").unwrap(), {
            let mut map = Map::new(Type::Int);
            map.insert(b"leet", 1337.into()).unwrap();
            map.insert(b"tabs", 25.into()).unwrap();
            map.insert(b"a\xFF\xFFb", 17.into()).unwrap();
            map
        }),
        Ok(()),
    );

    let json = assert_json!(
        ctx,
        {
            "bool": false,
            "ip": "127.0.0.1",
            "str": "a string",
            "bytes": [97, 255, 255, 98],
            "num": 42,
            "arr": [false, true],
            "map": [
                [[97, 255, 255, 98], 17],
                ["leet", 1337],
                ["tabs", 25]
            ]
        }
    )
    .to_string();

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_str(&json);
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_slice(json.as_bytes());
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx3 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_reader(json.as_bytes());
    ctx3.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx3);
}
