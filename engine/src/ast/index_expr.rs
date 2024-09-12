use super::{
    field_expr::{Cases, CasesOp, LhsFieldExpr},
    visitor::{Visitor, VisitorMut},
    ValueExpr,
};
use crate::{
    compiler::Compiler,
    execution_context::{ExecutionContext, State, Variables},
    filter::{CompiledExpr, CompiledOneExpr, CompiledValueExpr, CompiledVecExpr},
    lex::{
        complete, expect, skip_space, span, Lex, LexErrorKind, LexResult, LexWith, LexWith2,
        LexWith3,
    },
    lhs_types::{Array, Map},
    scheme::{FieldIndex, IndexAccessError, ParseError, Scheme},
    types::{GetType, IntoIter, LhsValue, Type, TypeMismatchError},
};
use serde::{ser::SerializeSeq, Serialize, Serializer};

/// SingleIndexExpr is an IndexExpr which returns a single value.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub struct SingleIndexExpr<'s> {
    /// Index expression.
    pub op: IndexExpr<'s>,
    /// Cases expressions.
    pub cases: Option<Cases<IndexExpr<'s>>>,
}

impl<'s> SingleIndexExpr<'s> {
    pub(crate) fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        let Self { op, cases } = self;
        let op = op.compile_with_compiler(compiler, variables);

        if let Some(cases) = cases {
            let cases = cases.compile_value_exprs_with_compiler(compiler, variables);
            CompiledValueExpr::new(move |ctx, variables, state| {
                let val = op.execute(ctx, variables, state)?;
                cases.execute(&val, ctx, variables, state)
            })
        } else {
            op
        }
    }
}

impl<'i, 's> LexWith2<'i, &'s Scheme, &Variables> for SingleIndexExpr<'s> {
    fn lex_with_2(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> LexResult<'i, Self> {
        let (op, input) = IndexExpr::lex_with_3(input, scheme, variables, None)?;
        let lhs_type = op.get_type();
        let input = skip_space(input);

        if CasesOp::lex(input).is_ok() {
            let (cases, input) =
                Cases::lex_with_lhs_type(input, scheme, None, lhs_type, None, variables, None)?;

            Ok((
                SingleIndexExpr {
                    op,
                    cases: Some(cases),
                },
                input,
            ))
        } else {
            Ok((SingleIndexExpr { op, cases: None }, input))
        }
    }
}

/// IndexExpr is an expr that destructures an index into an LhsFieldExpr.
///
/// For example, given a scheme which declares a field, http.request.headers,
/// as a map of string to list of strings, then the expression
/// http.request.headers["Cookie"][0] would have an LhsFieldExpr
/// http.request.headers and indexes ["Cookie", 0].
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct IndexExpr<'s> {
    /// Left-hand side of the index expression.
    pub lhs: LhsFieldExpr<'s>,
    /// Indexes to access the value.
    pub indexes: Vec<FieldIndex>,
}

macro_rules! index_access_one {
    ($indexes:ident, $first:expr, $default:expr, $ctx:ident, $variables:ident, $state:ident, $func:expr) => {
        #[allow(clippy::redundant_closure_call)]
        $indexes
            .iter()
            .fold($first, |value, idx| {
                value.and_then(|val| val.get(idx).unwrap())
            })
            .map_or_else(|| $default, |val| $func(val, $ctx, $variables, $state))
    };
}

macro_rules! index_access_vec {
    ($indexes:ident, $first:expr, $ctx:ident, $variables:ident, $state:ident, $func:ident) => {
        index_access_one!(
            $indexes,
            $first,
            Vec::new().into_boxed_slice(),
            $ctx,
            $variables,
            $state,
            |val: &LhsValue<'_>, ctx, variables, state| {
                let mut output = Vec::new();
                for item in val.iter().unwrap() {
                    output.push($func(item, ctx, variables, state));
                }
                output.into_boxed_slice()
            }
        )
    };
}

impl<'s> ValueExpr<'s> for IndexExpr<'s> {
    #[inline]
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        match self.lhs {
            LhsFieldExpr::Field(field) => visitor.visit_field(&field),
            LhsFieldExpr::FunctionCallExpr(ref call) => visitor.visit_function_call_expr(call),
            LhsFieldExpr::ScopedExtractedVariable(ref var) => {
                visitor.visit_scoped_extracted_variable(var)
            }
        }
    }

    #[inline]
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        match self.lhs {
            LhsFieldExpr::Field(field) => visitor.visit_field(&field),
            LhsFieldExpr::FunctionCallExpr(ref mut call) => visitor.visit_function_call_expr(call),
            LhsFieldExpr::ScopedExtractedVariable(ref mut var) => {
                visitor.visit_scoped_extracted_variable(var)
            }
        }
    }

    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        let ty = self.get_type();
        let map_each_count = self.map_each_count();
        let Self { lhs, indexes } = self;

        let last = match map_each_count {
            0 => Some(indexes.len()),
            1 if indexes.last() == Some(&FieldIndex::MapEach) => Some(indexes.len() - 1),
            _ => None,
        };
        if last == Some(0) {
            // Fast path
            lhs.compile_with_compiler(compiler, variables)
        } else if let Some(last) = last {
            // Average path
            match lhs {
                LhsFieldExpr::Field(f) => CompiledValueExpr::new(move |ctx, _, _| {
                    indexes[..last]
                        .iter()
                        .try_fold(ctx.get_field_value_unchecked(f), |value, index| {
                            value.get(index).unwrap()
                        })
                        .map(LhsValue::as_ref)
                        .ok_or_else(|| ty.clone())
                }),
                LhsFieldExpr::FunctionCallExpr(call) => {
                    let call = compiler.compile_function_call_expr(call, variables);
                    CompiledValueExpr::new(move |ctx, variables, state| {
                        let result = call.execute(ctx, variables, state)?;
                        indexes[..last]
                            .iter()
                            .try_fold(result, |value, index| value.extract(index).unwrap())
                            .ok_or_else(|| ty.clone())
                    })
                }
                LhsFieldExpr::ScopedExtractedVariable(_) => {
                    unreachable!()
                }
            }
        } else {
            // Slow path
            match lhs {
                LhsFieldExpr::Field(f) => CompiledValueExpr::new(move |ctx, _, _| {
                    let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                    iter.reset(ctx.get_field_value_unchecked(f).as_ref());
                    let mut arr = Array::new(ty.clone());
                    arr.extend(iter);
                    Ok(LhsValue::Array(arr))
                }),
                LhsFieldExpr::FunctionCallExpr(call) => {
                    let call = compiler.compile_function_call_expr(call, variables);
                    CompiledValueExpr::new(move |ctx, variables, state| {
                        let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                        iter.reset(call.execute(ctx, variables, state)?);
                        let mut arr = Array::new(ty.clone());
                        arr.extend(iter);
                        Ok(LhsValue::Array(arr))
                    })
                }
                LhsFieldExpr::ScopedExtractedVariable(_) => {
                    unreachable!()
                }
            }
        }
    }
}

fn simplify_indexes(mut indexes: Vec<FieldIndex>) -> Box<[FieldIndex]> {
    if Some(&FieldIndex::MapEach) == indexes.last() {
        indexes.pop();
    }
    indexes.into_boxed_slice()
}

impl<'s> IndexExpr<'s> {
    fn compile_one_with<
        F: 's + Fn(&LhsValue<'_>, &ExecutionContext<'_, U>, &Variables, &State) -> bool + Sync + Send,
        U: 's,
        C: Compiler<'s, U> + 's,
    >(
        self,
        compiler: &mut C,
        default: bool,
        func: F,
        variables: &Variables,
    ) -> CompiledOneExpr<'s, U> {
        let Self { lhs, indexes } = self;
        let indexes = simplify_indexes(indexes);
        match lhs {
            LhsFieldExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call, variables);
                if indexes.is_empty() {
                    CompiledOneExpr::new(move |ctx, variables, state| {
                        call.execute(ctx, variables, state)
                            .map_or(default, |val| func(&val, ctx, variables, state))
                    })
                } else {
                    CompiledOneExpr::new(move |ctx, variables, state| {
                        index_access_one!(
                            indexes,
                            call.execute(ctx, variables, state).as_ref().ok(),
                            default,
                            ctx,
                            variables,
                            state,
                            func
                        )
                    })
                }
            }
            LhsFieldExpr::Field(f) => {
                if indexes.is_empty() {
                    CompiledOneExpr::new(move |ctx, variables, state| {
                        func(ctx.get_field_value_unchecked(f), ctx, variables, state)
                    })
                } else {
                    CompiledOneExpr::new(move |ctx, variables, state| {
                        index_access_one!(
                            indexes,
                            Some(ctx.get_field_value_unchecked(f)),
                            default,
                            ctx,
                            variables,
                            state,
                            func
                        )
                    })
                }
            }
            LhsFieldExpr::ScopedExtractedVariable(var) => {
                if indexes.is_empty() {
                    CompiledOneExpr::new(move |ctx, variables, state| {
                        if let Some(value) = state.get(&var.scoped_var) {
                            func(&value.as_lhs_value().unwrap(), ctx, variables, state)
                        } else {
                            default
                        }
                    })
                } else {
                    CompiledOneExpr::new(move |_, _, _| unreachable!())
                }
            }
        }
    }

    pub(crate) fn compile_vec_with<
        F: 's + Fn(&LhsValue<'_>, &ExecutionContext<'_, U>, &Variables, &State) -> bool + Sync + Send,
        U: 's,
        C: Compiler<'s, U> + 's,
    >(
        self,
        compiler: &mut C,
        func: F,
        variables: &Variables,
    ) -> CompiledVecExpr<'s, U> {
        let Self { lhs, indexes } = self;
        let indexes = simplify_indexes(indexes);
        match lhs {
            LhsFieldExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call, variables);
                CompiledVecExpr::new(move |ctx, variables, state| {
                    index_access_vec!(
                        indexes,
                        call.execute(ctx, variables, state).as_ref().ok(),
                        ctx,
                        variables,
                        state,
                        func
                    )
                })
            }
            LhsFieldExpr::Field(f) => CompiledVecExpr::new(move |ctx, variables, state| {
                index_access_vec!(
                    indexes,
                    Some(ctx.get_field_value_unchecked(f)),
                    ctx,
                    variables,
                    state,
                    func
                )
            }),
            LhsFieldExpr::ScopedExtractedVariable(_) => {
                unreachable!()
            }
        }
    }

    pub(crate) fn compile_iter_with<
        F: 's + Fn(&LhsValue<'_>, &ExecutionContext<'_, U>, &Variables, &State) -> bool + Sync + Send,
        U: 's,
        C: Compiler<'s, U> + 's,
    >(
        self,
        compiler: &mut C,
        func: F,
        variables: &Variables,
    ) -> CompiledVecExpr<'s, U> {
        let Self { lhs, indexes } = self;
        match lhs {
            LhsFieldExpr::Field(f) => CompiledVecExpr::new(move |ctx, variables, state| {
                let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                iter.reset(ctx.get_field_value_unchecked(f).as_ref());

                let mut output = Vec::new();
                for item in iter {
                    output.push(func(&item, ctx, variables, state));
                }
                output.into_boxed_slice()
            }),
            LhsFieldExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call, variables);
                CompiledVecExpr::new(move |ctx, variables, state| {
                    let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                    if let Ok(val) = call.execute(ctx, variables, state) {
                        iter.reset(val);
                    } else {
                        return Vec::new().into_boxed_slice();
                    }

                    let mut output = Vec::new();
                    for item in iter {
                        output.push(func(&item, ctx, variables, state));
                    }
                    output.into_boxed_slice()
                })
            }
            LhsFieldExpr::ScopedExtractedVariable(_) => {
                unreachable!()
            }
        }
    }

    /// Compiles an [`IndexExpr`] node into a [`CompiledExpr`] (boxed closure)
    /// using the provided comparison function that returns a boolean.
    pub fn compile_with<
        F: 's + Fn(&LhsValue<'_>, &ExecutionContext<'_, U>, &Variables, &State) -> bool + Sync + Send,
        U: 's,
        C: Compiler<'s, U> + 's,
    >(
        self,
        compiler: &mut C,
        default: bool,
        func: F,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        match self.map_each_count() {
            0 => CompiledExpr::One(self.compile_one_with(compiler, default, func, variables)),
            1 if self.indexes.last() == Some(&FieldIndex::MapEach) => {
                CompiledExpr::Vec(self.compile_vec_with(compiler, func, variables))
            }
            _ => CompiledExpr::Vec(self.compile_iter_with(compiler, func, variables)),
        }
    }

    pub(crate) fn map_each_count(&self) -> usize {
        self.indexes
            .iter()
            .filter(|&index| index == &FieldIndex::MapEach)
            .count()
    }

    /// Parses an expression into an AST form.
    pub fn parse<'i>(
        scheme: &'s Scheme,
        variables: &Variables,
        input: &'i str,
        scope: Option<String>,
    ) -> Result<Self, ParseError<'i>> {
        complete(Self::lex_with_3(input.trim(), scheme, variables, scope))
            .and_then(|ast| {
                if ast.map_each_count() > 0 {
                    Err((
                        LexErrorKind::TypeMismatch(TypeMismatchError {
                            expected: ast.get_type().into(),
                            actual: Type::Array(Box::new(ast.get_type())),
                        }),
                        input,
                    ))
                } else {
                    Ok(ast)
                }
            })
            .map_err(|err| ParseError::new(input, err))
    }
}

impl<'i, 's> LexWith3<'i, &'s Scheme, &Variables, Option<String>> for IndexExpr<'s> {
    fn lex_with_3(
        mut input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
        scope: Option<String>,
    ) -> LexResult<'i, Self> {
        let (lhs, rest) = LhsFieldExpr::lex_with_3(input, scheme, variables, scope)?;

        let mut current_type = lhs.get_type();

        let mut indexes = Vec::new();

        input = rest;

        if let LhsFieldExpr::ScopedExtractedVariable(_) = lhs {
            return Ok((IndexExpr { lhs, indexes }, input));
        }

        while let Ok(rest) = expect(input, "[") {
            let rest = skip_space(rest);

            let (idx, rest) = FieldIndex::lex_with(rest, true)?;

            let mut rest = skip_space(rest);

            rest = expect(rest, "]")?;

            match &idx {
                FieldIndex::ArrayIndex(_) => match current_type {
                    Type::Array(array_type) => {
                        current_type = *array_type;
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ))
                    }
                },
                FieldIndex::MapKey(_) => match current_type {
                    Type::Map(map_type) => {
                        current_type = *map_type;
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ))
                    }
                },
                FieldIndex::MapEach => match current_type {
                    Type::Array(array_type) => {
                        current_type = *array_type;
                    }
                    Type::Map(map_type) => {
                        current_type = *map_type;
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ))
                    }
                },
            };

            input = rest;

            indexes.push(idx);
        }

        Ok((IndexExpr { lhs, indexes }, input))
    }
}

impl<'s> GetType for IndexExpr<'s> {
    fn get_type(&self) -> Type {
        let mut ty = self.lhs.get_type();
        for index in &self.indexes {
            ty = match (ty, index) {
                (Type::Array(idx), FieldIndex::ArrayIndex(_)) => *idx,
                (Type::Array(idx), FieldIndex::MapEach) => *idx,
                (Type::Map(child), FieldIndex::MapKey(_)) => *child,
                (Type::Map(child), FieldIndex::MapEach) => *child,
                (_, _) => unreachable!(),
            }
        }
        ty
    }
}

impl<'s> Serialize for IndexExpr<'s> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        if self.indexes.is_empty() {
            self.lhs.serialize(ser)
        } else {
            let mut seq = ser.serialize_seq(Some(self.indexes.len() + 1))?;
            match &self.lhs {
                LhsFieldExpr::Field(field) => seq.serialize_element(field)?,
                LhsFieldExpr::FunctionCallExpr(call) => seq.serialize_element(call)?,
                LhsFieldExpr::ScopedExtractedVariable(var) => seq.serialize_element(var)?,
            };
            for index in &self.indexes {
                seq.serialize_element(index)?;
            }
            seq.end()
        }
    }
}

enum FieldIndexIterator<'a, 'b> {
    ArrayIndex(Option<(Array<'a>, u32)>),
    MapKey(Option<(Map<'a>, &'b [u8])>),
    MapEach(IntoIter<'a>),
}

impl<'a, 'b> FieldIndexIterator<'a, 'b> {
    fn new(val: LhsValue<'a>, idx: &'b FieldIndex) -> Result<Self, IndexAccessError> {
        match idx {
            FieldIndex::ArrayIndex(idx) => match val {
                LhsValue::Array(arr) => Ok(Self::ArrayIndex(Some((arr, *idx)))),
                _ => Err(IndexAccessError {
                    index: FieldIndex::ArrayIndex(*idx),
                    actual: val.get_type(),
                }),
            },
            FieldIndex::MapKey(key) => match val {
                LhsValue::Map(map) => Ok(Self::MapKey(Some((map, key.as_bytes())))),
                _ => Err(IndexAccessError {
                    index: FieldIndex::MapKey(key.clone()),
                    actual: val.get_type(),
                }),
            },
            FieldIndex::MapEach => match val {
                LhsValue::Array(_) | LhsValue::Map(_) => Ok(Self::MapEach(val.into_iter())),
                _ => Err(IndexAccessError {
                    index: FieldIndex::MapEach,
                    actual: val.get_type(),
                }),
            },
        }
    }
}

impl<'a, 'b> Iterator for FieldIndexIterator<'a, 'b> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::ArrayIndex(opt) => opt.take().and_then(|(arr, idx)| arr.extract(idx as usize)),
            Self::MapKey(opt) => opt.take().and_then(|(map, key)| map.extract(key)),
            Self::MapEach(iter) => iter.next(),
        }
    }
}

struct MapEachIterator<'a, 'b> {
    indexes: &'b [FieldIndex],
    stack: Vec<FieldIndexIterator<'a, 'b>>,
}

impl<'a, 'b> MapEachIterator<'a, 'b> {
    fn from_indexes(indexes: &'b [FieldIndex]) -> Self {
        Self {
            indexes,
            stack: Vec::with_capacity(indexes.len()),
        }
    }

    fn reset(&mut self, val: LhsValue<'a>) {
        self.stack.clear();
        let first = self.indexes.first().unwrap();
        self.stack
            .push(FieldIndexIterator::new(val, first).unwrap());
    }
}

impl<'a, 'b> Iterator for MapEachIterator<'a, 'b> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        while !self.stack.is_empty() {
            assert!(self.stack.len() <= self.indexes.len());
            if let Some(nxt) = self.stack.last_mut().unwrap().next() {
                // Check that current iterator is a leaf iterator
                if self.stack.len() == self.indexes.len() {
                    // Return a value if a leaf iterator returned a value
                    return Some(nxt);
                } else {
                    self.stack.push(
                        FieldIndexIterator::new(nxt, &self.indexes[self.stack.len()]).unwrap(),
                    );
                }
            } else {
                // Last iterator is finished, remove it
                self.stack.pop();
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::field_expr::LhsFieldExpr, Array, FieldIndex};
    use indoc::indoc;
    use lazy_static::lazy_static;

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme::new();
            scheme
                .add_field("test".to_string(), Type::Array(Box::new(Type::Bytes)))
                .unwrap();
            scheme
                .add_field(
                    "test2".to_string(),
                    Type::Array(Box::new(Type::Array(Box::new(Type::Bytes)))),
                )
                .unwrap();
            scheme
        };
    }

    #[test]
    fn test_array_indices() {
        fn run(i: u32) {
            let filter = format!("test[{}]", i);
            assert_ok!(
                IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
                IndexExpr {
                    lhs: LhsFieldExpr::Field(SCHEME.get_field("test").unwrap()),
                    indexes: vec![FieldIndex::ArrayIndex(i)],
                }
            );
        }

        run(0);
        run(1);
        run(99);
        run(999);
        run(9999);
        run(99999);
    }

    #[test]
    fn test_mapeach() {
        let filter = "test2[0][*]".to_string();

        let expr = assert_ok!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            IndexExpr {
                lhs: LhsFieldExpr::Field(SCHEME.get_field("test2").unwrap()),
                indexes: vec![FieldIndex::ArrayIndex(0), FieldIndex::MapEach],
            }
        );

        assert_eq!(expr.map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Bytes);

        let filter = "test2[*][0]".to_string();

        let expr = assert_ok!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            IndexExpr {
                lhs: LhsFieldExpr::Field(SCHEME.get_field("test2").unwrap()),
                indexes: vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(0)],
            }
        );

        assert_eq!(expr.map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Bytes);

        let filter = "test2[*][*]".to_string();

        let expr = assert_ok!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            IndexExpr {
                lhs: LhsFieldExpr::Field(SCHEME.get_field("test2").unwrap()),
                indexes: vec![FieldIndex::MapEach, FieldIndex::MapEach],
            }
        );

        assert_eq!(expr.map_each_count(), 2);
        assert_eq!(expr.get_type(), Type::Bytes);

        let filter = "test2[0][*][*]".to_string();

        assert_err!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );

        let filter = "test2[*][0][*]".to_string();

        assert_err!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );

        let filter = "test2[*][*][0]".to_string();

        assert_err!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes
            }),
            "[0]"
        );

        let filter = "test2[*][*][*]".to_string();

        assert_err!(
            IndexExpr::lex_with_3(&filter, &SCHEME, &Default::default(), None),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );
    }

    #[test]
    fn test_flatten() {
        let mut arr = Array::new(Type::Array(Box::new(Type::Bytes)));
        for i in 0..10 {
            let mut nested_arr = Array::new(Type::Bytes);
            for j in 0..10 {
                nested_arr
                    .push(LhsValue::Bytes(
                        format!("[{}][{}]", i, j).into_bytes().into(),
                    ))
                    .unwrap();
            }
            arr.push(LhsValue::Array(nested_arr)).unwrap();
        }
        let arr = LhsValue::Array(arr);

        for i in 0..10 {
            let indexes = [FieldIndex::ArrayIndex(i), FieldIndex::MapEach];
            let mut iter = MapEachIterator::from_indexes(&indexes[..]);

            iter.reset(arr.clone());
            for (j, elem) in iter.enumerate() {
                let bytes = match elem {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => unreachable!(),
                };
                assert_eq!(
                    std::str::from_utf8(&bytes).unwrap(),
                    format!("[{}][{}]", i, j)
                );
            }

            let indexes = [FieldIndex::MapEach, FieldIndex::ArrayIndex(i)];
            let mut iter = MapEachIterator::from_indexes(&indexes[..]);

            iter.reset(arr.clone());
            for (j, elem) in iter.enumerate() {
                let bytes = match elem {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => unreachable!(),
                };
                assert_eq!(
                    std::str::from_utf8(&bytes).unwrap(),
                    format!("[{}][{}]", j, i)
                );
            }
        }

        let indexes = [FieldIndex::MapEach, FieldIndex::MapEach];
        let mut iter = MapEachIterator::from_indexes(&indexes[..]);
        let mut i = 0;
        let mut j = 0;

        iter.reset(arr.clone());
        for elem in iter {
            let bytes = match elem {
                LhsValue::Bytes(bytes) => bytes,
                _ => unreachable!(),
            };
            assert_eq!(
                std::str::from_utf8(&bytes).unwrap(),
                format!("[{}][{}]", i, j)
            );
            j = (j + 1) % 10;
            i += (j == 0) as u32;
        }
    }

    #[test]
    fn test_parse() {
        let err = IndexExpr::parse(&SCHEME, &Default::default(), "test[*]", None).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: Type::Bytes.into(),
                    actual: Type::Array(Box::new(Type::Bytes)),
                }),
                input: "test[*]",
                line_number: 0,
                span_start: 0,
                span_len: 7,
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:1):
                test[*]
                ^^^^^^^ expected value of type {Type(Bytes)}, but got Array(Bytes)
                "#
            )
        );

        assert_eq!(
            IndexExpr::parse(&SCHEME, &Default::default(), "test[42]", None),
            Ok(IndexExpr {
                lhs: LhsFieldExpr::Field(SCHEME.get_field("test").unwrap()),
                indexes: vec![FieldIndex::ArrayIndex(42)],
            })
        );
    }
}
