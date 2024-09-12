use super::{
    visitor::{Visitor, VisitorMut},
    ValueExpr,
};
use crate::{
    ast::{
        field_expr::{ComparisonExpr, ComparisonOp, ComparisonOpExpr},
        index_expr::IndexExpr,
        simple_expr::{SimpleExpr, UnaryOp},
    },
    compiler::Compiler,
    execution_context::Variables,
    filter::{CompiledExpr, CompiledValueExpr},
    functions::{
        ExactSizeChain, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
        FunctionParamError,
    },
    lex::{
        expect, skip_space, span, Lex, LexError, LexErrorKind, LexResult, LexWith, LexWith3,
        LexWith4,
    },
    lhs_types::Array,
    rhs_types::Variable,
    scheme::{Function, Scheme},
    types::{GetType, LhsValue, RhsValue, Type},
};
use derivative::Derivative;
use serde::Serialize;
use std::iter::once;

/// FunctionCallArgExpr is a function argument. It can be a sub-expression with
/// [`SimpleExpr`], a field with [`IndexExpr`] or a literal with [`Literal`].
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(tag = "kind", content = "value")]
pub enum FunctionCallArgExpr<'s> {
    /// IndexExpr is a field that supports the indexing operator.
    IndexExpr(IndexExpr<'s>),
    /// A Literal.
    Literal(RhsValue),
    /// SimpleExpr is a sub-expression which can evaluate to either true/false
    /// or a list of true/false. It compiles to a CompiledExpr and is coerced
    /// into a CompiledValueExpr.
    SimpleExpr(SimpleExpr<'s>),
    /// A variable.
    Variable(Variable),
}

impl<'s> ValueExpr<'s> for FunctionCallArgExpr<'s> {
    #[inline]
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => visitor.visit_index_expr(index_expr),
            FunctionCallArgExpr::Literal(_) => {}
            FunctionCallArgExpr::SimpleExpr(simple_expr) => visitor.visit_simple_expr(simple_expr),
            FunctionCallArgExpr::Variable(variable) => visitor.visit_variable(variable),
        }
    }

    #[inline]
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => visitor.visit_index_expr(index_expr),
            FunctionCallArgExpr::Literal(_) => {}
            FunctionCallArgExpr::SimpleExpr(simple_expr) => visitor.visit_simple_expr(simple_expr),
            FunctionCallArgExpr::Variable(variable) => visitor.visit_variable(variable),
        }
    }

    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => {
                compiler.compile_index_expr(index_expr, variables)
            }
            FunctionCallArgExpr::Literal(literal) => {
                CompiledValueExpr::new(move |_, _, _| LhsValue::from(literal.clone()).into())
            }
            // The function argument is an expression compiled as either an
            // CompiledExpr::One or CompiledExpr::Vec.
            // Here we execute the expression to get the actual argument
            // for the function and forward the result in a CompiledValueExpr.
            FunctionCallArgExpr::SimpleExpr(simple_expr) => {
                let compiled_expr = compiler.compile_simple_expr(simple_expr, variables);
                match compiled_expr {
                    CompiledExpr::One(expr) => {
                        CompiledValueExpr::new(move |ctx, variables, state| {
                            LhsValue::from(expr.execute(ctx, variables, state)).into()
                        })
                    }
                    CompiledExpr::Vec(expr) => {
                        CompiledValueExpr::new(move |ctx, variables, state| {
                            let result = expr.execute(ctx, variables, state);
                            LhsValue::Array({
                                let mut arr = Array::new(Type::Bool);
                                for next in result.iter() {
                                    arr.push((*next).into()).unwrap();
                                }
                                arr
                            })
                            .into()
                        })
                    }
                }
            }
            FunctionCallArgExpr::Variable(variable) => {
                CompiledValueExpr::new(move |_, variables, _| {
                    if let Some(variable_value) = variables.get(variable.name_as_str()) {
                        variable_value
                            .as_lhs_value()
                            .ok_or_else(|| variable.get_type().unwrap())
                    } else {
                        Err(variable.get_type().unwrap())
                    }
                })
            }
        }
    }
}

impl<'s> FunctionCallArgExpr<'s> {
    pub(crate) fn map_each_count(&self) -> usize {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.map_each_count(),
            FunctionCallArgExpr::Literal(_) => 0,
            FunctionCallArgExpr::SimpleExpr(_) => 0,
            FunctionCallArgExpr::Variable(_) => 0,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn simplify(self) -> Self {
        match self {
            FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(ComparisonExpr {
                lhs,
                op: ComparisonOpExpr::IsTrue,
            })) => FunctionCallArgExpr::IndexExpr(lhs),
            _ => self,
        }
    }
}

impl<'i, 's> LexWith4<'i, &'s Scheme, &Variables, Option<Type>, Option<String>>
    for FunctionCallArgExpr<'s>
{
    fn lex_with_4(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
        ty: Option<Type>,
        scope: Option<String>,
    ) -> LexResult<'i, Self> {
        let initial_input = input;

        macro_rules! c_is_field {
            // characters above F/f in the alphabet mean it can't be a decimal or hex int
            ($c:expr) => {
                (($c.is_ascii_alphanumeric() && !$c.is_ascii_hexdigit()) || $c == '_')
            };
        }

        macro_rules! c_is_field_or_int {
            ($c:expr) => {
                ($c.is_ascii_alphanumeric() || $c == '_')
            };
        }

        // Grammar is ambiguous but lets try to parse the tokens we can be sure of
        // This will provide better error reporting in most cases
        let mut chars = input.chars();
        if let Some(c) = chars.next() {
            // check up to 5 next chars because third char of a hex-string is either ':'
            // or '-'
            let c2 = chars.next();
            let c3 = chars.next();
            let c4 = chars.next();
            let c5 = chars.next();
            if c == '"'
                || (c == 'r' && (c2 == Some('"') || c2 == Some('#')))
                || (c.is_ascii_hexdigit()
                    && (c2.is_some() && c2.unwrap().is_ascii_hexdigit())
                    && (c3 == Some(':') || c3 == Some('-'))
                    && (c4.is_some() && c4.unwrap().is_ascii_hexdigit())
                    && (c5.is_some() && c5.unwrap().is_ascii_hexdigit()))
            {
                return RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input));
            } else if c == '(' || UnaryOp::lex(input).is_ok() {
                return SimpleExpr::lex_with_3(input, scheme, variables, scope)
                    .map(|(lhs, input)| (FunctionCallArgExpr::SimpleExpr(lhs), input));
            } else if c == '$' {
                let (mut variable, input) = Variable::lex(input)?;
                if let Some(variable_value) = variables.get(variable.name_as_str()) {
                    variable.set_type(variable_value.get_variable_type());
                    if let Some(ty) = ty {
                        if variable_value.is_supported_as_lhs_value(&ty) {
                            return Ok((FunctionCallArgExpr::Variable(variable), input));
                        } else {
                            return Err((
                                LexErrorKind::VariableTypeMismatch {
                                    name: variable.take_name(),
                                    actual: variable_value.get_variable_type(),
                                    expected: ty,
                                },
                                span(initial_input, input),
                            ));
                        }
                    }
                    return Ok((FunctionCallArgExpr::Variable(variable), input));
                } else {
                    return Err((
                        LexErrorKind::UnknownVariable {
                            name: variable.take_name(),
                        },
                        span(initial_input, input),
                    ));
                }
            } else if c_is_field!(c)
                || (c_is_field_or_int!(c) && c2.is_some() && c_is_field!(c2.unwrap()))
                || (c_is_field_or_int!(c)
                    && c2.is_some()
                    && c_is_field_or_int!(c2.unwrap())
                    && c3.is_some()
                    && c_is_field!(c3.unwrap()))
            {
                let (lhs, input) = IndexExpr::lex_with_3(input, scheme, variables, scope.clone())?;
                let lookahead = skip_space(input);
                if ComparisonOp::lex(lookahead).is_ok() {
                    return ComparisonExpr::lex_with_lhs(input, scheme, lhs, variables, scope).map(
                        |(op, input)| {
                            (
                                FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(op)),
                                input,
                            )
                        },
                    );
                } else {
                    return Ok((FunctionCallArgExpr::IndexExpr(lhs), input));
                }
            }
        }

        // Fallback to blind parsing next argument
        if let Ok((lhs, input)) = IndexExpr::lex_with_3(input, scheme, variables, scope.clone()) {
            let lookahead = skip_space(input);
            if ComparisonOp::lex(lookahead).is_ok() {
                return ComparisonExpr::lex_with_lhs(input, scheme, lhs, variables, scope).map(
                    |(op, input)| {
                        (
                            FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(op)),
                            input,
                        )
                    },
                );
            } else {
                return Ok((FunctionCallArgExpr::IndexExpr(lhs), input));
            }
        }

        RhsValue::lex_with(input, Type::Ip)
            .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Float)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Int)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            // try to parse Bytes after Int because digit literals < 255 are wrongly
            // interpreted as Bytes
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            .map_err(|_| (LexErrorKind::EOF, initial_input))
    }
}

impl<'s> GetType for FunctionCallArgExpr<'s> {
    fn get_type(&self) -> Type {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.get_type(),
            FunctionCallArgExpr::Literal(literal) => literal.get_type(),
            FunctionCallArgExpr::SimpleExpr(simple_expr) => simple_expr.get_type(),
            FunctionCallArgExpr::Variable(variable) => variable.get_type().unwrap(),
        }
    }
}

impl<'a, 's> From<&'a FunctionCallArgExpr<'s>> for FunctionParam<'a> {
    fn from(arg_expr: &'a FunctionCallArgExpr<'s>) -> Self {
        match arg_expr {
            FunctionCallArgExpr::IndexExpr(expr) => FunctionParam::Complex(expr.get_type()),
            FunctionCallArgExpr::SimpleExpr(expr) => FunctionParam::Complex(expr.get_type()),
            FunctionCallArgExpr::Literal(value) => FunctionParam::Constant(value.into()),
            FunctionCallArgExpr::Variable(variable) => {
                FunctionParam::Complex(variable.get_type().unwrap())
            }
        }
    }
}

/// FunctionCallExpr represents a function call expression.
#[derive(Derivative, Serialize)]
#[derivative(Debug, PartialEq, Eq, Clone, Hash)]
pub struct FunctionCallExpr<'s> {
    #[serde(rename = "name")]
    /// Function being called.
    pub function: Function<'s>,
    #[serde(skip)]
    /// Return type of the function.
    pub return_type: Type,
    /// Arguments of the function.
    pub args: Vec<FunctionCallArgExpr<'s>>,
    /// Context of the function definition.
    #[serde(skip)]
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub context: Option<FunctionDefinitionContext>,
}

impl<'s> ValueExpr<'s> for FunctionCallExpr<'s> {
    #[inline]
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        self.args
            .iter()
            .for_each(|arg| visitor.visit_function_call_arg_expr(arg));
        visitor.visit_function(&self.function)
    }

    #[inline]
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        self.args
            .iter_mut()
            .for_each(|arg| visitor.visit_function_call_arg_expr(arg));
        visitor.visit_function(&self.function)
    }

    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        let ty = self.get_type();
        let Self {
            function,
            args,
            return_type,
            context,
            ..
        } = self;
        let map_each_count = args.first().map_or(0, |arg| arg.map_each_count());
        let call = function
            .as_definition()
            .compile(&mut (args).iter().map(|arg| arg.into()), context);
        let args = args
            .into_iter()
            .map(|arg| compiler.compile_function_call_arg_expr(arg, variables))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        if map_each_count > 0 {
            CompiledValueExpr::new(move |ctx, variables, state| {
                // Create the output array
                let mut output = Array::new(return_type.clone());
                // Compute value of first argument
                if let Ok(first) = args[0].execute(ctx, variables, state) {
                    // Apply the function for each element contained
                    // in the first argument and extend output array
                    output.extend(first.into_iter().filter_map(|elem| {
                        call(
                            &mut ExactSizeChain::new(
                                once(Ok(elem)),
                                args[1..]
                                    .iter()
                                    .map(|arg| arg.execute(ctx, variables, state)),
                            ),
                            state,
                        )
                    }));
                }
                Ok(LhsValue::Array(output))
            })
        } else {
            CompiledValueExpr::new(move |ctx, variables, state| {
                if let Some(value) = call(
                    &mut args.iter().map(|arg| arg.execute(ctx, variables, state)),
                    state,
                ) {
                    debug_assert!(value.get_type() == ty);
                    Ok(value)
                } else {
                    Err(ty.clone())
                }
            })
        }
    }
}

impl<'s> FunctionCallExpr<'s> {
    pub(crate) fn new(
        function: Function<'s>,
        args: Vec<FunctionCallArgExpr<'s>>,
        context: Option<FunctionDefinitionContext>,
    ) -> Self {
        let return_type = function
            .as_definition()
            .return_type(&mut args.iter().map(|arg| arg.into()), context.as_ref());
        Self {
            function,
            args,
            return_type,
            context,
        }
    }

    pub(crate) fn lex_with_function<'i>(
        input: &'i str,
        function: Function<'s>,
        variables: &Variables,
        scope: Option<String>,
    ) -> LexResult<'i, Self> {
        let scheme = function.scheme();
        let definition = function.as_definition();

        let mut input = skip_space(input);

        input = expect(input, "(")?;

        input = skip_space(input);

        let (mandatory_arg_count, optional_arg_count) = definition.arg_count();

        let mut args: Vec<FunctionCallArgExpr<'s>> = Vec::new();

        let mut index = 0;

        let mut ctx = definition.context();

        while let Some(c) = input.chars().next() {
            if c == ')' {
                break;
            }
            // ',' is expected only if the current argument
            // is not the first one in the list of specified arguments.
            if index != 0 {
                input = expect(input, ",")?;
            }

            input = skip_space(input);

            let (arg, rest) = FunctionCallArgExpr::lex_with_4(
                input,
                scheme,
                variables,
                definition.arg_type(index),
                scope.clone(),
            )?;

            // Mapping is only accepted for the first argument
            // of a function call for code simplicity
            if arg.map_each_count() > 0 && index != 0 {
                return Err((LexErrorKind::InvalidMapEachAccess, span(input, rest)));
            }

            let next_param = (&arg).into();

            if optional_arg_count.is_some()
                && index >= (mandatory_arg_count + optional_arg_count.unwrap())
            {
                return Err(invalid_args_count(definition, input));
            }

            definition
                .check_param(
                    &mut args.iter().map(|arg| arg.into()),
                    &next_param,
                    ctx.as_mut(),
                )
                .map_err(|err| match err {
                    FunctionParamError::KindMismatch(err) => (
                        LexErrorKind::InvalidArgumentKind {
                            index,
                            mismatch: err,
                        },
                        span(input, rest),
                    ),
                    FunctionParamError::TypeMismatch(err) => (
                        LexErrorKind::InvalidArgumentType {
                            index,
                            mismatch: err,
                        },
                        span(input, rest),
                    ),
                    FunctionParamError::InvalidConstant(err) => (
                        LexErrorKind::InvalidArgumentValue {
                            index,
                            invalid: err,
                        },
                        span(input, rest),
                    ),
                })?;

            args.push(arg);

            input = skip_space(rest);

            // Check if the next character is a comma, indicating a possible trailing comma
            if let Some(next_char) = input.chars().next() {
                if next_char == ',' {
                    let mut input2 = &input[1..];

                    input2 = skip_space(input2);

                    if input2.starts_with(')') {
                        input = input2;
                        break;
                    }
                }
            }

            index += 1;
        }

        if args.len() < mandatory_arg_count {
            return Err(invalid_args_count(definition, input));
        }

        input = expect(input, ")")?;

        let function_call = FunctionCallExpr::new(function, args, ctx);

        Ok((function_call, input))
    }

    /// Returns the function being called.
    pub fn function(&self) -> Function<'s> {
        self.function
    }

    /// Returns the return type of the function.
    pub fn return_type(&self) -> &Type {
        &self.return_type
    }

    /// Returns the arguments of the function.
    pub fn args(&self) -> &[FunctionCallArgExpr<'s>] {
        &self.args
    }
}

fn invalid_args_count<'i>(function: &dyn FunctionDefinition, input: &'i str) -> LexError<'i> {
    let (mandatory, optional) = function.arg_count();
    (
        LexErrorKind::InvalidArgumentsCount {
            expected_min: mandatory,
            expected_max: optional.map(|v| mandatory + v),
        },
        input,
    )
}

impl<'s> GetType for FunctionCallExpr<'s> {
    fn get_type(&self) -> Type {
        let ty = self.return_type.clone();
        if !self.args.is_empty() && self.args[0].map_each_count() > 0 {
            Type::Array(Box::new(ty))
        } else {
            ty
        }
    }
}

impl<'i, 's> LexWith3<'i, &'s Scheme, &Variables, Option<String>> for FunctionCallExpr<'s> {
    fn lex_with_3(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
        scope: Option<String>,
    ) -> LexResult<'i, Self> {
        let (function, rest) = Function::lex_with(input, scheme)?;

        Self::lex_with_function(rest, function, variables, scope)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{
            field_expr::{ComparisonExpr, ComparisonOpExpr, LhsFieldExpr, OrderingOp},
            logical_expr::{LogicalExpr, LogicalOp},
        },
        execution_context::{State, Variables},
        functions::{
            FunctionArgKind, FunctionArgKindMismatchError, FunctionArgs, SimpleFunctionDefinition,
            SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam,
        },
        scheme::{FieldIndex, IndexAccessError},
        types::{ExpectedType, RhsValues, Type, TypeMismatchError, VariableType},
    };
    use lazy_static::lazy_static;
    use std::{collections::HashSet, convert::TryFrom};

    fn any_function<'a>(args: FunctionArgs<'_, 'a>, _: &State) -> Option<LhsValue<'a>> {
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

    fn lower_function<'a>(args: FunctionArgs<'_, 'a>, _: &State) -> Option<LhsValue<'a>> {
        use std::borrow::Cow;

        match args.next()? {
            Ok(LhsValue::Bytes(mut b)) => {
                let mut text: Vec<u8> = b.to_mut().to_vec();
                text.make_ascii_lowercase();
                Some(LhsValue::Bytes(Cow::Owned(text)))
            }
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    fn upper_function<'a>(args: FunctionArgs<'_, 'a>, _: &State) -> Option<LhsValue<'a>> {
        use std::borrow::Cow;

        match args.next()? {
            Ok(LhsValue::Bytes(mut b)) => {
                let mut text: Vec<u8> = b.to_mut().to_vec();
                text.make_ascii_uppercase();
                Some(LhsValue::Bytes(Cow::Owned(text)))
            }
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>, _: &State) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>, _: &State) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.headers: Map(Bytes),
                http.host: Bytes,
                http.request.headers.names: Array(Bytes),
                http.request.headers.values: Array(Bytes),
                http.request.headers.is_empty: Array(Bool),
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
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
                        opt_params: Some(vec![
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Any,
                                default_value: LhsValue::Int(10),
                            },
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: LhsValue::Int(1),
                            },
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: LhsValue::Bytes(b"test".into()),
                            },
                        ]),
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(echo_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "lower".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Complex,
                            val_type: Type::Bytes,
                        }],
                        opt_params: Some(vec![]),
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(lower_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "upper".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Any,
                            val_type: Type::Bytes,
                        }],
                        opt_params: Some(vec![]),
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(upper_function),
                    },
                )
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
            variables.add("func_test_var".to_string(), 10.into());
            variables
        };
    }

    #[test]
    fn test_lex_function_call_expr() {
        // test that adjacent single digit int literals are parsed properly
        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo ( http.host, 1, 2, "test" );"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo ( http.host, 1, 2, "test", );"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo ( http.host, 1, 2, "test" , );"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo ( http.host, $func_test_var, 2, "test" );"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Variable(Variable {
                        name: "func_test_var".into(),
                        ty: Some(VariableType::Int),
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Variable",
                        "value": {
                            "name": "func_test_var",
                            "ty": "Int"
                        }
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo ( http.host, 1, 2, r"test" );"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r##"echo ( http.host, 1, 2, r#"test"# );"##,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo ( http.host, 1, 2, 74:65:73:74 );"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes(vec![116, 101, 115, 116].into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": vec![116, 101, 115, 116]
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3("echo ( http.host );", &SCHEME, &VARIABLES, None),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                    indexes: vec![],
                })],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    }
                ]
            }
        );

        // test that adjacent single digit int literals are parsed properly (without
        // spaces)
        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"echo (http.host,1,2,"test");"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes("test".to_owned().into())),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    },
                    {
                        "kind": "Literal",
                        "value": "test"
                    }
                ]
            }
        );

        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( );", &SCHEME, &VARIABLES, None),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(4),
            },
            ");"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.host , http.host );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            LexErrorKind::InvalidArgumentType {
                index: 1,
                mismatch: TypeMismatchError {
                    expected: {
                        let mut hash_set = HashSet::new();
                        hash_set.insert(ExpectedType::Type(Type::Int));
                        hash_set
                    },
                    actual: Type::Bytes,
                }
            },
            "http.host"
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3("echo ( echo ( http.host ) );", &SCHEME, &VARIABLES, None),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: [FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                })]
                .to_vec(),
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": {
                            "name": "echo",
                            "args": [
                                {
                                    "kind": "IndexExpr",
                                    "value": "http.host"
                                }
                            ]
                        }
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                r#"any ( ( http.request.headers.is_empty or http.request.headers.is_empty ) )"#,
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Parenthesized(
                    Box::new(LogicalExpr::Combining {
                        op: LogicalOp::Or(0),
                        items: vec![
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.is_empty").unwrap()
                                    ),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::IsTrue,
                            })),
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.is_empty").unwrap()
                                    ),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::IsTrue,
                            }))
                        ]
                    })
                ))],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "name": "any",
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "items": [
                                {
                                    "lhs": "http.request.headers.is_empty",
                                    "op": "IsTrue",
                                },
                                {
                                    "lhs": "http.request.headers.is_empty",
                                    "op": "IsTrue",
                                }
                            ],
                            "op": "Or",
                        }
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.request.headers.names[*] );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                })],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": ["http.request.headers.names", {"kind": "MapEach"}],
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3("echo ( http.headers[*] );", &SCHEME, &VARIABLES, None),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(SCHEME.get_field("http.headers").unwrap()),
                    indexes: vec![FieldIndex::MapEach],
                })],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bytes)));

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": ["http.headers", {"kind": "MapEach"}],
                    }
                ]
            }
        );

        assert_ok!(
            FunctionCallArgExpr::lex_with_4(
                "http.request.headers.names[*] == \"test\"",
                &SCHEME,
                &VARIABLES,
                Some(Type::Bool),
                None,
            ),
            FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal(1),
                    rhs: RhsValue::Bytes("test".to_owned().into())
                }
            })),
            ""
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                "any(lower(http.request.headers.names[*])[*] contains \"c\")",
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(
                    ComparisonExpr {
                        lhs: IndexExpr {
                            lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                                function: SCHEME.get_function("lower").unwrap(),
                                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.names").unwrap()
                                    ),
                                    indexes: vec![FieldIndex::MapEach],
                                })],
                                return_type: Type::Bytes,
                                context: None,
                            }),
                            indexes: vec![FieldIndex::MapEach],
                        },
                        op: ComparisonOpExpr::Contains {
                            rhs: "c".to_string().into(),
                            variant: 0,
                        }
                    }
                ))],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "lhs": [
                                {
                                    "args": [
                                        {
                                            "kind": "IndexExpr",
                                            "value": ["http.request.headers.names", {"kind": "MapEach"}]
                                        }
                                    ],
                                    "name": "lower"
                                },{
                                    "kind": "MapEach"
                                }
                            ],
                            "op": "Contains",
                            "rhs": "c"
                        }
                    }
                ],
                "name": "any"
            }
        );

        let expr = FunctionCallArgExpr::lex_with_4("lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(http.host)))))))))))))))))))))))))))))))) contains \"c\"",&SCHEME, &VARIABLES, Some(Type::Bool), None);
        assert!(expr.is_ok());

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                "len(http.request.headers.names[*])",
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("len").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                })],
                return_type: Type::Int,
                context: None,
            },
            ""
        );

        assert_eq!(expr.args[0].map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Int)));
    }

    #[test]
    fn test_lex_function_with_unary_expression_as_argument() {
        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                "any(not(http.request.headers.names[*] in [\"Cookie\", \"Cookies\"]))",
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Unary {
                    op: UnaryOp::Not(0),
                    arg: Box::new(SimpleExpr::Parenthesized(Box::new(LogicalExpr::Simple(
                        SimpleExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                lhs: LhsFieldExpr::Field(
                                    SCHEME.get_field("http.request.headers.names").unwrap()
                                ),
                                indexes: vec![FieldIndex::MapEach],
                            },
                            op: ComparisonOpExpr::OneOf {
                                rhs: RhsValues::Bytes(vec![
                                    "Cookie".to_owned().into(),
                                    "Cookies".to_owned().into(),
                                ]),
                                variant: 0,
                            },
                        })
                    ))))
                })],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "name": "any",
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "op": "Not",
                            "arg": {
                                "lhs": [
                                    "http.request.headers.names",
                                    {
                                        "kind": "MapEach"
                                    }
                                ],
                                "op": "OneOf",
                                "rhs": [
                                    "Cookie",
                                    "Cookies"
                                ]
                            }
                        }
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                "any(!(http.request.headers.names[*] in [\"Cookie\", \"Cookies\"]))",
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Unary {
                    op: UnaryOp::Not(0),
                    arg: Box::new(SimpleExpr::Parenthesized(Box::new(LogicalExpr::Simple(
                        SimpleExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                lhs: LhsFieldExpr::Field(
                                    SCHEME.get_field("http.request.headers.names").unwrap()
                                ),
                                indexes: vec![FieldIndex::MapEach],
                            },
                            op: ComparisonOpExpr::OneOf {
                                rhs: RhsValues::Bytes(vec![
                                    "Cookie".to_owned().into(),
                                    "Cookies".to_owned().into(),
                                ]),
                                variant: 0,
                            },
                        })
                    ))))
                })],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "name": "any",
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "op": "Not",
                            "arg": {
                                "lhs": [
                                    "http.request.headers.names",
                                    {
                                        "kind": "MapEach"
                                    }
                                ],
                                "op": "OneOf",
                                "rhs": [
                                    "Cookie",
                                    "Cookies"
                                ]
                            }
                        }
                    }
                ]
            }
        );
    }

    #[test]
    fn test_lex_function_with_any_arg_kind() {
        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3(
                "any(upper(http.request.headers.names[*])[*] CONTAINS \"C\")",
                &SCHEME,
                &VARIABLES,
                None
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(
                    ComparisonExpr {
                        lhs: IndexExpr {
                            lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                                function: SCHEME.get_function("upper").unwrap(),
                                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.names").unwrap()
                                    ),
                                    indexes: vec![FieldIndex::MapEach],
                                })],
                                return_type: Type::Bytes,
                                context: None,
                            }),
                            indexes: vec![FieldIndex::MapEach],
                        },
                        op: ComparisonOpExpr::Contains {
                            rhs: "C".to_string().into(),
                            variant: 1,
                        }
                    }
                ))],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "lhs": [
                                {
                                    "args": [
                                        {
                                            "kind": "IndexExpr",
                                            "value": ["http.request.headers.names", {"kind": "MapEach"}]
                                        }
                                    ],
                                    "name": "upper"
                                },{
                                    "kind": "MapEach"
                                }
                            ],
                            "op": "Contains",
                            "rhs": "C"
                        }
                    }
                ],
                "name": "any"
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with_3("echo(upper(\"abc\"))", &SCHEME, &VARIABLES, None),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: [FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("upper").unwrap(),
                        args: vec![FunctionCallArgExpr::Literal(RhsValue::Bytes(
                            "abc".to_owned().into()
                        ))],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                })]
                .to_vec(),
                return_type: Type::Bytes,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": {
                            "args": [
                                {
                                    "kind": "Literal",
                                    "value": "abc"
                                }
                            ],
                            "name": "upper"
                        }
                    }
                ],
                "name": "echo"
            }
        );
    }

    #[test]
    fn test_lex_function_call_expr_failure() {
        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( \"test\" );", &SCHEME, &VARIABLES, None),
            LexErrorKind::InvalidArgumentKind {
                index: 0,
                mismatch: FunctionArgKindMismatchError {
                    actual: FunctionArgKind::Literal,
                    expected: FunctionArgKind::Complex,
                }
            },
            "\"test\""
        );

        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( 10 );", &SCHEME, &VARIABLES, None),
            LexErrorKind::InvalidArgumentKind {
                index: 0,
                mismatch: FunctionArgKindMismatchError {
                    actual: FunctionArgKind::Literal,
                    expected: FunctionArgKind::Complex,
                }
            },
            "10"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( ip.addr );", &SCHEME, &VARIABLES, None),
            LexErrorKind::InvalidArgumentType {
                index: 0,
                mismatch: TypeMismatchError {
                    actual: Type::Ip,
                    expected: Type::Bytes.into(),
                }
            },
            "ip.addr"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.host, 10, 2, \"test\", 4.0 );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(4),
            },
            "4.0 );"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( http.test );", &SCHEME, &VARIABLES, None),
            LexErrorKind::UnknownIdentifier,
            "http.test"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( echo ( http.test ) );", &SCHEME, &VARIABLES, None),
            LexErrorKind::UnknownIdentifier,
            "http.test"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3("echo ( http.host[*] );", &SCHEME, &VARIABLES, None),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.request.headers.names[0][*] );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.request.headers.names[*][0] );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes,
            }),
            "[0]"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.headers[*][\"host\"] );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapKey("host".to_string()),
                actual: Type::Bytes,
            }),
            "[\"host\"]"
        );

        assert_err!(
            FunctionCallExpr::lex_with_3(
                "echo ( http.host, http.headers[*] );",
                &SCHEME,
                &VARIABLES,
                None
            ),
            LexErrorKind::InvalidMapEachAccess,
            "http.headers[*]"
        );
    }
}
