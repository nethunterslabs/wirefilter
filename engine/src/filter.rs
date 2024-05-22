//! Each AST expression node gets compiled into a CompiledExpr or a
//! CompiledValueExpr. Therefore, Filter essentialy is a public API facade for a
//! tree of Compiled(Value)Exprs. When filter gets executed it calls `execute`
//! method on its root expression which then under the hood propagates field
//! values to its leafs by recursively calling their `execute` methods and
//! aggregating results into a single boolean value as recursion unwinds.

use crate::{
    execution_context::{ExecutionContext, State},
    scheme::{Scheme, SchemeMismatchError},
    types::{LhsValue, Type},
};

type BoxedClosureToOneBool<'s, U> =
    Box<dyn for<'e> Fn(&'e ExecutionContext<'e, U>, &State<'s, 'e>) -> bool + Sync + Send + 's>;

/// Boxed closure for [`Expr`] AST node that evaluates to a simple [`bool`].
pub struct CompiledOneExpr<'s, U = ()>(BoxedClosureToOneBool<'s, U>);

impl<'s, U> CompiledOneExpr<'s, U> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e, U>, &State<'s, 'e>) -> bool + Sync + Send + 's,
    ) -> Self {
        CompiledOneExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e, U>, state: &State<'s, 'e>) -> bool {
        self.0(ctx, state)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToOneBool<'s, U> {
        self.0
    }
}

pub(crate) type CompiledVecExprResult = Box<[bool]>;

type BoxedClosureToVecBool<'s, U> = Box<
    dyn for<'e> Fn(&'e ExecutionContext<'e, U>, &State<'s, 'e>) -> CompiledVecExprResult
        + Sync
        + Send
        + 's,
>;

/// Boxed closure for [`Expr`] AST node that evaluates to a list of [`bool`].
pub struct CompiledVecExpr<'s, U = ()>(BoxedClosureToVecBool<'s, U>);

impl<'s, U> CompiledVecExpr<'s, U> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e, U>, &State<'s, 'e>) -> CompiledVecExprResult
            + Sync
            + Send
            + 's,
    ) -> Self {
        CompiledVecExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
        state: &State<'s, 'e>,
    ) -> CompiledVecExprResult {
        self.0(ctx, state)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToVecBool<'s, U> {
        self.0
    }
}

/// Enum of boxed closure for [`Expr`] AST nodes.
pub enum CompiledExpr<'s, U = ()> {
    /// Variant for [`Expr`] AST node that evaluates to a simple [`bool`].
    One(CompiledOneExpr<'s, U>),
    /// Variant for [`Expr`] AST node that evaluates to a list of [`bool`].
    Vec(CompiledVecExpr<'s, U>),
}

impl<'s, U> CompiledExpr<'s, U> {
    #[cfg(test)]
    pub(crate) fn execute_one<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
        state: &State<'s, 'e>,
    ) -> bool {
        match self {
            CompiledExpr::One(one) => one.execute(ctx, state),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    #[cfg(test)]
    pub(crate) fn execute_vec<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
        state: &State<'s, 'e>,
    ) -> CompiledVecExprResult {
        match self {
            CompiledExpr::One(_) => unreachable!(),
            CompiledExpr::Vec(vec) => vec.execute(ctx, state),
        }
    }
}

pub type CompiledValueResult<'a> = Result<LhsValue<'a>, Type>;

impl<'a> From<LhsValue<'a>> for CompiledValueResult<'a> {
    fn from(value: LhsValue<'a>) -> Self {
        Ok(value)
    }
}

impl<'a> From<Type> for CompiledValueResult<'a> {
    fn from(ty: Type) -> Self {
        Err(ty)
    }
}

type BoxedClosureToValue<'s, U> = Box<
    dyn for<'e> Fn(&'e ExecutionContext<'e, U>, &State<'s, 'e>) -> CompiledValueResult<'e>
        + Sync
        + Send
        + 's,
>;

/// Boxed closure for [`ValueExpr`] AST node that evaluates to an [`LhsValue`].
pub struct CompiledValueExpr<'s, U = ()>(BoxedClosureToValue<'s, U>);

impl<'s, U> CompiledValueExpr<'s, U> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e, U>, &State<'s, 'e>) -> CompiledValueResult<'e>
            + Sync
            + Send
            + 's,
    ) -> Self {
        CompiledValueExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
        state: &State<'s, 'e>,
    ) -> CompiledValueResult<'e> {
        self.0(ctx, state)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToValue<'s, U> {
        self.0
    }
}

/// An IR for a compiled filter expression.
///
/// Currently it works by creating and combining boxed untyped closures and
/// performing indirect calls between them, which is fairly cheap, but,
/// surely, not as fast as an inline code with real JIT compilers.
///
/// On the other hand, it's much less risky than allocating, trusting and
/// executing code at runtime, because all the code being executed is
/// already statically generated and verified by the Rust compiler and only the
/// data differs. For the same reason, our "compilation" times are much better
/// than with a full JIT compiler as well.
///
/// In the future the underlying representation might change, but for now it
/// provides the best trade-off between safety and performance of compilation
/// and execution.
pub struct Filter<'s, U = ()> {
    root_expr: CompiledOneExpr<'s, U>,
    scheme: &'s Scheme,
}

impl<'s, U> Filter<'s, U> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledOneExpr<'s, U>, scheme: &'s Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a filter against a provided context with values and an internal mutable state.
    pub fn execute<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
        state: &State<'s, 'e>,
    ) -> Result<bool, SchemeMismatchError> {
        if ctx.scheme() == self.scheme {
            Ok(self.root_expr.execute(ctx, state))
        } else {
            Err(SchemeMismatchError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Filter, LhsValue, SchemeMismatchError};
    use crate::{
        execution_context::{ExecutionContext, State},
        functions::{
            FunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam,
        },
        types::Type,
    };

    #[test]
    fn test_scheme_mismatch() {
        let scheme1 = Scheme! { foo: Int };
        let scheme2 = Scheme! { foo: Int, bar: Int };
        let filter = scheme1.parse("foo == 42").unwrap().compile();
        let ctx = ExecutionContext::new(&scheme2);

        assert_eq!(
            filter.execute(&ctx, &Default::default()),
            Err(SchemeMismatchError)
        );
    }

    #[test]
    fn ensure_send_and_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        is_send::<Filter<'_, ExecutionContext<'_>>>();
        is_sync::<Filter<'_, ExecutionContext<'_>>>();
    }

    #[test]
    fn test_state() {
        let mut scheme = Scheme! { foo: Int };
        scheme
            .add_function(
                "multiply_by_secret_number".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Int,
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(|args, state| {
                        if let LhsValue::Int(arg) = args.next().unwrap().unwrap() {
                            if let LhsValue::Int(secret_number) =
                                state.get("secret-number").unwrap()
                            {
                                return Some(LhsValue::Int(arg * secret_number));
                            }
                        }
                        None
                    }),
                },
            )
            .unwrap();
        let single_value_expr = scheme
            .parse_single_value_expr("multiply_by_secret_number(foo)")
            .unwrap()
            .compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value(scheme.get_field("foo").unwrap(), LhsValue::Int(42))
            .unwrap();

        let mut state = State::new();
        state.insert("secret-number", LhsValue::Int(42));

        assert_eq!(
            single_value_expr.execute(&ctx, &state),
            Ok(LhsValue::Int(42 * 42))
        );
    }
}
