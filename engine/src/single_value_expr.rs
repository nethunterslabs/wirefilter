//! Each AST expression node gets compiled into CompiledValueExpr.
//! Therefore, SingleValueExpr essentialy is a public API facade for a
//! tree of CompiledValueExprs. When SingleValueExpr gets executed it calls `execute`
//! method on its root expression which then under the hood propagates field
//! values to its leafs by recursively calling their `execute` methods and
//! aggregating results into a single value as recursion unwinds.

use thiserror::Error;

use crate::{
    execution_context::ExecutionContext,
    filter::CompiledValueExpr,
    scheme::Scheme,
    types::{LhsValue, Type},
};

/// AM IR for a compiled single value expression.
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
pub struct SingleValueExpr<'s, U = ()> {
    root_expr: CompiledValueExpr<'s, U>,
    scheme: &'s Scheme,
}

impl<'s, U> SingleValueExpr<'s, U> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledValueExpr<'s, U>, scheme: &'s Scheme) -> Self {
        SingleValueExpr { root_expr, scheme }
    }

    /// Executes a single value expression against a provided context with values
    /// and returns the result.
    pub fn execute<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
    ) -> Result<LhsValue<'e>, SingleValueExprError> {
        if ctx.scheme() == self.scheme {
            self.root_expr
                .execute(ctx)
                .map_err(SingleValueExprError::TypeMismatch)
        } else {
            Err(SingleValueExprError::SchemeMismatch)
        }
    }
}

/// An error that occurs when executing a single value expression.
#[derive(Debug, PartialEq, Error)]
pub enum SingleValueExprError {
    /// An error that occurs when the scheme of the provided context does not
    /// match the scheme of the single value expression.
    #[error("Scheme mismatch")]
    SchemeMismatch,
    /// An error that occurs when the type of the value returned by the single
    /// value expression does not match the expected type.
    #[error("Type mismatch: `{0:?}`")]
    TypeMismatch(Type),
}

#[cfg(test)]
mod tests {
    use crate::execution_context::ExecutionContext;
    use crate::{
        functions::{
            FunctionArgKind, FunctionArgs, SimpleFunctionDefinition, SimpleFunctionImpl,
            SimpleFunctionParam,
        },
        types::{LhsValue, Type},
    };

    fn lower_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
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

    #[test]
    fn test_run_single_value_expr() {
        let mut scheme = Scheme! { foo: Bytes };
        scheme
            .add_function(
                "lower".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
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
                "is_true".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bool,
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Bool,
                    implementation: SimpleFunctionImpl::new(|args| {
                        Some(LhsValue::Bool(
                            args.next()
                                .unwrap()
                                .map_or(false, |v| v == LhsValue::Bool(true)),
                        ))
                    }),
                },
            )
            .unwrap();

        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value(
            scheme.get_field("foo").unwrap(),
            LhsValue::Bytes(b"HELLO".into()),
        )
        .unwrap();

        // Test simple field access
        let value_expr = scheme.parse_single_value_expr("foo").unwrap();
        let result = value_expr.compile().execute(&ctx);
        assert_eq!(result, Ok(LhsValue::Bytes(b"HELLO".into())));

        // Test function call
        let value_expr = scheme.parse_single_value_expr("lower(foo)").unwrap();
        let result = value_expr.compile().execute(&ctx);
        assert_eq!(result, Ok(LhsValue::Bytes(b"hello".into())));

        // Test function call with comparison expression as an argument
        let value_expr = scheme
            .parse_single_value_expr(r#"is_true(foo == "HELLO")"#)
            .unwrap();
        let result = value_expr.compile().execute(&ctx);
        assert_eq!(result, Ok(LhsValue::Bool(true)));

        // Test function call with function call in a comparison expression as an argument
        let value_expr = scheme
            .parse_single_value_expr(r#"is_true(lower(foo) == "hello")"#)
            .unwrap();
        let result = value_expr.compile().execute(&ctx);
        assert_eq!(result, Ok(LhsValue::Bool(true)));
    }
}
