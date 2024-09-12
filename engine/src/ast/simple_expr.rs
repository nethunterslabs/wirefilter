use super::{
    field_expr::ComparisonExpr,
    logical_expr::LogicalExpr,
    visitor::{Visitor, VisitorMut},
    Expr,
};
use crate::{
    compiler::Compiler,
    execution_context::Variables,
    filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr},
    lex::{expect, skip_space, Lex, LexResult, LexWith3},
    scheme::Scheme,
    types::{GetType, Type},
};
use serde::Serialize;

lex_enum!(UnaryOp {
    "not" | "NOT" | "!" => Not,
});

/// SimpleExpr is a "generic" expression. It can be either a comparison
/// expression with [`SimpleExpr::Comparison`], a parenthesized expression
/// with [`SimpleExpr::Parenthesized`] or a unary expression with
/// [`SimpleExpr::Unary`].
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum SimpleExpr<'s> {
    /// A comparison expression.
    Comparison(ComparisonExpr<'s>),
    /// A parenthisized expression.
    Parenthesized(Box<LogicalExpr<'s>>),
    /// A unary expression.
    Unary {
        /// Unary operator.
        op: UnaryOp,
        /// Sub-expression.
        arg: Box<SimpleExpr<'s>>,
    },
}

impl<'s> GetType for SimpleExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            SimpleExpr::Comparison(op) => op.get_type(),
            SimpleExpr::Parenthesized(op) => op.get_type(),
            SimpleExpr::Unary { arg, .. } => arg.get_type(),
        }
    }
}

impl<'i, 's> LexWith3<'i, &'s Scheme, &Variables, Option<String>> for SimpleExpr<'s> {
    fn lex_with_3(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
        scope: Option<String>,
    ) -> LexResult<'i, Self> {
        Ok(if let Ok(input) = expect(input, "(") {
            let input = skip_space(input);
            let (op, input) = LogicalExpr::lex_with_3(input, scheme, variables, scope)?;
            let input = skip_space(input);
            let input = expect(input, ")")?;
            (SimpleExpr::Parenthesized(Box::new(op)), input)
        } else if let Ok((op, input)) = UnaryOp::lex(input) {
            let input = skip_space(input);
            let (arg, input) = SimpleExpr::lex_with_3(input, scheme, variables, scope)?;
            (
                SimpleExpr::Unary {
                    op,
                    arg: Box::new(arg),
                },
                input,
            )
        } else {
            let (op, input) = ComparisonExpr::lex_with_3(input, scheme, variables, scope)?;
            (SimpleExpr::Comparison(op), input)
        })
    }
}

impl<'s> Expr<'s> for SimpleExpr<'s> {
    #[inline]
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        match self {
            SimpleExpr::Comparison(node) => visitor.visit_comparison_expr(node),
            SimpleExpr::Parenthesized(node) => visitor.visit_logical_expr(node),
            SimpleExpr::Unary { arg, .. } => visitor.visit_simple_expr(arg),
        }
    }

    #[inline]
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        match self {
            SimpleExpr::Comparison(node) => visitor.visit_comparison_expr(node),
            SimpleExpr::Parenthesized(node) => visitor.visit_logical_expr(node),
            SimpleExpr::Unary { arg, .. } => visitor.visit_simple_expr(arg),
        }
    }

    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        match self {
            SimpleExpr::Comparison(op) => compiler.compile_comparison_expr(op, variables),
            SimpleExpr::Parenthesized(op) => compiler.compile_logical_expr(*op, variables),
            SimpleExpr::Unary {
                op: UnaryOp::Not(_),
                arg,
            } => {
                let arg = compiler.compile_simple_expr(*arg, variables);
                match arg {
                    CompiledExpr::One(one) => {
                        CompiledExpr::One(CompiledOneExpr::new(move |ctx, variables, state| {
                            !one.execute(ctx, variables, state)
                        }))
                    }
                    CompiledExpr::Vec(vec) => {
                        CompiledExpr::Vec(CompiledVecExpr::new(move |ctx, variables, state| {
                            vec.execute(ctx, variables, state)
                                .iter()
                                .map(|item| !item)
                                .collect()
                        }))
                    }
                }
            }
        }
    }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn test() {
    use crate::{
        execution_context::ExecutionContext,
        lex::{complete, LexErrorKind},
        lhs_types::Array,
    };

    let scheme = &Scheme! {
        t: Bool,
        at: Array(Bool),
        aat: Array(Array(Bool)),
    };

    let variables = Default::default();

    let ctx = &mut ExecutionContext::new(scheme);
    ctx.set_field_value(scheme.get_field("t").unwrap(), true)
        .unwrap();
    ctx.set_field_value(scheme.get_field("at").unwrap(), {
        let mut arr = Array::new(Type::Bool);
        arr.push(true.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();

    let t_expr = SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with_3(
            "t",
            scheme,
            &Default::default(),
            None,
        ))
        .unwrap(),
    );
    let t_expr = || t_expr.clone();

    let at_expr = SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with_3(
            "at",
            scheme,
            &Default::default(),
            None,
        ))
        .unwrap(),
    );
    let at_expr = || at_expr.clone();

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("t", scheme, &Default::default(), None),
            t_expr()
        );

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": "t",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("at", scheme, &Default::default(), None),
            at_expr()
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

        assert_json!(
            expr,
            {
                "lhs": "at",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![true, false, true].into_boxed_slice()
        );
    }

    {
        let expr = SimpleExpr::lex_with_3("at[*]", scheme, &Default::default(), None)
            .unwrap()
            .0;

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

        assert_json!(
            expr,
            {
                "lhs": ["at", {"kind": "MapEach"}],
                "op": "IsTrue"
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![true, false, true].into_boxed_slice()
        );
    }

    {
        assert_err!(
            SimpleExpr::lex_with_3("aat[*]", scheme, &Default::default(), None),
            LexErrorKind::UnsupportedOp {
                lhs_type: Type::Array(Box::new(Type::Array(Box::new(Type::Bool))))
            },
            ""
        );
    }

    let parenthesized_expr = |expr| SimpleExpr::Parenthesized(Box::new(LogicalExpr::Simple(expr)));

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("((t))", scheme, &Default::default(), None),
            parenthesized_expr(parenthesized_expr(t_expr()))
        );

        assert_json!(
            expr,
            {
                "lhs": "t",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("((at))", scheme, &Default::default(), None),
            parenthesized_expr(parenthesized_expr(at_expr()))
        );

        assert_json!(
            expr,
            {
                "lhs": "at",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![true, false, true].into_boxed_slice()
        );
    }

    let not_expr = |expr| SimpleExpr::Unary {
        op: UnaryOp::Not(0),
        arg: Box::new(expr),
    };

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("not t", scheme, &Default::default(), None),
            not_expr(t_expr())
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "lhs": "t",
                    "op": "IsTrue"
                }
            }
        );

        let expr = expr.compile(&variables);

        assert!(!expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    assert_ok!(
        SimpleExpr::lex_with_3("!t", scheme, &Default::default(), None),
        not_expr(t_expr())
    );

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("not at", scheme, &Default::default(), None),
            not_expr(at_expr())
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "lhs": "at",
                    "op": "IsTrue"
                }
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![false, true, false].into_boxed_slice()
        );
    }

    assert_ok!(
        SimpleExpr::lex_with_3("!at", scheme, &Default::default(), None),
        not_expr(at_expr())
    );

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("!!t", scheme, &Default::default(), None),
            not_expr(not_expr(t_expr()))
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "op": "Not",
                    "arg": {
                        "lhs": "t",
                        "op": "IsTrue"
                    }
                }
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    assert_ok!(
        SimpleExpr::lex_with_3("! (not !t)", scheme, &Default::default(), None),
        not_expr(parenthesized_expr(not_expr(not_expr(t_expr()))))
    );

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with_3("!!at", scheme, &Default::default(), None),
            not_expr(not_expr(at_expr()))
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "op": "Not",
                    "arg": {
                        "lhs": "at",
                        "op": "IsTrue"
                    }
                }
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![true, false, true].into_boxed_slice()
        );
    }

    assert_ok!(
        SimpleExpr::lex_with_3("! (not !at)", scheme, &Default::default(), None),
        not_expr(parenthesized_expr(not_expr(not_expr(at_expr()))))
    );
}
