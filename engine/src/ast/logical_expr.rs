use super::{
    simple_expr::SimpleExpr,
    visitor::{Visitor, VisitorMut},
    Expr,
};
use crate::{
    compiler::Compiler,
    execution_context::Variables,
    filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr},
    lex::{skip_space, Lex, LexErrorKind, LexResult, LexWith3},
    scheme::Scheme,
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;

lex_enum!(
    /// LogicalOp is an operator for a [`LogicalExpr`]. Its ordering is defined
    /// by the operators' precedences in ascending order.
    #[derive(PartialOrd, Ord)] LogicalOp {
        /// `or` / `OR` / `||` operator
        "or" | "OR" | "||" => Or,
        /// `xor` / `XOR` / `^^` operator
        "xor" | "XOR" | "^^" => Xor,
        /// `and` / `AND` / `&&` operator
        "and" | "AND" | "&&" => And,
    }
);

/// LogicalExpr is a either a generic sub-expression
/// or a logical conjunction expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum LogicalExpr<'s> {
    /// Sub-expression
    Simple(SimpleExpr<'s>),
    /// Logical conjunction expression
    Combining {
        /// Logical operator
        op: LogicalOp,
        /// List of sub-expressions
        items: Vec<LogicalExpr<'s>>,
    },
}

impl<'s> GetType for LogicalExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            LogicalExpr::Simple(lhs) => lhs.get_type(),
            LogicalExpr::Combining { ref items, .. } => items[0].get_type(),
        }
    }
}

impl<'s> LogicalExpr<'s> {
    fn lex_combining_op(input: &str) -> (Option<LogicalOp>, &str) {
        match LogicalOp::lex(skip_space(input)) {
            Ok((op, input)) => (Some(op), skip_space(input)),
            Err(_) => (None, input),
        }
    }

    fn lex_more_with_precedence<'i>(
        self,
        scheme: &'s Scheme,
        variables: &Variables,
        scope: Option<String>,
        min_prec: Option<LogicalOp>,
        mut lookahead: (Option<LogicalOp>, &'i str),
    ) -> LexResult<'i, Self> {
        let mut lhs = self;

        while let Some(op) = lookahead.0 {
            let mut rhs = SimpleExpr::lex_with_3(lookahead.1, scheme, variables, scope.clone())
                .map(|(op, input)| (LogicalExpr::Simple(op), input))?;

            loop {
                lookahead = Self::lex_combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = rhs.0.lex_more_with_precedence(
                    scheme,
                    variables,
                    scope.clone(),
                    lookahead.0,
                    lookahead,
                )?;
            }

            // check that the LogicalExpr is valid by ensuring both the left
            // hand side and right hand side of the operator are comparable.
            // For example, it doesn't make sense to do a logical operator on
            // a Bool and Bytes, or an Array(Bool) with Bool.
            let (lhsty, rhsty) = (lhs.get_type(), rhs.0.get_type());
            match (&lhsty, &rhsty) {
                (Type::Bool, Type::Bool) => {}
                (Type::Array(_), Type::Array(_)) => {}
                _ => {
                    return Err((
                        LexErrorKind::TypeMismatch(TypeMismatchError {
                            expected: lhsty.into(),
                            actual: rhsty,
                        }),
                        lookahead.1,
                    ))
                }
            }

            match lhs {
                LogicalExpr::Combining {
                    op: lhs_op,
                    ref mut items,
                } if lhs_op == op => {
                    items.push(rhs.0);
                }
                _ => {
                    lhs = LogicalExpr::Combining {
                        op,
                        items: vec![lhs, rhs.0],
                    };
                }
            }

            if lookahead.0 < min_prec {
                // pretend we haven't seen an operator if its precedence is
                // outside of our limits
                lookahead = (None, rhs.1);
            }
        }

        Ok((lhs, lookahead.1))
    }

    pub(crate) fn is_combining(&self) -> bool {
        matches!(self, LogicalExpr::Combining { .. })
    }
}

impl<'i, 's> LexWith3<'i, &'s Scheme, &Variables, Option<String>> for LogicalExpr<'s> {
    fn lex_with_3(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
        scope: Option<String>,
    ) -> LexResult<'i, Self> {
        let (lhs, input) = SimpleExpr::lex_with_3(input, scheme, variables, scope.clone())?;
        let lookahead = Self::lex_combining_op(input);
        LogicalExpr::Simple(lhs).lex_more_with_precedence(scheme, variables, scope, None, lookahead)
    }
}

impl<'s> Expr<'s> for LogicalExpr<'s> {
    #[inline]
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        match self {
            LogicalExpr::Simple(node) => visitor.visit_simple_expr(node),
            LogicalExpr::Combining { items, .. } => {
                items
                    .iter()
                    .for_each(|node| visitor.visit_logical_expr(node));
            }
        }
    }

    #[inline]
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        match self {
            LogicalExpr::Simple(node) => visitor.visit_simple_expr(node),
            LogicalExpr::Combining { items, .. } => {
                items
                    .iter_mut()
                    .for_each(|node| visitor.visit_logical_expr(node));
            }
        }
    }

    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        match self {
            LogicalExpr::Simple(op) => compiler.compile_simple_expr(op, variables),
            LogicalExpr::Combining { op, items } => {
                let items = items.into_iter();
                let mut items = items.map(|item| compiler.compile_logical_expr(item, variables));
                let first = items.next().unwrap();
                match first {
                    CompiledExpr::One(first) => {
                        let items = items
                            .map(|item| match item {
                                CompiledExpr::One(one) => one,
                                CompiledExpr::Vec(_) => unreachable!(),
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            LogicalOp::And(_) => CompiledExpr::One(CompiledOneExpr::new(
                                move |ctx, variables, state| {
                                    first.execute(ctx, variables, state)
                                        && items
                                            .iter()
                                            .all(|item| item.execute(ctx, variables, state))
                                },
                            )),
                            LogicalOp::Or(_) => CompiledExpr::One(CompiledOneExpr::new(
                                move |ctx, variables, state| {
                                    first.execute(ctx, variables, state)
                                        || items
                                            .iter()
                                            .any(|item| item.execute(ctx, variables, state))
                                },
                            )),
                            LogicalOp::Xor(_) => CompiledExpr::One(CompiledOneExpr::new(
                                move |ctx, variables, state| {
                                    items
                                        .iter()
                                        .fold(first.execute(ctx, variables, state), |acc, item| {
                                            acc ^ item.execute(ctx, variables, state)
                                        })
                                },
                            )),
                        }
                    }
                    CompiledExpr::Vec(first) => {
                        let items = items
                            .map(|item| match item {
                                CompiledExpr::One(_) => unreachable!(),
                                CompiledExpr::Vec(vec) => vec,
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            LogicalOp::And(_) => CompiledExpr::Vec(CompiledVecExpr::new(
                                move |ctx, variables, state| {
                                    let items = items
                                        .iter()
                                        .map(|item| item.execute(ctx, variables, state));
                                    let mut output =
                                        first.execute(ctx, variables, state).into_vec();
                                    for values in items {
                                        for (idx, val) in values.iter().enumerate() {
                                            if idx < output.len() {
                                                output[idx] = output[idx] && *val;
                                            }
                                        }
                                        if values.len() < output.len() {
                                            output.truncate(values.len());
                                        }
                                    }
                                    output.into_boxed_slice()
                                },
                            )),
                            LogicalOp::Or(_) => CompiledExpr::Vec(CompiledVecExpr::new(
                                move |ctx, variables, state| {
                                    let items = items
                                        .iter()
                                        .map(|item| item.execute(ctx, variables, state));
                                    let mut output =
                                        first.execute(ctx, variables, state).into_vec();
                                    for values in items {
                                        for (idx, val) in values.iter().enumerate() {
                                            if idx < output.len() {
                                                output[idx] = output[idx] || *val;
                                            }
                                        }
                                        if values.len() < output.len() {
                                            output.truncate(values.len());
                                        }
                                    }
                                    output.into_boxed_slice()
                                },
                            )),
                            LogicalOp::Xor(_) => CompiledExpr::Vec(CompiledVecExpr::new(
                                move |ctx, variables, state| {
                                    let items = items
                                        .iter()
                                        .map(|item| item.execute(ctx, variables, state));
                                    let mut output =
                                        first.execute(ctx, variables, state).into_vec();
                                    for values in items {
                                        for (idx, val) in values.iter().enumerate() {
                                            if idx < output.len() {
                                                output[idx] ^= *val;
                                            }
                                        }
                                        if values.len() < output.len() {
                                            output.truncate(values.len());
                                        }
                                    }
                                    output.into_boxed_slice()
                                },
                            )),
                        }
                    }
                }
            }
        }
    }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn test() {
    use super::field_expr::ComparisonExpr;
    use crate::{
        execution_context::ExecutionContext, lex::complete, lhs_types::Array, types::Type,
    };

    let scheme = &Scheme! {
        t: Bool,
        f: Bool,
        at: Array(Bool),
        af: Array(Bool),
    };

    let variables = Default::default();

    let ctx = &mut ExecutionContext::new(scheme);

    let t_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with_3(
            "t",
            scheme,
            &Default::default(),
            None,
        ))
        .unwrap(),
    ));

    let t_expr = || t_expr.clone();

    let f_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with_3(
            "f",
            scheme,
            &Default::default(),
            None,
        ))
        .unwrap(),
    ));

    let f_expr = || f_expr.clone();

    assert_ok!(
        LogicalExpr::lex_with_3("t", scheme, &Default::default(), None),
        t_expr()
    );

    let at_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with_3(
            "at",
            scheme,
            &Default::default(),
            None,
        ))
        .unwrap(),
    ));

    let at_expr = || at_expr.clone();

    let af_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with_3(
            "af",
            scheme,
            &Default::default(),
            None,
        ))
        .unwrap(),
    ));

    let af_expr = || af_expr.clone();

    assert_ok!(
        LogicalExpr::lex_with_3("at", scheme, &Default::default(), None),
        at_expr()
    );

    ctx.set_field_value(scheme.get_field("t").unwrap(), true)
        .unwrap();
    ctx.set_field_value(scheme.get_field("f").unwrap(), false)
        .unwrap();
    ctx.set_field_value(scheme.get_field("at").unwrap(), {
        let mut arr = Array::new(Type::Bool);
        arr.push(true.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();
    ctx.set_field_value(scheme.get_field("af").unwrap(), {
        let mut arr = Array::new(Type::Bool);
        arr.push(false.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("t and t", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::And(0),
                items: vec![t_expr(), t_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("t and f", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::And(0),
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "And",
                "items": [
                    {
                        "lhs": "t",
                        "op": "IsTrue"
                    },
                    {
                        "lhs": "f",
                        "op": "IsTrue"
                    }
                ]
            }
        );

        let expr = expr.compile(&variables);

        assert!(!expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("t or f", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Or(0),
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "Or",
                "items": [
                    {
                        "lhs": "t",
                        "op": "IsTrue"
                    },
                    {
                        "lhs": "f",
                        "op": "IsTrue"
                    }
                ]
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("f or f", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Or(0),
                items: vec![f_expr(), f_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert!(!expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("t xor f", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Xor(0),
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "Xor",
                "items": [
                    {
                        "lhs": "t",
                        "op": "IsTrue"
                    },
                    {
                        "lhs": "f",
                        "op": "IsTrue"
                    }
                ]
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("f xor f", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Xor(0),
                items: vec![f_expr(), f_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert!(!expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("f xor t", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Xor(0),
                items: vec![f_expr(), t_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert!(expr.execute_one(ctx, &Default::default(), &Default::default()));
    }

    assert_ok!(
        LogicalExpr::lex_with_3(
            "t or t && t and t or t ^^ t and t || t",
            scheme,
            &Default::default(),
            None
        ),
        LogicalExpr::Combining {
            op: LogicalOp::Or(0),
            items: vec![
                t_expr(),
                LogicalExpr::Combining {
                    op: LogicalOp::And(0),
                    items: vec![t_expr(), t_expr(), t_expr()],
                },
                LogicalExpr::Combining {
                    op: LogicalOp::Or(0),
                    items: vec![
                        LogicalExpr::Combining {
                            op: LogicalOp::Xor(0),
                            items: vec![
                                t_expr(),
                                LogicalExpr::Combining {
                                    op: LogicalOp::And(0),
                                    items: vec![t_expr(), t_expr()],
                                }
                            ],
                        },
                        t_expr(),
                    ],
                },
            ],
        }
    );

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("at and af", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::And(0),
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![false, false, true].into_boxed_slice()
        );
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("at or af", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Or(0),
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![true, false, true].into_boxed_slice()
        );
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with_3("at xor af", scheme, &Default::default(), None),
            LogicalExpr::Combining {
                op: LogicalOp::Xor(0),
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile(&variables);

        assert_eq!(
            expr.execute_vec(ctx, &Default::default(), &Default::default()),
            vec![true, false, false].into_boxed_slice()
        );
    }

    {
        assert_err!(
            LogicalExpr::lex_with_3("t and af", scheme, &Default::default(), None),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            LogicalExpr::lex_with_3("at and f", scheme, &Default::default(), None),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            LogicalExpr::lex_with_3("t or af", scheme, &Default::default(), None),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            LogicalExpr::lex_with_3("at or f", scheme, &Default::default(), None),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            LogicalExpr::lex_with_3("t xor af", scheme, &Default::default(), None),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            LogicalExpr::lex_with_3("at xor f", scheme, &Default::default(), None),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }
}
