pub mod field_expr;
pub mod fmt;
pub mod function_expr;
pub mod index_expr;
pub mod logical_expr;
pub mod simple_expr;
pub mod visitor;

use self::{index_expr::SingleIndexExpr, logical_expr::LogicalExpr};
use crate::{
    compiler::{Compiler, DefaultCompiler},
    execution_context::Variables,
    filter::{CompiledExpr, CompiledValueExpr, Filter},
    lex::{LexErrorKind, LexResult, LexWith2},
    scheme::{Scheme, UnknownFieldError},
    single_value_expr::SingleValueExpr,
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;
use std::fmt::Debug;
use visitor::{UsesVariableVisitor, UsesVisitor, Visitor, VisitorMut};

/// Trait used to represent node that evaluates to a [`bool`] (or a
/// [`Vec<bool>`]).
pub trait Expr<'s>: Sized + Eq + Debug + Serialize {
    /// Recursively visit all nodes in the AST using a [`Visitor`].
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V);
    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V);
    /// Compiles current node into a [`CompiledExpr`] using [`Compiler`].
    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledExpr<'s, U>;
    /// Compiles current node into a [`CompiledExpr`] using [`DefaultCompiler`].
    fn compile(self, variables: &Variables) -> CompiledExpr<'s> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler, variables)
    }
}

/// Trait used to represent node that evaluates to an [`LhsValue`].
pub trait ValueExpr<'s>: Sized + Eq + Debug + Serialize {
    /// Recursively visit all nodes in the AST using a [`Visitor`].
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V);
    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V);
    /// Compiles current node into a [`CompiledValueExpr`] using [`Compiler`].
    fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U>;
    /// Compiles current node into a [`CompiledValueExpr`] using
    /// [`DefaultCompiler`].
    fn compile(self, variables: &Variables) -> CompiledValueExpr<'s> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler, variables)
    }
}

/// A parsed single value expression AST. Used to parse a SingleIndexExpr which is compiled then to a SingleValueExprAst.
///
/// It's attached to its corresponding [`Scheme`](struct@Scheme) because all
/// parsed fields are represented as indices and are valid only when
/// [`ExecutionContext`](::ExecutionContext) is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone, Hash)]
#[serde(transparent)]
pub struct SingleValueExprAst<'s> {
    /// The scheme that this AST is attached to.
    #[serde(skip)]
    pub scheme: &'s Scheme,
    /// The root of the AST.
    pub op: SingleIndexExpr<'s>,
}

impl<'s> Debug for SingleValueExprAst<'s> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.op, f)
    }
}

impl<'i, 's> LexWith2<'i, &'s Scheme, &Variables> for SingleValueExprAst<'s> {
    fn lex_with_2(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> LexResult<'i, Self> {
        let (op, input) = SingleIndexExpr::lex_with_2(input, scheme, variables)?;
        Ok((SingleValueExprAst { scheme, op }, input))
    }
}

impl<'s> SingleValueExprAst<'s> {
    /// Compiles a [`SingleValueExprAst`] into a [`SingleValueExpr`] using a specific
    /// [`Compiler`].
    pub fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> SingleValueExpr<'s, U> {
        let compiled = self.op.compile_with_compiler(compiler, variables);
        SingleValueExpr::new(compiled, self.scheme)
    }

    /// Compiles a [`SingleValueExprAst`] into a [`SingleValueExpr`] using [`DefaultCompiler`].
    pub fn compile(self, variables: &Variables) -> SingleValueExpr<'s> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler, variables)
    }
}

/// A parsed filter AST.
///
/// It's attached to its corresponding [`Scheme`](struct@Scheme) because all
/// parsed fields are represented as indices and are valid only when
/// [`ExecutionContext`](::ExecutionContext) is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone, Hash)]
#[serde(transparent)]
pub struct FilterAst<'s> {
    /// The scheme that this AST is attached to.
    #[serde(skip)]
    pub scheme: &'s Scheme,
    /// The root of the AST.
    pub op: LogicalExpr<'s>,
}

impl<'s> Debug for FilterAst<'s> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.op, f)
    }
}

impl<'i, 's> LexWith2<'i, &'s Scheme, &Variables> for FilterAst<'s> {
    fn lex_with_2(
        input: &'i str,
        scheme: &'s Scheme,
        variables: &Variables,
    ) -> LexResult<'i, Self> {
        let (op, input) = LogicalExpr::lex_with_2(input, scheme, variables)?;
        // LogicalExpr::lex_with can return an AST where the root is an
        // LogicalExpr::Combining of type [`Array(Bool)`].
        //
        // It must do this because we need to be able to use
        // LogicalExpr::Combining of type [`Array(Bool)`]
        // as arguments to functions, however it should not be valid as a
        // filter expression itself.
        //
        // Here we enforce the constraint that the root of the AST, a
        // LogicalExpr, must evaluate to type [`Bool`].
        let ty = op.get_type();
        match ty {
            Type::Bool => Ok((FilterAst { scheme, op }, input)),
            _ => Err((
                LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: Type::Bool.into(),
                    actual: ty,
                }),
                input,
            )),
        }
    }
}

impl<'s> FilterAst<'s> {
    /// Recursively visit all nodes in the AST using a [`Visitor`].
    #[inline]
    pub fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        visitor.visit_logical_expr(&self.op)
    }

    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    #[inline]
    pub fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V) {
        visitor.visit_logical_expr(&mut self.op)
    }

    /// Recursively checks whether a [`FilterAst`] uses a given field name.
    ///
    /// This is useful to lazily initialise expensive fields only if necessary.
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme.get_field(field_name).map(|field| {
            let mut visitor = UsesVisitor::new(field);
            self.walk(&mut visitor);
            visitor.uses()
        })
    }

    /// Recursively checks whether a [`FilterAst`] uses a variable.
    pub fn uses_variable(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme.get_field(field_name).map(|field| {
            let mut visitor = UsesVariableVisitor::new(field);
            self.walk(&mut visitor);
            visitor.uses()
        })
    }

    /// Compiles a [`FilterAst`] into a [`Filter`] using a specific
    /// [`Compiler`].
    pub fn compile_with_compiler<U: 's, C: Compiler<'s, U> + 's>(
        self,
        compiler: &mut C,
        variables: &Variables,
    ) -> Filter<'s, U> {
        match self.op.compile_with_compiler(compiler, variables) {
            CompiledExpr::One(one) => Filter::new(one, self.scheme),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    /// Compiles a [`FilterAst`] into a [`Filter`] using [`DefaultCompiler`].
    pub fn compile(self, variables: &Variables) -> Filter<'s> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler, variables)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        execution_context::{ExecutionContext, State, Variables},
        functions::{
            FunctionArgKind, FunctionArgs, SimpleFunctionDefinition, SimpleFunctionImpl,
            SimpleFunctionOptParam, SimpleFunctionParam,
        },
        types::LhsValue,
    };

    #[test]
    fn test_single_value_expr() {
        let mut scheme = Scheme! {
            http.request.headers: Map(Array(Bytes)),
            http.host: Bytes,
            http.request.headers.names: Array(Bytes),
            http.request.headers.values: Array(Bytes),
            http.request.headers.is_empty: Array(Bool),
            http.version: Float,
            ip.addr: Ip,
            ssl: Bool,
            tcp.port: Int,
        };

        fn echo_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            args.next()?.ok()
        }

        fn bytes<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
            let arg = args.next()?.ok()?;
            Some(arg)
        }

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
                "echo.int".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Any,
                        val_type: Type::Int,
                    }],
                    opt_params: Some(Vec::new()),
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(echo_function),
                },
            )
            .unwrap();

        scheme
            .add_function(
                "bytes".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Any,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(Vec::new()),
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(bytes),
                },
            )
            .unwrap();

        let mut variables = Variables::new();
        variables.add("func_test_var".to_string(), 10.into());

        let state = State::new();

        let compiled = SingleValueExprAst::lex_with_2("http.host", &scheme, &variables)
            .unwrap()
            .0
            .compile(&variables);

        let mut execution_context = ExecutionContext::new(&scheme);
        execution_context
            .set_field_value(
                scheme.get_field("http.host").unwrap(),
                LhsValue::Bytes(b"example.com".into()),
            )
            .unwrap();
        execution_context
            .set_field_value(scheme.get_field("tcp.port").unwrap(), LhsValue::Int(80))
            .unwrap();

        assert_eq!(
            compiled
                .execute(&execution_context, &variables, &state)
                .unwrap(),
            LhsValue::Bytes(b"example.com".into())
        );

        let compiled = SingleValueExprAst::lex_with_2("echo(http.host)", &scheme, &variables)
            .unwrap()
            .0
            .compile(&variables);

        assert_eq!(
            compiled
                .execute(&execution_context, &variables, &state)
                .unwrap(),
            LhsValue::Bytes(b"example.com".into())
        );

        let compiled =
            SingleValueExprAst::lex_with_2("echo(http.host, 1, 2, \"test\")", &scheme, &variables)
                .unwrap()
                .0
                .compile(&variables);

        assert_eq!(
            compiled
                .execute(&execution_context, &variables, &state)
                .unwrap(),
            LhsValue::Bytes(b"example.com".into())
        );

        let compiled = SingleValueExprAst::lex_with_2(
            "echo(http.host, $func_test_var, 2)",
            &scheme,
            &variables,
        )
        .unwrap()
        .0
        .compile(&variables);

        assert_eq!(
            compiled
                .execute(&execution_context, &variables, &state)
                .unwrap(),
            LhsValue::Bytes(b"example.com".into())
        );

        let compiled =
            SingleValueExprAst::lex_with_2("echo.int($func_test_var)", &scheme, &variables)
                .unwrap()
                .0
                .compile(&variables);

        assert_eq!(
            compiled
                .execute(&execution_context, &variables, &state)
                .unwrap(),
            LhsValue::Int(10)
        );

        let compiled = SingleValueExprAst::lex_with_2(
            r#"tcp.port cases {
                    80 => http.host,
                    443 | 8000..8080 => bytes("example.org"),
                    _ => bytes("example.net")
                }"#,
            &scheme,
            &variables,
        )
        .unwrap()
        .0
        .compile(&variables);

        assert_eq!(
            compiled
                .execute(&execution_context, &variables, &state)
                .unwrap(),
            LhsValue::Bytes(b"example.com".into())
        );
    }
}
