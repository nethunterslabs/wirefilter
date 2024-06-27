use crate::{
    ComparisonExpr, CompiledExpr, CompiledValueExpr, Expr, FunctionCallArgExpr, FunctionCallExpr,
    IndexExpr, LogicalExpr, SimpleExpr, ValueExpr, Variables,
};

/// Trait used to drive the compilation of a [`FilterAst`] into a [`Filter`].
pub trait Compiler<'s, U: 's = ()>: Sized + 's {
    /// Compiles a [`Expr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_expr(&mut self, node: impl Expr<'s>, variables: &Variables) -> CompiledExpr<'s, U> {
        node.compile_with_compiler(self, variables)
    }

    /// Compiles a [`SimpleExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_simple_expr(
        &mut self,
        node: SimpleExpr<'s>,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        self.compile_expr(node, variables)
    }

    /// Compiles a [`LogicalExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_logical_expr(
        &mut self,
        node: LogicalExpr<'s>,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        self.compile_expr(node, variables)
    }

    /// Compiles a [`ComparisonExpr`] node into a [`CompiledExpr`] (boxed
    /// closure).
    #[inline]
    fn compile_comparison_expr(
        &mut self,
        node: ComparisonExpr<'s>,
        variables: &Variables,
    ) -> CompiledExpr<'s, U> {
        self.compile_expr(node, variables)
    }

    /// Compiles a [`ValueExpr`] node into a [`CompiledValueExpr`] (boxed
    /// closure).
    #[inline]
    fn compile_value_expr(
        &mut self,
        node: impl ValueExpr<'s>,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        node.compile_with_compiler(self, variables)
    }

    /// Compiles a [`FunctionCallExpr`] node into a [`CompiledValueExpr`] (boxed
    /// closure).
    #[inline]
    fn compile_function_call_expr(
        &mut self,
        node: FunctionCallExpr<'s>,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        self.compile_value_expr(node, variables)
    }

    /// Compiles a [`FunctionCallArgExpr`] node into a [`CompiledValueExpr`]
    /// (boxed closure).
    #[inline]
    fn compile_function_call_arg_expr(
        &mut self,
        node: FunctionCallArgExpr<'s>,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        self.compile_value_expr(node, variables)
    }

    /// Compiles a [`IndexExpr`] node into a [`CompiledValueExpr`] (boxed
    /// closure).
    #[inline]
    fn compile_index_expr(
        &mut self,
        node: IndexExpr<'s>,
        variables: &Variables,
    ) -> CompiledValueExpr<'s, U> {
        self.compile_value_expr(node, variables)
    }
}

/// Default compiler
#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultCompiler {}

impl DefaultCompiler {
    /// Creates a new [`DefaultCompiler`].
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'s, U: 's> Compiler<'s, U> for DefaultCompiler {}
