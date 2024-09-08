use crate::{
    ast::{
        field_expr::{Cases, IntOp},
        simple_expr::UnaryOp,
        SingleIndexExpr,
    },
    rhs_types::{Bytes, ExplicitIpRange, FloatRange, IntRange, IpRange, StrType},
    CasePatternValue, ComparisonExpr, ComparisonOpExpr, FieldIndex, FilterAst, FunctionCallArgExpr,
    FunctionCallExpr, IndexExpr, LhsFieldExpr, LogicalExpr, LogicalOp, OrderingOp, RhsValue,
    RhsValues, SimpleExpr, SingleValueExprAst, Variables,
};
use thiserror::Error;

/// Error formatting, mismatched AST.
#[derive(Debug, PartialEq, Error)]
#[error("format error")]
pub enum FormatError {
    /// Error formatting, mismatched AST.
    #[error("format error")]
    MismatchedAst,
    /// Parse error.
    #[error("{0}")]
    ParseError(String),
}

impl Fmt for FieldIndex {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            FieldIndex::ArrayIndex(i) => output.push_str(&i.to_string()),
            FieldIndex::MapKey(k) => {
                output.push('"');
                output.push_str(&escape(k, true));
                output.push('"');
            }
            FieldIndex::MapEach => output.push('*'),
        }
    }
}

impl Fmt for CasePatternValue {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            CasePatternValue::Bool => output.push('_'),
            CasePatternValue::Int(num) => output.push_str(&num.to_string()),
            CasePatternValue::IntRange(int_range) => int_range.fmt(0, output),
            CasePatternValue::Float(float_num) => {
                output.push_str(&format!("{:?}", float_num.into_inner()))
            }
            CasePatternValue::FloatRange(float_range) => float_range.fmt(0, output),
            CasePatternValue::Bytes(bytes) => bytes.fmt(0, output),
            CasePatternValue::Ip(ip) => output.push_str(&ip.to_string()),
            CasePatternValue::IpRange(ip_range) => ip_range.fmt(0, output),
            CasePatternValue::Regex(_)
            | CasePatternValue::Like(_)
            | CasePatternValue::Array(_)
            | CasePatternValue::Map(_) => {
                unreachable!()
            }
        }
    }
}

impl Fmt for RhsValue {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            RhsValue::Ip(ip) => output.push_str(&ip.to_string()),
            RhsValue::Bytes(bytes) => bytes.fmt(0, output),
            RhsValue::Int(num) => output.push_str(&num.to_string()),
            RhsValue::Float(float_num) => output.push_str(&format!("{:?}", float_num.into_inner())),
            RhsValue::Bool(_)
            | RhsValue::Array(_)
            | RhsValue::Map(_)
            | RhsValue::Regex(_)
            | RhsValue::Like(_) => {
                unreachable!()
            }
        }
    }
}

fn calculate_indent(output: &str) -> usize {
    let last_line = output.rsplit_once('\n').map(|(_, s)| s).unwrap_or(output);
    let last_line_indent: usize = last_line.len();
    last_line_indent + (last_line_indent % 2)
}

impl Fmt for RhsValues {
    fn fmt(&self, _indent: usize, output: &mut String) {
        let indent = calculate_indent(output);
        let indent_str = " ".repeat(indent);
        let len;

        output.push('[');
        match self {
            RhsValues::Ip(ips) => {
                len = ips.len();
                for ip in ips {
                    if len > 1 {
                        output.push('\n');
                        output.push_str(&indent_str);
                        output.push_str("  ");
                    } else {
                        output.push(' ');
                    }
                    ip.fmt(0, output);
                    if len > 0 {
                        output.push(',');
                    } else {
                        output.push(' ');
                    }
                }
            }
            RhsValues::Bytes(bytes) => {
                len = bytes.len();
                for byte in bytes {
                    if len > 1 {
                        output.push('\n');
                        output.push_str(&indent_str);
                        output.push_str("  ");
                    } else {
                        output.push(' ');
                    }
                    byte.fmt(0, output);
                    if len > 0 {
                        output.push(',');
                    } else {
                        output.push(' ');
                    }
                }
            }
            RhsValues::Int(ints) => {
                len = ints.len();
                for int in ints {
                    if len > 1 {
                        output.push('\n');
                        output.push_str(&indent_str);
                        output.push_str("  ");
                    } else {
                        output.push(' ');
                    }
                    int.fmt(0, output);
                    if len > 0 {
                        output.push(',');
                    } else {
                        output.push(' ');
                    }
                }
            }
            RhsValues::Float(floats) => {
                len = floats.len();
                for float in floats {
                    if len > 1 {
                        output.push('\n');
                        output.push_str(&indent_str);
                        output.push_str("  ");
                    } else {
                        output.push(' ');
                    }
                    float.fmt(0, output);
                    if len > 0 {
                        output.push(',');
                    } else {
                        output.push(' ');
                    }
                }
            }
            RhsValues::Bool(_)
            | RhsValues::Array(_)
            | RhsValues::Map(_)
            | RhsValues::Regex(_)
            | RhsValues::Like(_) => {
                unreachable!()
            }
        }

        if len > 1 {
            output.push('\n');
            output.push_str(&" ".repeat(indent));
        }
        output.push(']');
    }
}

trait Fmt {
    fn fmt(&self, indent: usize, output: &mut String);
}

impl<'s> Fmt for LhsFieldExpr<'s> {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            LhsFieldExpr::Field(field) => output.push_str(field.name()),
            LhsFieldExpr::FunctionCallExpr(call) => call.fmt(0, output),
        }
    }
}

impl Fmt for OrderingOp {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            OrderingOp::Equal(variant) => match *variant {
                0 => output.push_str(" eq "),
                1 => output.push_str(" EQ "),
                _ => output.push_str(" == "),
            },
            OrderingOp::NotEqual(variant) => match *variant {
                0 => output.push_str(" ne "),
                1 => output.push_str(" NE "),
                _ => output.push_str(" != "),
            },
            OrderingOp::GreaterThanEqual(variant) => match *variant {
                0 => output.push_str(" ge "),
                1 => output.push_str(" GE "),
                _ => output.push_str(" >= "),
            },
            OrderingOp::LessThanEqual(variant) => match *variant {
                0 => output.push_str(" le "),
                1 => output.push_str(" LE "),
                _ => output.push_str(" <= "),
            },
            OrderingOp::GreaterThan(variant) => match *variant {
                0 => output.push_str(" gt "),
                1 => output.push_str(" GT "),
                _ => output.push_str(" > "),
            },
            OrderingOp::LessThan(variant) => match *variant {
                0 => output.push_str(" lt "),
                1 => output.push_str(" LT "),
                _ => output.push_str(" < "),
            },
        }
    }
}

impl Fmt for IntOp {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            IntOp::BitwiseAnd(variant) => match *variant {
                0 => output.push_str(" & "),
                1 => output.push_str(" bitwise_and "),
                _ => output.push_str(" BITWISE_AND "),
            },
        }
    }
}

impl<'s> Fmt for ComparisonExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        self.lhs.fmt(0, output);

        match &self.op {
            ComparisonOpExpr::IsTrue => {}

            ComparisonOpExpr::Ordering { op, rhs } => {
                op.fmt(0, output);
                rhs.fmt(0, output);
            }
            ComparisonOpExpr::OrderingVariable { op, var } => {
                op.fmt(0, output);
                output.push('$');
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::Cases(cases) => {
                cases.fmt(indent, output);
            }

            ComparisonOpExpr::Int { op, rhs } => {
                op.fmt(0, output);
                output.push_str(&rhs.to_string());
            }
            ComparisonOpExpr::IntVariable { op, var } => {
                op.fmt(0, output);
                output.push('$');
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::Contains {
                rhs: bytes,
                variant,
            } => {
                match *variant {
                    0 => output.push_str(" contains "),
                    _ => output.push_str(" CONTAINS "),
                }
                bytes.fmt(0, output);
            }
            ComparisonOpExpr::ContainsVariable { var, variant } => {
                match *variant {
                    0 => output.push_str(" contains $"),
                    _ => output.push_str(" CONTAINS $"),
                }
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::Matches {
                rhs: regex,
                variant,
            } => {
                match *variant {
                    0 => output.push_str(" ~ "),
                    1 => output.push_str(" matches "),
                    _ => output.push_str(" MATCHES "),
                }
                match regex.ty {
                    StrType::Raw { hash_count } => {
                        let hashes = "#".repeat(hash_count);
                        output.push('r');
                        output.push_str(&hashes);
                        output.push('"');
                        output.push_str(regex.as_str());
                        output.push('"');
                        output.push_str(&hashes);
                    }
                    StrType::Escaped => {
                        output.push('"');
                        let mut escaped_regex = String::new();
                        let mut in_char_class = false;
                        for c in regex.as_str().chars() {
                            match c {
                                '"' if !in_char_class => {
                                    escaped_regex.push('\\');
                                    escaped_regex.push('"');
                                }
                                '[' => {
                                    in_char_class = true;
                                    escaped_regex.push('[');
                                }
                                ']' => {
                                    in_char_class = false;
                                    escaped_regex.push(']');
                                }
                                _ => escaped_regex.push(c),
                            }
                        }
                        output.push_str(&escaped_regex);
                        output.push('"');
                    }
                }
            }
            ComparisonOpExpr::MatchesVariable { var, variant } => {
                match *variant {
                    0 => output.push_str(" ~ $"),
                    1 => output.push_str(" matches $"),
                    _ => output.push_str(" MATCHES $"),
                }
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::Like { rhs: like, variant } => {
                if like.is_case_insensitive() {
                    match *variant {
                        0 => output.push_str(" like_case_insensitive "),
                        1 => output.push_str(" like_ci "),
                        2 => output.push_str(" LIKE_CASE_INSENSITIVE "),
                        _ => output.push_str(" LIKE_CI "),
                    }
                } else {
                    match *variant {
                        0 => output.push_str(" like "),
                        _ => output.push_str(" LIKE "),
                    }
                }
                match like.ty() {
                    StrType::Raw { hash_count } => {
                        let hashes = "#".repeat(hash_count);
                        output.push('r');
                        output.push_str(&hashes);
                        output.push('"');
                        output.push_str(like.pattern().as_str());
                        output.push('"');
                        output.push_str(&hashes);
                    }
                    StrType::Escaped => {
                        output.push('"');
                        output.push_str(&escape(like.pattern().as_str(), true));
                        output.push('"');
                    }
                }
            }
            ComparisonOpExpr::LikeVariable {
                var,
                case_insensitive,
                variant,
            } => {
                if *case_insensitive {
                    match *variant {
                        0 => output.push_str(" like_case_insensitive $"),
                        1 => output.push_str(" like_ci $"),
                        2 => output.push_str(" LIKE_CASE_INSENSITIVE $"),
                        _ => output.push_str(" LIKE_CI $"),
                    }
                } else {
                    match *variant {
                        0 => output.push_str(" like $"),
                        _ => output.push_str(" LIKE $"),
                    }
                }
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::OneOf {
                rhs: values,
                variant,
            } => {
                match *variant {
                    0 => output.push_str(" in "),
                    _ => output.push_str(" IN "),
                }
                values.fmt(0, output);
            }
            ComparisonOpExpr::OneOfVariable { var, variant } => {
                match *variant {
                    0 => output.push_str(" in $"),
                    _ => output.push_str(" IN $"),
                }
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::HasAny {
                rhs: values,
                case_insensitive,
                variant,
            } => {
                if *case_insensitive {
                    match *variant {
                        0 => output.push_str(" has_any_case_insensitive "),
                        1 => output.push_str(" has_any_ci "),
                        2 => output.push_str(" HAS_ANY_CASE_INSENSITIVE "),
                        _ => output.push_str(" HAS_ANY_CI "),
                    }
                } else {
                    match *variant {
                        0 => output.push_str(" has_any "),
                        _ => output.push_str(" HAS_ANY "),
                    }
                }
                values.fmt(0, output);
            }
            ComparisonOpExpr::HasAnyVariable {
                var,
                case_insensitive,
                variant,
            } => {
                if *case_insensitive {
                    match *variant {
                        0 => output.push_str(" has_any_case_insensitive $"),
                        1 => output.push_str(" has_any_ci $"),
                        2 => output.push_str(" HAS_ANY_CASE_INSENSITIVE $"),
                        _ => output.push_str(" HAS_ANY_CI $"),
                    }
                } else {
                    match *variant {
                        0 => output.push_str(" has_any $"),
                        _ => output.push_str(" HAS_ANY $"),
                    }
                }
                output.push_str(var.name_as_str());
            }

            ComparisonOpExpr::HasAll {
                rhs: values,
                case_insensitive,
                variant,
            } => {
                if *case_insensitive {
                    match *variant {
                        0 => output.push_str(" has_all_case_insensitive "),
                        1 => output.push_str(" has_all_ci "),
                        2 => output.push_str(" HAS_ALL_CASE_INSENSITIVE "),
                        _ => output.push_str(" HAS_ALL_CI "),
                    }
                } else {
                    match *variant {
                        0 => output.push_str(" has_all "),
                        _ => output.push_str(" HAS_ALL "),
                    }
                }
                values.fmt(0, output);
            }
            ComparisonOpExpr::HasAllVariable {
                var,
                case_insensitive,
                variant,
            } => {
                if *case_insensitive {
                    match *variant {
                        0 => output.push_str(" has_all_case_insensitive $"),
                        1 => output.push_str(" has_all_ci $"),
                        2 => output.push_str(" HAS_ALL_CASE_INSENSITIVE $"),
                        _ => output.push_str(" HAS_ALL_CI $"),
                    }
                } else {
                    match *variant {
                        0 => output.push_str(" has_all $"),
                        _ => output.push_str(" HAS_ALL $"),
                    }
                }
                output.push_str(var.name_as_str());
            }
        }
    }
}

impl<'s> Fmt for LogicalExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        match self {
            LogicalExpr::Simple(expr) => expr.fmt(indent, output),
            LogicalExpr::Combining { op, items } => {
                let indent_str = " ".repeat(indent);

                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        output.push('\n');
                        output.push_str(&indent_str);
                        match op {
                            LogicalOp::And(variant) => match *variant {
                                0 => output.push_str("and "),
                                1 => output.push_str("AND "),
                                _ => output.push_str("&& "),
                            },
                            LogicalOp::Or(variant) => match *variant {
                                0 => output.push_str("or "),
                                1 => output.push_str("OR "),
                                _ => output.push_str("|| "),
                            },
                            LogicalOp::Xor(variant) => match *variant {
                                0 => output.push_str("xor "),
                                1 => output.push_str("XOR "),
                                _ => output.push_str("^^ "),
                            },
                        }
                    }
                    item.fmt(indent, output);
                }
            }
        }
    }
}

impl<'s> Fmt for SimpleExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        match self {
            SimpleExpr::Comparison(node) => node.fmt(indent, output),
            SimpleExpr::Parenthesized(node) => {
                if node.is_combining() {
                    let indent_str = " ".repeat(indent);

                    output.push_str("(\n");
                    output.push_str(&indent_str);
                    output.push_str("  ");
                    node.fmt(indent + 2, output);
                    output.push('\n');
                    output.push_str(&indent_str);
                    output.push(')');
                } else {
                    output.push_str("( ");
                    node.fmt(indent, output);
                    output.push_str(" )");
                }
            }
            SimpleExpr::Unary { op, arg } => match op {
                UnaryOp::Not(variant) => {
                    match *variant {
                        0 => output.push_str("not "),
                        1 => output.push_str("NOT "),
                        _ => output.push('!'),
                    }
                    arg.fmt(indent, output);
                }
            },
        }
    }
}

impl<T: Fmt> Fmt for Cases<T> {
    fn fmt(&self, _indent: usize, output: &mut String) {
        let indent = calculate_indent(output);

        match self.variant {
            0 => output.push_str(" cases {"),
            1 => output.push_str(" CASES {"),
            _ => output.push_str(" => {"),
        }

        let indent_str = " ".repeat(indent + 2);

        for (patterns, expr) in &self.patterns {
            output.push('\n');
            output.push_str(&indent_str);
            for (i, pattern) in patterns.iter().enumerate() {
                if i > 0 {
                    output.push('\n');
                    output.push_str(&indent_str);
                    output.push_str("| ");
                }
                pattern.fmt(0, output);
            }
            output.push_str(" => ");
            expr.fmt(indent + 2, output);
            output.push(',');
        }

        output.push('\n');
        output.push_str(&" ".repeat(indent));
        output.push('}');
    }
}

impl<'s> Fmt for FunctionCallExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        output.push_str(self.function.name());
        output.push('(');
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                output.push_str(", ");
            }
            arg.fmt(indent, output);
        }
        output.push(')');
    }
}

impl<'s> Fmt for FunctionCallArgExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.fmt(indent, output),
            FunctionCallArgExpr::Literal(literal) => literal.fmt(indent, output),
            FunctionCallArgExpr::SimpleExpr(simple_expr) => simple_expr.fmt(indent, output),
            FunctionCallArgExpr::Variable(variable) => {
                output.push('$');
                output.push_str(variable.name_as_str())
            }
        }
    }
}

impl<'s> Fmt for IndexExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        self.lhs.fmt(indent, output);
        for index in &self.indexes {
            output.push('[');
            index.fmt(indent, output);
            output.push(']');
        }
    }
}

impl Fmt for Bytes {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            Bytes::Str { value, ty } => match ty {
                StrType::Raw { hash_count } => {
                    let hashes = "#".repeat(*hash_count);
                    output.push('r');
                    output.push_str(&hashes);
                    output.push('"');
                    output.push_str(value);
                    output.push('"');
                    output.push_str(&hashes);
                }
                StrType::Escaped => {
                    output.push('"');
                    output.push_str(&escape(value, true));
                    output.push('"');
                }
            },
            Bytes::Raw { value, separator } => {
                for (i, b) in value.iter().cloned().enumerate() {
                    if i != 0 {
                        output.push(separator.as_char());
                    }
                    output.push_str(&format!("{:02X}", b));
                }
            }
        }
    }
}

impl Fmt for FloatRange {
    fn fmt(&self, _indent: usize, output: &mut String) {
        let range = &self.0;
        if range.start() == range.end() {
            output.push_str(&format!("{:?}", range.start().into_inner()));
        } else {
            output.push_str(&format!("{:?}", range.start().into_inner()));
            output.push_str("..");
            output.push_str(&format!("{:?}", range.end().into_inner()));
        }
    }
}

impl Fmt for IntRange {
    fn fmt(&self, _indent: usize, output: &mut String) {
        let range = &self.0;
        if range.start() == range.end() {
            output.push_str(&range.start().to_string());
        } else {
            output.push_str(&range.start().to_string());
            output.push_str("..");
            output.push_str(&range.end().to_string());
        }
    }
}

impl Fmt for IpRange {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            IpRange::Explicit(range) => match range {
                ExplicitIpRange::V4(range) => {
                    output.push_str(&range.start().to_string());
                    output.push_str("..");
                    output.push_str(&range.end().to_string());
                }
                ExplicitIpRange::V6(range) => {
                    output.push_str(&range.start().to_string());
                    output.push_str("..");
                    output.push_str(&range.end().to_string());
                }
            },
            IpRange::Cidr(cidr) => {
                output.push_str(&cidr.to_string());
            }
        }
    }
}

fn escape(string: &str, hex_and_oct: bool) -> String {
    let mut res = String::new();
    for c in string.chars() {
        match c {
            '\n' => res.push_str(r"\n"),
            '\x00'..='\x1f' | '\x7f' if hex_and_oct => {
                res.push('\\');
                res.push('x');
                res.push_str(&format!("{:02x}", c as u8));
            }
            '\x20'..='\x7e' => match c {
                '\\' if hex_and_oct => {
                    res.push_str(r"\\");
                }
                '"' => {
                    res.push_str(r#"\""#);
                }
                _ => {
                    res.push(c);
                }
            },
            _ => {
                res.push(c);
            }
        }
    }
    res
}

impl<'s> Fmt for SingleIndexExpr<'s> {
    fn fmt(&self, indent: usize, output: &mut String) {
        self.op.fmt(indent, output);

        if let Some(cases) = &self.cases {
            cases.fmt(indent, output);
        }
    }
}

impl<'s> SingleValueExprAst<'s> {
    /// Format a [`SingleValueExprAst`] in an opinionated way.
    pub fn fmt(&self, variables: &Variables) -> Result<String, FormatError> {
        self.fmt_with_indent(0, variables)
    }

    /// Format a [`SingleValueExprAst`] in an opinionated way with an indent.
    pub fn fmt_with_indent(
        &self,
        indent: usize,
        variables: &Variables,
    ) -> Result<String, FormatError> {
        let mut formatted = String::new();
        self.op.fmt(indent, &mut formatted);

        let formatted_ast: SingleValueExprAst<'_> = self
            .scheme
            .parse_single_value_expr(&formatted, variables)
            .map_err(|e| FormatError::ParseError(e.to_string()))?;
        if self == &formatted_ast {
            Ok(formatted.trim().to_owned())
        } else {
            Err(FormatError::MismatchedAst)
        }
    }
}

impl<'s> FilterAst<'s> {
    /// Format a [`FilterAst`] in an opinionated way.
    pub fn fmt(&self, variables: &Variables) -> Result<String, FormatError> {
        self.fmt_with_indent(0, variables)
    }

    /// Format a [`FilterAst`] in an opinionated way with an indent.
    pub fn fmt_with_indent(
        &self,
        indent: usize,
        variables: &Variables,
    ) -> Result<String, FormatError> {
        let mut formatted = String::new();
        self.op.fmt(indent, &mut formatted);

        let formatted_ast = self
            .scheme
            .parse(&formatted, variables)
            .map_err(|e| FormatError::ParseError(e.to_string()))?;
        if self == &formatted_ast {
            Ok(formatted.trim().to_owned())
        } else {
            dbg!(self);
            dbg!(&formatted_ast);
            dbg!(formatted);
            Err(FormatError::MismatchedAst)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Array, ExecutionContext, FunctionArgKind, FunctionArgs, GetType, LhsValue, Map, Scheme,
        SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam,
        State, Type, Variables,
    };
    use lazy_static::lazy_static;
    use ordered_float::OrderedFloat;
    use std::{convert::TryFrom, net::IpAddr};

    fn any_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
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

    fn lower_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
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

    fn upper_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
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

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>, _: &State<'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.request.headers: Map(Array(Bytes)),
                http.host: Bytes,
                http.user_agent: Bytes,
                http.request.headers.names: Array(Bytes),
                http.request.headers.values: Array(Bytes),
                http.request.headers.is_empty: Array(Bool),
                http.version: Float,
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
                tcp.dport: Int,
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
        static ref EXECUTION_CONTEXT: ExecutionContext<'static> = {
            {
                let mut execution_context = ExecutionContext::new(&SCHEME);
                execution_context
                    .set_field_value(
                        SCHEME.get_field("http.host").unwrap(),
                        LhsValue::Bytes(b"example.com".into()),
                    )
                    .unwrap();
                execution_context
                    .set_field_value(SCHEME.get_field("tcp.port").unwrap(), LhsValue::Int(80))
                    .unwrap();
                execution_context
                    .set_field_value(SCHEME.get_field("tcp.dport").unwrap(), LhsValue::Int(443))
                    .unwrap();
                execution_context
                    .set_field_value(
                        SCHEME.get_field("http.version").unwrap(),
                        LhsValue::Float(OrderedFloat(1.1)),
                    )
                    .unwrap();
                execution_context
                    .set_field_value(
                        SCHEME.get_field("ip.addr").unwrap(),
                        LhsValue::Ip("127.0.0.1".parse::<IpAddr>().unwrap()),
                    )
                    .unwrap();
                execution_context
                    .set_field_value(SCHEME.get_field("ssl").unwrap(), LhsValue::Bool(true))
                    .unwrap();
                execution_context
                    .set_field_value(
                        SCHEME.get_field("http.user_agent").unwrap(),
                        LhsValue::Bytes(b"\\.\"abc\"".into()),
                    )
                    .unwrap();
                execution_context
                    .set_field_value(
                        SCHEME.get_field("http.request.headers").unwrap(),
                        LhsValue::Map({
                            let mut map = Map::new(Type::Array(Box::new(Type::Bytes)));
                            map.insert(b"host", {
                                let mut array = Array::new(Type::Bytes);
                                array.push(b"example.com".to_vec().into()).unwrap();
                                array.into()
                            })
                            .unwrap();
                            map.insert(b"user-agent", {
                                let mut array = Array::new(Type::Bytes);
                                array.push(b"Mozilla/5.0".to_vec().into()).unwrap();
                                array.into()
                            })
                            .unwrap();
                            map.insert(b"content-type", {
                                let mut array = Array::new(Type::Bytes);
                                array.push(b"application/json".to_vec().into()).unwrap();
                                array.into()
                            })
                            .unwrap();
                            map
                        }),
                    )
                    .unwrap();
                execution_context
            }
        };
        static ref VARIABLES: Variables = {
            let mut variables = Variables::new();
            variables.add(
                "in_var".to_string(),
                vec![b"example.com".to_vec(), b"example.org".to_vec()].into(),
            );
            variables.add(
                "has_any_var".to_string(),
                vec![b".com".to_vec(), b".org".to_vec()].into(),
            );
            variables.add(
                "has_all_var".to_string(),
                vec![b"exam".to_vec(), b"ple".to_vec()].into(),
            );
            variables.add("bool_var".to_string(), true.into());
            variables.add("bytes_var".to_string(), b"example.com".to_vec().into());
            variables.add("bytes_var2".to_string(), b"example.org".to_vec().into());
            variables.add("int_var".to_string(), 80.into());
            variables.add("float_var".to_string(), OrderedFloat(80.0).into());
            variables.add(
                "ip_var".to_string(),
                "127.0.0.1".parse::<IpAddr>().unwrap().into(),
            );
            variables
        };
        static ref STATE: State<'static> = State::new();
    }

    macro_rules! test_fmt {
        ($input:expr, $expected:expr) => {
            let ast = SCHEME.parse($input, &VARIABLES).unwrap();
            let formatted = ast.fmt(&VARIABLES).unwrap();
            assert_eq!(
                formatted, $expected,
                "Failed to format:\n{}\nGot:\n{}\nExpected:\n{}",
                $input, formatted, $expected
            );

            let filter = ast.compile(&VARIABLES);
            assert!(
                filter
                    .execute(&EXECUTION_CONTEXT, &VARIABLES, &STATE)
                    .unwrap(),
                "Failed to match filter: {}",
                $input
            );
        };
    }

    #[test]
    fn test_fmt_bytes_eq() {
        test_fmt!(
            r#" http.host  ==   "example.com"   "#,
            r#"http.host == "example.com""#
        );

        test_fmt!(
            r#"http.host  eq   "example.com"    "#,
            r#"http.host eq "example.com""#
        );
        test_fmt!(
            r#"http.host  EQ   "example.com"    "#,
            r#"http.host EQ "example.com""#
        );
    }

    #[test]
    fn test_fmt_float_eq() {
        test_fmt!(r#"http.version == 1.1"#, r#"http.version == 1.1"#);
    }

    #[test]
    fn test_fmt_bytes_eq_var() {
        test_fmt!(
            r#" http.host  ==   $bytes_var   "#,
            r#"http.host == $bytes_var"#
        );
    }

    #[test]
    fn test_fmt_not_bytes_eq() {
        test_fmt!(
            r#"!http.host  ==   "example.org"    "#,
            r#"!http.host == "example.org""#
        );

        test_fmt!(
            r#"not http.host  ==   "example.org"    "#,
            r#"not http.host == "example.org""#
        );
        test_fmt!(
            r#"NOT http.host  ==   "example.org"    "#,
            r#"NOT http.host == "example.org""#
        );
    }

    #[test]
    fn test_not_bytes_eq_var_fmt() {
        test_fmt!(
            r#"!http.host  ==   $bytes_var2    "#,
            r#"!http.host == $bytes_var2"#
        );

        test_fmt!(
            r#"NOT http.host  ==   $bytes_var2    "#,
            r#"NOT http.host == $bytes_var2"#
        );

        test_fmt!(
            r#"not http.host  ==   $bytes_var2    "#,
            r#"not http.host == $bytes_var2"#
        );
    }

    #[test]
    fn test_fmt_not_equals() {
        test_fmt!(
            r#"http.host  !=   "example.org"    "#,
            r#"http.host != "example.org""#
        );
        test_fmt!(
            r#"http.host  ne   "example.org"    "#,
            r#"http.host ne "example.org""#
        );
        test_fmt!(
            r#"http.host  NE   "example.org"    "#,
            r#"http.host NE "example.org""#
        );
    }

    #[test]
    fn test_fmt_escape() {
        test_fmt!(
            r#"http.host != "example\".com""#,
            r#"http.host != "example\".com""#
        );
    }

    #[test]
    fn test_fmt_colon_separated() {
        test_fmt!(
            r#"http.host == 65:78:61:6d:70:6c:65:2e:63:6f:6d"#,
            r#"http.host == 65:78:61:6D:70:6C:65:2E:63:6F:6D"#
        );
    }

    #[test]
    fn test_fmt_dot_separated() {
        test_fmt!(
            r#"http.host == 65.78.61.6d.70.6c.65.2e.63.6f.6d"#,
            r#"http.host == 65.78.61.6D.70.6C.65.2E.63.6F.6D"#
        );
    }

    #[test]
    fn test_fmt_dash_separated() {
        test_fmt!(
            r#"http.host == 65-78-61-6d-70-6c-65-2e-63-6f-6d"#,
            r#"http.host == 65-78-61-6D-70-6C-65-2E-63-6F-6D"#
        );
    }

    #[test]
    fn test_fmt_equals() {
        test_fmt!(r#"tcp.port == 80"#, r#"tcp.port == 80"#);
    }

    #[test]
    fn test_fmt_bitwise_and() {
        test_fmt!(r#"tcp.dport bitwise_and 1"#, r#"tcp.dport bitwise_and 1"#);
        test_fmt!(r#"tcp.dport BITWISE_AND 1"#, r#"tcp.dport BITWISE_AND 1"#);
        test_fmt!(r#"tcp.dport & 1"#, r#"tcp.dport & 1"#);
    }

    #[test]
    fn test_fmt_greater_than() {
        test_fmt!(r#"tcp.port > 70"#, r#"tcp.port > 70"#);
        test_fmt!(r#"tcp.port gt 70"#, r#"tcp.port gt 70"#);
        test_fmt!(r#"tcp.port GT 70"#, r#"tcp.port GT 70"#);
    }

    #[test]
    fn test_fmt_greater_than_or_equal_to() {
        test_fmt!(r#"tcp.port >= 80"#, r#"tcp.port >= 80"#);
        test_fmt!(r#"tcp.port ge 80"#, r#"tcp.port ge 80"#);
        test_fmt!(r#"tcp.port GE 80"#, r#"tcp.port GE 80"#);
    }

    #[test]
    fn test_fmt_less_than() {
        test_fmt!(r#"tcp.port < 90"#, r#"tcp.port < 90"#);
        test_fmt!(r#"tcp.port lt 90"#, r#"tcp.port lt 90"#);
        test_fmt!(r#"tcp.port LT 90"#, r#"tcp.port LT 90"#);
    }

    #[test]
    fn test_fmt_less_than_or_equal_to() {
        test_fmt!(r#"tcp.port <= 80"#, r#"tcp.port <= 80"#);
        test_fmt!(r#"tcp.port le 80"#, r#"tcp.port le 80"#);
        test_fmt!(r#"tcp.port LE 80"#, r#"tcp.port LE 80"#);
    }

    #[test]
    fn test_fmt_in() {
        test_fmt!(r#"http.host in $in_var"#, r#"http.host in $in_var"#);
        test_fmt!(
            r#"http.host in ["example.com", "example.org"]"#,
            r#"http.host in [
                "example.com",
                "example.org",
              ]"#
        );
        test_fmt!(
            r#"http.host IN ["example.com", "example.org"]"#,
            r#"http.host IN [
                "example.com",
                "example.org",
              ]"#
        );
        test_fmt!(
            r#"tcp.port in [80, 443]"#,
            r#"tcp.port in [
              80,
              443,
            ]"#
        );
        test_fmt!(
            r#"tcp.port in [80..443, 8000..8080]"#,
            r#"tcp.port in [
              80..443,
              8000..8080,
            ]"#
        );
        test_fmt!(
            r#"http.version in [1.0, 1.1]"#,
            r#"http.version in [
                  1.0,
                  1.1,
                ]"#
        );
        test_fmt!(
            r#"http.version in [1.0..1.1, 2.0..3.0]"#,
            r#"http.version in [
                  1.0..1.1,
                  2.0..3.0,
                ]"#
        );
    }

    #[test]
    fn test_fmt_has_any() {
        test_fmt!(
            r#"http.host has_any [".com", ".org"]"#,
            r#"http.host has_any [
                    ".com",
                    ".org",
                  ]"#
        );
        test_fmt!(
            r#"http.host has_any $has_any_var"#,
            r#"http.host has_any $has_any_var"#
        );
        test_fmt!(
            r#"http.host HAS_ANY [".com", ".org"]"#,
            r#"http.host HAS_ANY [
                    ".com",
                    ".org",
                  ]"#
        );
    }

    #[test]
    fn test_fmt_has_all() {
        test_fmt!(
            r#"http.host has_all ["exam", "ple"]"#,
            r#"http.host has_all [
                    "exam",
                    "ple",
                  ]"#
        );
        test_fmt!(
            r#"http.host has_all $has_all_var"#,
            r#"http.host has_all $has_all_var"#
        );
        test_fmt!(
            r#"http.host HAS_ALL ["exam", "ple"]"#,
            r#"http.host HAS_ALL [
                    "exam",
                    "ple",
                  ]"#
        );
    }

    #[test]
    fn test_fmt_case() {
        test_fmt!(
            r#"tcp.port cases {
                    80 => http.host == "example.com",
                    443 | 8000..8080 => http.host == "example.org",
                    _ => http.host == "example.net"
                }"#,
            r#"tcp.port cases {
          80 => http.host == "example.com",
          443
          | 8000..8080 => http.host == "example.org",
          _ => http.host == "example.net",
        }"#
        );

        test_fmt!(
            r#"http.host cases {
                    "example.com" => tcp.port == 80,
                    "example.org" | "example.net" => tcp.port == 443,
                    _ => tcp.port == 8000
                }"#,
            r#"http.host cases {
            "example.com" => tcp.port == 80,
            "example.org"
            | "example.net" => tcp.port == 443,
            _ => tcp.port == 8000,
          }"#
        );
    }

    #[test]
    fn test_fmt_ip_addr() {
        test_fmt!(r#"ip.addr == 127.0.0.1"#, r#"ip.addr == 127.0.0.1"#);
        test_fmt!(
            r#"ip.addr in [127.0.0.1, 127.0.0.2]"#,
            r#"ip.addr in [
              127.0.0.1,
              127.0.0.2,
            ]"#
        );
        test_fmt!(
            r#"ip.addr in [127.0.0.1..127.0.0.2, 127.0.0.0/24]"#,
            r#"ip.addr in [
              127.0.0.1..127.0.0.2,
              127.0.0.0/24,
            ]"#
        );
    }

    #[test]
    fn test_fmt_http_host() {
        test_fmt!(
            r#"http.host contains "example""#,
            r#"http.host contains "example""#
        );
        test_fmt!(
            r#"http.host CONTAINS "example""#,
            r#"http.host CONTAINS "example""#
        );
        test_fmt!(
            r#"http.host CONTAINS $bytes_var"#,
            r#"http.host CONTAINS $bytes_var"#
        );
        test_fmt!(
            r#"http.host matches "\.[a-z]{3}""#,
            r#"http.host matches "\.[a-z]{3}""#
        );
        test_fmt!(
            r#"http.host MATCHES "\.[a-z]{3}""#,
            r#"http.host MATCHES "\.[a-z]{3}""#
        );
        test_fmt!(r#"http.host ~ "\.[a-z]{3}""#, r#"http.host ~ "\.[a-z]{3}""#);
        test_fmt!(
            r#"http.host matches r"\.[a-z]{3}""#,
            r#"http.host matches r"\.[a-z]{3}""#
        );
        test_fmt!(
            r##"http.host matches r#"\.[a-z]{3}"#"##,
            r##"http.host matches r#"\.[a-z]{3}"#"##
        );
        test_fmt!(
            r##"http.user_agent MATCHES r#"\."[a-z]{3}""#"##,
            r##"http.user_agent MATCHES r#"\."[a-z]{3}""#"##
        );
        test_fmt!(
            r#"http.user_agent MATCHES "\.\"[a-z\"]{3}""#,
            r#"http.user_agent MATCHES "\.\"[a-z\"]{3}""#
        );
        test_fmt!(r#"http.host ~ "\.[a-z]{3}""#, r#"http.host ~ "\.[a-z]{3}""#);
    }

    #[test]
    fn test_fmt_http_host_and_content_type() {
        test_fmt!(
            r#"http.host == "example.com" && http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.com"
&& http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r#"http.host == "example.com" and http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.com"
and http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r#"http.host == "example.com" AND http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.com"
AND http.request.headers["content-type"][0] == "application/json""#
        );
    }

    #[test]
    fn test_fmt_http_host_or_content_type() {
        test_fmt!(
            r#"http.host == "example.com" || http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.com"
|| http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r#"http.host == "example.com" or http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.com"
or http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r#"http.host == "example.com" OR http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.com"
OR http.request.headers["content-type"][0] == "application/json""#
        );
    }

    #[test]
    fn test_fmt_http_host_xor_content_type() {
        test_fmt!(
            r#"http.host == "example.org" ^^ http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.org"
^^ http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r#"http.host == "example.org" xor http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.org"
xor http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r#"http.host == "example.org" XOR http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == "example.org"
XOR http.request.headers["content-type"][0] == "application/json""#
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_raw_string() {
        test_fmt!(
            r#"http.host == r"example.com" && http.request.headers["content-type"][0] == "application/json""#,
            r#"http.host == r"example.com"
&& http.request.headers["content-type"][0] == "application/json""#
        );
        test_fmt!(
            r##"http.host == r#"example.com"# && http.request.headers["content-type"][0] == "application/json""##,
            r##"http.host == r#"example.com"#
&& http.request.headers["content-type"][0] == "application/json""##
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_lower() {
        test_fmt!(
            r#"http.host == "example.com" && lower(http.request.headers["content-type"][0]) == "application/json""#,
            r#"http.host == "example.com"
&& lower(http.request.headers["content-type"][0]) == "application/json""#
        );
    }

    #[test]
    fn test_fmt_http_host_parentheses() {
        test_fmt!(
            r#"(http.host == "example.com")"#,
            r#"( http.host == "example.com" )"#
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_upper() {
        test_fmt!(
            r#"(http.host == "example.com" && upper(http.request.headers["content-type"][0]) == "APPLICATION/JSON")"#,
            r#"(
  http.host == "example.com"
  && upper(http.request.headers["content-type"][0]) == "APPLICATION/JSON"
)"#
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_len() {
        test_fmt!(
            r#"http.host == "example.com" && len(http.request.headers["content-type"][0]) == 16"#,
            r#"http.host == "example.com"
&& len(http.request.headers["content-type"][0]) == 16"#
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_echo() {
        test_fmt!(
            r#"(echo(http.request.headers["content-type"][0]) == "application/json" && (ssl || http.host == "example.com"))"#,
            r#"(
  echo(http.request.headers["content-type"][0]) == "application/json"
  && (
    ssl
    || http.host == "example.com"
  )
)"#
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_echo_parentheses() {
        test_fmt!(
            r#"((http.host == "example.com") && (echo(http.request.headers["content-type"][0]) == "application/json"))"#,
            r#"(
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0]) == "application/json" )
)"#
        );
    }

    #[test]
    fn test_fmt_http_host_and_content_type_echo_nested_parentheses() {
        test_fmt!(
            r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0]) == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0]) == "application/json" )
) )"#
        );
    }

    #[test]
    fn test_fmt_logical_expression_in_parentheses_with_map_index() {
        test_fmt!(
            r#"(((http.host == "example.com") && any(http.request.headers["content-type"][*] == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && any(http.request.headers["content-type"][*] == "application/json")
) )"#
        );

        test_fmt!(
            r#"(((http.host == "example.com") && any((http.request.headers["content-type"][*] == "application/json"))))"#,
            r#"( (
  ( http.host == "example.com" )
  && any(( http.request.headers["content-type"][*] == "application/json" ))
) )"#
        );
    }

    #[test]
    fn test_fmt_logical_expression_in_parentheses_with_function_returning_bytes() {
        test_fmt!(
            r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0], 100) == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100) == "application/json" )
) )"#
        );

        test_fmt!(
            r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,"teeeeeeest") == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, "teeeeeeest") == "application/json" )
) )"#
        );

        test_fmt!(
            r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,r"teeeeeeest") == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, r"teeeeeeest") == "application/json" )
) )"#
        );

        test_fmt!(
            r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,74:65:65:65:65:65:65:65:73:74) == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, 74:65:65:65:65:65:65:65:73:74) == "application/json" )
) )"#
        );

        test_fmt!(
            r#"(((http.host == "example.com") && (http.host has_all ["exam", "ple"]) && (echo(http.request.headers["content-type"][0],100   , 200,74:65:65:65:65:65:65:65:73:74) == "application/json")))"#,
            r#"( (
  ( http.host == "example.com" )
  && ( http.host has_all [
                            "exam",
                            "ple",
                          ] )
  && ( echo(http.request.headers["content-type"][0], 100, 200, 74:65:65:65:65:65:65:65:73:74) == "application/json" )
) )"#
        );
    }
}
