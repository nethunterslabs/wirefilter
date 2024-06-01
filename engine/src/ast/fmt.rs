use crate::{
    ast::{field_expr::IntOp, simple_expr::UnaryOp, LhsFieldExpr},
    rhs_types::{Bytes, ExplicitIpRange, FloatRange, IntRange, IpRange, StrType},
    ComparisonExpr, ComparisonOpExpr, FieldIndex, FilterAst, FunctionCallArgExpr, FunctionCallExpr,
    IndexExpr, LogicalExpr, LogicalOp, OrderingOp, RhsValue, RhsValues, SimpleExpr,
    SingleValueExprAst,
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

impl Fmt for RhsValue {
    fn fmt(&self, _indent: usize, output: &mut String) {
        match self {
            RhsValue::Ip(ip) => output.push_str(&ip.to_string()),
            RhsValue::Bytes(bytes) => bytes.fmt(0, output),
            RhsValue::Int(num) => output.push_str(&num.to_string()),
            RhsValue::Float(float_num) => output.push_str(&format!("{:?}", float_num.into_inner())),
            RhsValue::Bool(_) => unreachable!(),
            RhsValue::Array(_) => unreachable!(),
            RhsValue::Map(_) => unreachable!(),
        }
    }
}

impl Fmt for RhsValues {
    fn fmt(&self, _indent: usize, output: &mut String) {
        output.push('{');
        match self {
            RhsValues::Ip(ips) => {
                for (i, ip) in ips.iter().enumerate() {
                    if i > 0 {
                        output.push(' ');
                    }
                    ip.fmt(0, output);
                }
            }
            RhsValues::Bytes(bytes) => {
                for (i, byte) in bytes.iter().enumerate() {
                    if i > 0 {
                        output.push(' ');
                    }
                    byte.fmt(0, output);
                }
            }
            RhsValues::Int(ints) => {
                for (i, int) in ints.iter().enumerate() {
                    if i > 0 {
                        output.push(' ');
                    }
                    int.fmt(0, output);
                }
            }
            RhsValues::Float(floats) => {
                for (i, float) in floats.iter().enumerate() {
                    if i > 0 {
                        output.push(' ');
                    }
                    float.fmt(0, output);
                }
            }
            RhsValues::Bool(_) => unreachable!(),
            RhsValues::Array(_) => unreachable!(),
            RhsValues::Map(_) => unreachable!(),
        }
        output.push('}');
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

impl<'s> Fmt for ComparisonExpr<'s> {
    fn fmt(&self, _indent: usize, output: &mut String) {
        self.lhs.fmt(0, output);

        match &self.op {
            ComparisonOpExpr::IsTrue => {}
            ComparisonOpExpr::Ordering { op, rhs } => {
                match op {
                    OrderingOp::Equal(variant) => {
                        if *variant == 0 {
                            output.push_str(" eq ");
                        } else {
                            output.push_str(" == ");
                        }
                    }
                    OrderingOp::NotEqual(variant) => {
                        if *variant == 0 {
                            output.push_str(" ne ");
                        } else {
                            output.push_str(" != ");
                        }
                    }
                    OrderingOp::GreaterThanEqual(variant) => {
                        if *variant == 0 {
                            output.push_str(" ge ");
                        } else {
                            output.push_str(" >= ");
                        }
                    }
                    OrderingOp::LessThanEqual(variant) => {
                        if *variant == 0 {
                            output.push_str(" le ");
                        } else {
                            output.push_str(" <= ");
                        }
                    }
                    OrderingOp::GreaterThan(variant) => {
                        if *variant == 0 {
                            output.push_str(" gt ");
                        } else {
                            output.push_str(" > ");
                        }
                    }
                    OrderingOp::LessThan(variant) => {
                        if *variant == 0 {
                            output.push_str(" lt ");
                        } else {
                            output.push_str(" < ");
                        }
                    }
                }

                rhs.fmt(0, output);
            }
            ComparisonOpExpr::Int { op, rhs } => match op {
                IntOp::BitwiseAnd(variant) => {
                    if *variant == 0 {
                        output.push_str(" & ");
                    } else {
                        output.push_str(" bitwise_and ");
                    }
                    output.push_str(&rhs.to_string());
                }
            },
            ComparisonOpExpr::Contains(bytes) => {
                output.push_str(" contains ");
                bytes.fmt(0, output);
            }
            ComparisonOpExpr::Matches((regex, variant)) => {
                if *variant == 0 {
                    output.push_str(" ~ ");
                } else {
                    output.push_str(" matches ");
                }
                output.push('"');
                output.push_str(&escape(regex.as_str(), false));
                output.push('"');
            }
            ComparisonOpExpr::OneOf(values) => {
                output.push_str(" in ");
                values.fmt(0, output);
            }
            ComparisonOpExpr::HasAny(values) => {
                output.push_str(" has_any ");
                values.fmt(0, output);
            }
            ComparisonOpExpr::HasAll(values) => {
                output.push_str(" has_all ");
                values.fmt(0, output);
            }
            ComparisonOpExpr::InList { name, list: _ } => {
                output.push_str(" in $");
                output.push_str(name.as_str());
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
                            LogicalOp::And(variant) => {
                                if *variant == 0 {
                                    output.push_str("and ")
                                } else {
                                    output.push_str("&& ")
                                }
                            }
                            LogicalOp::Or(variant) => {
                                if *variant == 0 {
                                    output.push_str("or ")
                                } else {
                                    output.push_str("|| ")
                                }
                            }
                            LogicalOp::Xor(variant) => {
                                if *variant == 0 {
                                    output.push_str("xor ")
                                } else {
                                    output.push_str("^^ ")
                                }
                            }
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
                    output.push_str("(\n");
                    output.push_str(&" ".repeat(indent + 2));
                    node.fmt(indent + 2, output);
                    output.push('\n');
                    output.push_str(&" ".repeat(indent));
                    output.push(')');
                } else {
                    output.push_str("( ");
                    node.fmt(indent, output);
                    output.push_str(" )");
                }
            }
            SimpleExpr::Unary { op, arg } => match op {
                UnaryOp::Not(_) => {
                    output.push('!');
                    arg.fmt(indent, output);
                }
            },
        }
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
                        output.push_str(&separator.as_char().to_string());
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

impl<'s> SingleValueExprAst<'s> {
    /// Format a [`SingleValueExprAst`] in an opinionated way.
    pub fn fmt(&self) -> Result<String, FormatError> {
        self.fmt_with_indent(0)
    }

    /// Format a [`SingleValueExprAst`] in an opinionated way with an indent.
    pub fn fmt_with_indent(&self, indent: usize) -> Result<String, FormatError> {
        let mut formatted = String::new();
        self.op.fmt(indent, &mut formatted);

        let formatted_ast = self
            .scheme
            .parse_single_value_expr(&formatted)
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
    pub fn fmt(&self) -> Result<String, FormatError> {
        self.fmt_with_indent(0)
    }

    /// Format a [`FilterAst`] in an opinionated way with an indent.
    pub fn fmt_with_indent(&self, indent: usize) -> Result<String, FormatError> {
        let mut formatted = String::new();
        self.op.fmt(indent, &mut formatted);

        let formatted_ast = self
            .scheme
            .parse(&formatted)
            .map_err(|e| FormatError::ParseError(e.to_string()))?;
        if self == &formatted_ast {
            Ok(formatted.trim().to_owned())
        } else {
            Err(FormatError::MismatchedAst)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Array, FunctionArgKind, FunctionArgs, GetType, LhsValue, Scheme, SimpleFunctionDefinition,
        SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam, State, Type,
    };
    use std::convert::TryFrom;

    #[test]
    fn test_fmt() {
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
                Ok(LhsValue::Bytes(bytes)) => {
                    Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap()))
                }
                Err(Type::Bytes) => None,
                _ => unreachable!(),
            }
        }

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
        scheme
            .add_function(
                "any".into(),
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
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
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(vec![
                        SimpleFunctionOptParam {
                            arg_kind: FunctionArgKind::Literal,
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
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: Some(vec![]),
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(len_function),
                },
            )
            .unwrap();

        let ast = scheme
            .parse(r#" http.host  ==   "example.com"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#" http.host  eq   "example.com"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host eq "example.com""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#" http.host  !=   "example.com"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host != "example.com""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#" http.host  ne   "example.com"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host ne "example.com""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"http.host == "example\".com""#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example\".com""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == 65:78:61:6d:70:6c:65:2e:63:6f:6d"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == 65:78:61:6D:70:6C:65:2E:63:6F:6D"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == 65.78.61.6d.70.6c.65.2e.63.6f.6d"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == 65.78.61.6D.70.6C.65.2E.63.6F.6D"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == 65-78-61-6d-70-6c-65-2e-63-6f-6d"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == 65-78-61-6D-70-6C-65-2E-63-6F-6D"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         ==  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port == 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         bitwise_and  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port bitwise_and 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         &  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port & 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         >  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port > 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         gt  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port gt 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         >=  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port >= 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         ge  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port ge 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         <  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port < 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         lt  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port lt 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         <=  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port <= 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"tcp.port         le  80"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port le 80"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host   in    {    "example.com"     "example.org" }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host in {"example.com" "example.org"}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host   has_any    {    ".com"     ".org" }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host has_any {".com" ".org"}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host   has_any    {    "exam"     "ample" }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host has_any {"exam" "ample"}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"tcp.port   in    {    80     443 }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port in {80 443}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"tcp.port   in    {    80..443           8000..8080 }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"tcp.port in {80..443 8000..8080}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"http.version         ==  1.1"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.version == 1.1"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.version   in    {    1.0     1.1 }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.version in {1.0 1.1}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.version   in    {    1.0..1.1      2.0..3.0 }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.version in {1.0..1.1 2.0..3.0}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#"ip.addr         ==  127.0.0.1"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"ip.addr == 127.0.0.1"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"ip.addr   in    {    127.0.0.1     127.0.0.2 }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"ip.addr in {127.0.0.1 127.0.0.2}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"ip.addr   in    {    127.0.0.1..127.0.0.2     127.0.0.0/24 }"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"ip.addr in {127.0.0.1..127.0.0.2 127.0.0.0/24}"#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#" http.host  contains   "example"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host contains "example""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#" http.host  matches   "\.[a-z]{3}"    "#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host matches "\.[a-z]{3}""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme.parse(r#" http.host  ~   "\.[a-z]{3}"    "#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host ~ "\.[a-z]{3}""#.to_string()),
            "Unable to format single field expression"
        );

        let ast = scheme
            .parse(r#"http.host == "example.com" && http.request.headers["content-type"][0] == "application/json""#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com"
&& http.request.headers["content-type"][0] == "application/json""#
                .to_string()),
            "Unable to format logical expression"
        );

        let ast = scheme
            .parse(r#"http.host == r"example.com" && http.request.headers["content-type"][0] == "application/json""#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == r"example.com"
&& http.request.headers["content-type"][0] == "application/json""#
                .to_string()),
            "Unable to format logical expression with raw string"
        );

        let ast = scheme
            .parse(r##"http.host == r#"example.com"# && http.request.headers["content-type"][0] == "application/json""##)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r##"http.host == r#"example.com"#
&& http.request.headers["content-type"][0] == "application/json""##
                .to_string()),
            "Unable to format logical expression with raw string"
        );

        let ast = scheme
            .parse(r#"http.host == "example.com" && lower(http.request.headers["content-type"][0]) == "application/json""#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com"
&& lower(http.request.headers["content-type"][0]) == "application/json""#
                .to_string()),
            "Unable to format logical expression with function"
        );

        let ast = scheme.parse(r#"(http.host == "example.com")"#).unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( http.host == "example.com" )"#.to_string()),
            "Unable to format logical expression in parentheses with function"
        );

        let ast = scheme
            .parse(r#"(http.host == "example.com" && upper(http.request.headers["content-type"][0]) == "APPLICATION/JSON")"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"(
  http.host == "example.com"
  && upper(http.request.headers["content-type"][0]) == "APPLICATION/JSON"
)"#
            .to_string()),
            "Unable to format logical expression in parentheses with function"
        );

        let ast = scheme
            .parse(r#"http.host == "example.com" && len(http.request.headers["content-type"][0]) == 16"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"http.host == "example.com"
&& len(http.request.headers["content-type"][0]) == 16"#
                .to_string()),
            "Unable to format logical expression with function returning int"
        );

        let ast = scheme
            .parse(r#"(echo(http.request.headers["content-type"][0]) == "application/json" && (ssl || http.host == "example.com"))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"(
  echo(http.request.headers["content-type"][0]) == "application/json"
  && (
    ssl
    || http.host == "example.com"
  )
)"#
            .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"((http.host == "example.com") && (echo(http.request.headers["content-type"][0]) == "application/json"))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"(
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0]) == "application/json" )
)"#
            .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0]) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0]) == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && any(http.request.headers["content-type"][*] == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && any(http.request.headers["content-type"][*] == "application/json")
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with map index"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && any((http.request.headers["content-type"][*] == "application/json"))))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && any(( http.request.headers["content-type"][*] == "application/json" ))
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with map index"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0], 100) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100) == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,"teeeeeeest"    ) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, "teeeeeeest") == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,r"teeeeeeest"    ) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, r"teeeeeeest") == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );

        let ast = scheme
            .parse(r#"(((http.host == "example.com") && (echo(http.request.headers["content-type"][0],100   , 200,74:65:65:65:65:65:65:65:73:74    ) == "application/json")))"#)
            .unwrap();
        assert_eq!(
            ast.fmt(),
            Ok(r#"( (
  ( http.host == "example.com" )
  && ( echo(http.request.headers["content-type"][0], 100, 200, 74:65:65:65:65:65:65:65:73:74) == "application/json" )
) )"#
                .to_string()),
            "Unable to format logical expression in parentheses with function returning bytes"
        );
    }
}
