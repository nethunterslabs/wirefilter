import json
import os

from python_ast_builder import (
    ByteSeparatorBuilder,
    BytesBuilder,
    CasesBuilder,
    CasePatternValueBuilder,
    CombiningExprBuilder,
    ComparisonExprBuilder,
    ComparisonOpExprBuilder,
    ExplicitIpRangeBuilder,
    FieldBuilder,
    FieldIndexBuilder,
    FilterAstBuilder,
    FunctionBuilder,
    FunctionCallArgExprBuilder,
    FunctionCallExprBuilder,
    IndexExprBuilder,
    IntOpBuilder,
    IpCidrBuilder,
    IpRangeBuilder,
    LhsFieldExprBuilder,
    LogicalExprBuilder,
    LogicalOpBuilder,
    OrderingOpBuilder,
    RegexBuilder,
    RhsValueBuilder,
    RhsValuesBuilder,
    SimpleExprBuilder,
    SingleIndexExprBuilder,
    SingleValueExprAstBuilder,
    StrTypeBuilder,
    TypeBuilder,
    UnaryExprBuilder,
    UnaryOpBuilder,
    VariableBuilder,
)


if __name__ == "__main__":
    curret_dir = os.path.dirname(os.path.abspath(__file__))

    tests_dir = os.path.join(curret_dir, "../tests")

    for file in os.listdir(tests_dir):
        os.remove(os.path.join(tests_dir, file))

    def write_to_file(builder, filename):
        with open(os.path.join(tests_dir, f"{filename}.json"), "w") as f:
            json.dump(builder.to_json(), f)

    byte_separator_builder = ByteSeparatorBuilder.Colon
    write_to_file(byte_separator_builder, "byte_separator_builder")

    bytes_builder1 = BytesBuilder(Str=("value", StrTypeBuilder(Escaped=True)))
    write_to_file(bytes_builder1, "bytes_builder1")

    bytes_builder2 = BytesBuilder(Raw=([1, 2, 3], ByteSeparatorBuilder.Dot))
    write_to_file(bytes_builder2, "bytes_builder2")

    field_builder = FieldBuilder("http.version")
    write_to_file(field_builder, "field_builder")

    function_builder = FunctionBuilder("len")
    write_to_file(function_builder, "function_builder")

    variable_builder = VariableBuilder("bytes_var")
    write_to_file(variable_builder, "variable_builder")

    type_builder1 = TypeBuilder(Bool=True)
    write_to_file(type_builder1, "type_builder1")

    type_builder2 = TypeBuilder(Array=TypeBuilder(Bytes=True))
    write_to_file(type_builder2, "type_builder2")

    ordering_op_builder = OrderingOpBuilder.LessThan
    write_to_file(ordering_op_builder, "ordering_op_builder")

    regex_builder1 = RegexBuilder("^\\d{3}$", StrTypeBuilder(Escaped=True))
    write_to_file(regex_builder1, "regex_builder1")

    regex_builder2 = RegexBuilder("^\\d{3}$", StrTypeBuilder(Raw=3))
    write_to_file(regex_builder2, "regex_builder2")

    unary_op_builder = UnaryOpBuilder.Not
    write_to_file(unary_op_builder, "unary_op_builder")

    logical_op_builder = LogicalOpBuilder.And
    write_to_file(logical_op_builder, "logical_op_builder")

    int_op_builder = IntOpBuilder.BitwiseAnd
    write_to_file(int_op_builder, "int_op_builder")

    field_index_builder1 = FieldIndexBuilder(ArrayIndex=1)
    write_to_file(field_index_builder1, "field_index_builder1")

    field_index_builder2 = FieldIndexBuilder(MapKey="key")
    write_to_file(field_index_builder2, "field_index_builder2")

    field_index_builder3 = FieldIndexBuilder(MapEach=True)
    write_to_file(field_index_builder3, "field_index_builder3")

    ip_cidr_builder = IpCidrBuilder("127.0.0.0", 24)
    write_to_file(ip_cidr_builder, "ip_cidr_builder")

    explicit_ip_range_builder = ExplicitIpRangeBuilder(V4=("127.0.0.1", "127.0.0.255"))
    write_to_file(explicit_ip_range_builder, "explicit_ip_range_builder")

    ip_range_builder1 = IpRangeBuilder(Explicit=explicit_ip_range_builder)
    write_to_file(ip_range_builder1, "ip_range_builder1")

    ip_range_builder2 = IpRangeBuilder(Cidr=ip_cidr_builder)
    write_to_file(ip_range_builder2, "ip_range_builder2")

    rhs_value_builder1 = RhsValueBuilder(Int=1)
    write_to_file(rhs_value_builder1, "rhs_value_builder1")

    rhs_value_builder2 = RhsValueBuilder(Bytes=bytes_builder1)
    write_to_file(rhs_value_builder2, "rhs_value_builder2")

    rhs_value_builder3 = RhsValueBuilder(Float=1.0)
    write_to_file(rhs_value_builder3, "rhs_value_builder3")

    rhs_value_builder4 = RhsValueBuilder(Ip="127.0.0.1")
    write_to_file(rhs_value_builder4, "rhs_value_builder4")

    rhs_values_builder1 = RhsValuesBuilder(Int=[(1, 2), (3, 4)])
    write_to_file(rhs_values_builder1, "rhs_values_builder1")

    rhs_values_builder2 = RhsValuesBuilder(Float=[(1.0, 10.0)])
    write_to_file(rhs_values_builder2, "rhs_values_builder2")

    rhs_values_builder3 = RhsValuesBuilder(Ip=[IpRangeBuilder(Cidr=ip_cidr_builder)])
    write_to_file(rhs_values_builder3, "rhs_values_builder3")

    rhs_values_builder4 = RhsValuesBuilder(Bytes=[bytes_builder1])
    write_to_file(rhs_values_builder4, "rhs_values_builder4")

    case_pattern_value_builder1 = CasePatternValueBuilder(Bool=True)
    write_to_file(case_pattern_value_builder1, "case_pattern_value_builder1")

    case_pattern_value_builder2 = CasePatternValueBuilder(Int=1)
    write_to_file(case_pattern_value_builder2, "case_pattern_value_builder2")

    case_pattern_value_builder3 = CasePatternValueBuilder(IntRange=(1, 2))
    write_to_file(case_pattern_value_builder3, "case_pattern_value_builder3")

    case_pattern_value_builder4 = CasePatternValueBuilder(Float=1.0)
    write_to_file(case_pattern_value_builder4, "case_pattern_value_builder4")

    case_pattern_value_builder5 = CasePatternValueBuilder(FloatRange=(1.0, 2.0))
    write_to_file(case_pattern_value_builder5, "case_pattern_value_builder5")

    case_pattern_value_builder6 = CasePatternValueBuilder(Ip="127.0.0.1")
    write_to_file(case_pattern_value_builder6, "case_pattern_value_builder6")

    case_pattern_value_builder7 = CasePatternValueBuilder(IpRange=ip_range_builder1)
    write_to_file(case_pattern_value_builder7, "case_pattern_value_builder7")

    case_pattern_value_builder8 = CasePatternValueBuilder(IpRange=ip_range_builder2)
    write_to_file(case_pattern_value_builder8, "case_pattern_value_builder8")

    case_pattern_value_builder9 = CasePatternValueBuilder(Bytes=bytes_builder1)
    write_to_file(case_pattern_value_builder9, "case_pattern_value_builder9")

    comparison_op_expr_builder1 = ComparisonOpExprBuilder(IsTrue=True)
    write_to_file(comparison_op_expr_builder1, "comparison_op_expr_builder1")

    comparison_op_expr_builder2 = ComparisonOpExprBuilder(
        Ordering=(ordering_op_builder, rhs_value_builder1)
    )
    write_to_file(comparison_op_expr_builder2, "comparison_op_expr_builder2")

    comparison_op_expr_builder3 = ComparisonOpExprBuilder(Int=(int_op_builder, 1))
    write_to_file(comparison_op_expr_builder3, "comparison_op_expr_builder3")

    comparison_op_expr_builder4 = ComparisonOpExprBuilder(Contains=(bytes_builder1))
    write_to_file(comparison_op_expr_builder4, "comparison_op_expr_builder4")

    comparison_op_expr_builder5 = ComparisonOpExprBuilder(Matches=(regex_builder1))
    write_to_file(comparison_op_expr_builder5, "comparison_op_expr_builder5")

    comparison_op_expr_builder6 = ComparisonOpExprBuilder(OneOf=(rhs_values_builder1))
    write_to_file(comparison_op_expr_builder6, "comparison_op_expr_builder6")

    comparison_op_expr_builder7 = ComparisonOpExprBuilder(HasAny=(rhs_values_builder4))
    write_to_file(comparison_op_expr_builder7, "comparison_op_expr_builder7")

    comparison_op_expr_builder8 = ComparisonOpExprBuilder(HasAll=(rhs_values_builder4))
    write_to_file(comparison_op_expr_builder8, "comparison_op_expr_builder8")

    comparison_op_expr_builder9 = ComparisonOpExprBuilder(
        OrderingVariable=(ordering_op_builder, VariableBuilder("int_var"))
    )
    write_to_file(comparison_op_expr_builder9, "comparison_op_expr_builder9")

    comparison_op_expr_builder10 = ComparisonOpExprBuilder(
        IntVariable=(int_op_builder, VariableBuilder("int_var"))
    )
    write_to_file(comparison_op_expr_builder10, "comparison_op_expr_builder10")

    comparison_op_expr_builder11 = ComparisonOpExprBuilder(
        ContainsVariable=(VariableBuilder("bytes_var"))
    )
    write_to_file(comparison_op_expr_builder11, "comparison_op_expr_builder11")

    comparison_op_expr_builder12 = ComparisonOpExprBuilder(
        MatchesVariable=(VariableBuilder("regex_var"))
    )
    write_to_file(comparison_op_expr_builder12, "comparison_op_expr_builder12")

    comparison_op_expr_builder13 = ComparisonOpExprBuilder(
        OneOfVariable=(VariableBuilder("in_var"))
    )
    write_to_file(comparison_op_expr_builder13, "comparison_op_expr_builder13")

    comparison_op_expr_builder14 = ComparisonOpExprBuilder(
        HasAnyVariable=(VariableBuilder("has_any_var"))
    )
    write_to_file(comparison_op_expr_builder14, "comparison_op_expr_builder14")

    comparison_op_expr_builder15 = ComparisonOpExprBuilder(
        HasAllVariable=(VariableBuilder("has_all_var"))
    )
    write_to_file(comparison_op_expr_builder15, "comparison_op_expr_builder15")

    comparison_op_expr_builder16 = ComparisonOpExprBuilder(
        Cases=CasesBuilder(
            patterns=[
                (
                    [
                        case_pattern_value_builder4,
                        case_pattern_value_builder1,
                    ],
                    LogicalExprBuilder(
                        Simple=SimpleExprBuilder(
                            Comparison=ComparisonExprBuilder(
                                IndexExprBuilder(
                                    LhsFieldExprBuilder(Field=field_builder), []
                                ),
                                ComparisonOpExprBuilder(
                                    Ordering=(ordering_op_builder, rhs_value_builder3)
                                ),
                            )
                        )
                    ),
                )
            ]
        )
    )
    write_to_file(comparison_op_expr_builder16, "comparison_op_expr_builder16")

    unary_expr_builder = UnaryExprBuilder(
        unary_op_builder,
        SimpleExprBuilder(
            Comparison=ComparisonExprBuilder(
                IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
                comparison_op_expr_builder2,
            )
        ),
    )
    write_to_file(unary_expr_builder, "unary_expr_builder")

    index_expr_builder1 = IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), [])
    write_to_file(index_expr_builder1, "index_expr_builder1")

    index_expr_builder2 = IndexExprBuilder(
        LhsFieldExprBuilder(Field=FieldBuilder("http.request.headers")),
        [
            FieldIndexBuilder(ArrayIndex=1),
            FieldIndexBuilder(MapKey="key"),
        ],
    )
    write_to_file(index_expr_builder2, "index_expr_builder2")

    function_call_arg_expr_builder1 = FunctionCallArgExprBuilder(
        IndexExpr=IndexExprBuilder(
            LhsFieldExprBuilder(Field=FieldBuilder("http.host")), []
        )
    )
    write_to_file(function_call_arg_expr_builder1, "function_call_arg_expr_builder1")

    function_call_arg_expr_builder2 = FunctionCallArgExprBuilder(
        Literal=rhs_value_builder1
    )
    write_to_file(function_call_arg_expr_builder2, "function_call_arg_expr_builder2")

    function_call_arg_expr_builder3 = FunctionCallArgExprBuilder(
        Literal=RhsValueBuilder(
            Bytes=BytesBuilder(Str=("value", StrTypeBuilder(Escaped=True)))
        )
    )
    write_to_file(function_call_arg_expr_builder3, "function_call_arg_expr_builder3")

    function_call_arg_expr_builder4 = FunctionCallArgExprBuilder(
        Literal=RhsValueBuilder(Float=1.0)
    )
    write_to_file(function_call_arg_expr_builder4, "function_call_arg_expr_builder4")

    function_call_arg_expr_builder5 = FunctionCallArgExprBuilder(
        Literal=RhsValueBuilder(Ip="127.0.0.1")
    )
    write_to_file(function_call_arg_expr_builder5, "function_call_arg_expr_builder5")

    function_call_arg_expr_builder6 = FunctionCallArgExprBuilder(
        SimpleExpr=SimpleExprBuilder(
            Comparison=ComparisonExprBuilder(
                IndexExprBuilder(
                    LhsFieldExprBuilder(Field=FieldBuilder("http.host")), []
                ),
                comparison_op_expr_builder2,
            )
        )
    )
    write_to_file(function_call_arg_expr_builder6, "function_call_arg_expr_builder6")

    function_call_expr_builder = FunctionCallExprBuilder(
        function_builder,
        TypeBuilder(Int=True),
        [function_call_arg_expr_builder1],
    )
    write_to_file(function_call_expr_builder, "function_call_expr_builder")

    comparison_expr_builder1 = ComparisonExprBuilder(
        IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
        comparison_op_expr_builder2,
    )
    write_to_file(comparison_expr_builder1, "comparison_expr_builder1")

    comparison_expr_builder2 = ComparisonExprBuilder(
        IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
        comparison_op_expr_builder1,
    )
    write_to_file(comparison_expr_builder2, "comparison_expr_builder2")

    comparison_expr_builder3 = ComparisonExprBuilder(
        IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
        ComparisonOpExprBuilder(Int=(IntOpBuilder.BitwiseAnd, 1)),
    )
    write_to_file(comparison_expr_builder3, "comparison_expr_builder3")

    comparison_expr_builder4 = ComparisonExprBuilder(
        IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
        ComparisonOpExprBuilder(Contains=bytes_builder1),
    )
    write_to_file(comparison_expr_builder4, "comparison_expr_builder4")

    comparison_expr_builder5 = ComparisonExprBuilder(
        IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
        ComparisonOpExprBuilder(Matches=regex_builder1),
    )
    write_to_file(comparison_expr_builder5, "comparison_expr_builder5")

    simple_expr_builder1 = SimpleExprBuilder(
        Comparison=ComparisonExprBuilder(
            IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
            comparison_op_expr_builder2,
        )
    )
    write_to_file(simple_expr_builder1, "simple_expr_builder1")

    simple_expr_builder2 = SimpleExprBuilder(
        Unary=UnaryExprBuilder(
            UnaryOpBuilder.Not,
            SimpleExprBuilder(
                Comparison=ComparisonExprBuilder(
                    IndexExprBuilder(LhsFieldExprBuilder(Field=field_builder), []),
                    comparison_op_expr_builder2,
                )
            ),
        )
    )
    write_to_file(simple_expr_builder2, "simple_expr_builder2")

    str_type_builder1 = StrTypeBuilder(Escaped=True)
    write_to_file(str_type_builder1, "str_type_builder1")

    str_type_builder2 = StrTypeBuilder(Raw=3)
    write_to_file(str_type_builder2, "str_type_builder2")

    lhs_field_expr_builder1 = LhsFieldExprBuilder(Field=field_builder)
    write_to_file(lhs_field_expr_builder1, "lhs_field_expr_builder1")

    lhs_field_expr_builder2 = LhsFieldExprBuilder(
        FunctionCallExpr=function_call_expr_builder
    )
    write_to_file(lhs_field_expr_builder2, "lhs_field_expr_builder2")

    logical_expr_builder1 = LogicalExprBuilder(
        Simple=SimpleExprBuilder(
            Comparison=ComparisonExprBuilder(
                IndexExprBuilder(lhs_field_expr_builder1, []),
                comparison_op_expr_builder2,
            )
        )
    )
    write_to_file(logical_expr_builder1, "logical_expr_builder1")

    logical_expr_builder2 = LogicalExprBuilder(
        Simple=SimpleExprBuilder(
            Unary=UnaryExprBuilder(
                UnaryOpBuilder.Not,
                SimpleExprBuilder(
                    Comparison=ComparisonExprBuilder(
                        IndexExprBuilder(lhs_field_expr_builder1, []),
                        comparison_op_expr_builder2,
                    )
                ),
            )
        )
    )
    write_to_file(logical_expr_builder2, "logical_expr_builder2")

    logical_expr_builder3 = LogicalExprBuilder(
        Combining=CombiningExprBuilder(
            op=logical_op_builder,
            items=[
                LogicalExprBuilder(
                    Simple=SimpleExprBuilder(
                        Comparison=ComparisonExprBuilder(
                            IndexExprBuilder(lhs_field_expr_builder1, []),
                            comparison_op_expr_builder2,
                        )
                    )
                ),
                LogicalExprBuilder(
                    Simple=SimpleExprBuilder(
                        Comparison=ComparisonExprBuilder(
                            IndexExprBuilder(lhs_field_expr_builder1, []),
                            comparison_op_expr_builder2,
                        )
                    )
                ),
            ],
        )
    )
    write_to_file(logical_expr_builder3, "logical_expr_builder3")

    combining_expr_builder = CombiningExprBuilder(
        op=logical_op_builder,
        items=[
            LogicalExprBuilder(
                Simple=SimpleExprBuilder(
                    Comparison=ComparisonExprBuilder(
                        IndexExprBuilder(lhs_field_expr_builder1, []),
                        comparison_op_expr_builder2,
                    )
                )
            ),
            LogicalExprBuilder(
                Simple=SimpleExprBuilder(
                    Comparison=ComparisonExprBuilder(
                        IndexExprBuilder(lhs_field_expr_builder1, []),
                        comparison_op_expr_builder2,
                    )
                )
            ),
        ],
    )
    write_to_file(combining_expr_builder, "combining_expr_builder")

    filter_ast_builder = FilterAstBuilder(op=logical_expr_builder1)
    write_to_file(filter_ast_builder, "filter_ast_builder")

    single_value_expr_ast_builder1 = SingleValueExprAstBuilder(
        op=SingleIndexExprBuilder(
            op=IndexExprBuilder(
                lhs=LhsFieldExprBuilder(Field=field_builder), indexes=[]
            ),
            cases=CasesBuilder(
                patterns=[
                    (
                        [
                            case_pattern_value_builder4,
                            case_pattern_value_builder1,
                        ],
                        IndexExprBuilder(
                            LhsFieldExprBuilder(Field=FieldBuilder("ssl.version")),
                            [],
                        ),
                    )
                ]
            ),
        )
    )
    write_to_file(single_value_expr_ast_builder1, "single_value_expr_ast_builder1")

    single_value_expr_ast_builder2 = SingleValueExprAstBuilder(
        op=SingleIndexExprBuilder(
            op=IndexExprBuilder(
                lhs=LhsFieldExprBuilder(
                    FunctionCallExpr=FunctionCallExprBuilder(
                        function_builder,
                        TypeBuilder(Int=True),
                        [
                            FunctionCallArgExprBuilder(
                                IndexExpr=IndexExprBuilder(
                                    LhsFieldExprBuilder(
                                        Field=FieldBuilder("http.host")
                                    ),
                                    [],
                                )
                            )
                        ],
                    )
                ),
                indexes=[],
            ),
            cases=None,
        )
    )
    write_to_file(single_value_expr_ast_builder2, "single_value_expr_ast_builder2")
