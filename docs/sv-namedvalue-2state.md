# Residual two-state named-value boundary — retained fixed-array identity

`NamedValueExpression:2state` marks a named value whose fixed unpacked-array
identity is required by an array concatenation, pattern, literal context or
`foreach` traversal. The existing two-state scalar conversion does not cover
these aggregate uses.

## Why these named values remain loud

IEEE 1800-2023 §§5.11, 10.9.1, 10.10.1 and 12.7.3 require array element
context, subarray concatenation, indexed pattern conversion and declared-range
iteration. The public named-value path has no complete unpacked aggregate store
or range-aware aggregate resolver. Treating an array name as a scalar value
would lose subarray expansion, element casts or descending indices. No second
array evaluator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NamedValueExpression:2state` in **1,482**
files: **5** are sole refusals and 1,477 co-occur. Re-elaborating the sole
files finds **5** named-value spans: two unpacked concatenation cases, one
indexed array pattern, one descending fixed-array `foreach` and one array
literal context. Reproduce with:

```text
python3.9 extractors/sv/namedvalue_2state_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports aggregate source shapes only and does not allocate an
array store or evaluate a pattern.
