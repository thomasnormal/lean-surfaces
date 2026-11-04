# Residual two-state named-value boundary — retained fixed-array identity

`NamedValueExpression:2state` marks a named value whose fixed unpacked-array
identity is required by an array concatenation, pattern, literal context,
`foreach` traversal, or a value context without a flat representation. The
existing two-state scalar conversion does not cover these aggregate uses. A
direct one-dimensional fixed integral array in a `%p` diagnostic is the one
narrow exception: its declared cells are rendered in order through the
existing flat state.

## Why the remaining named values stay loud

IEEE 1800-2023 §§5.11, 10.9.1, 10.10.1 and 12.7.3 require array element
context, subarray concatenation, indexed pattern conversion and declared-range
iteration. The public named-value path has no complete unpacked aggregate store
or range-aware aggregate resolver. Treating an array name as a scalar value
would lose subarray expansion, element casts or descending indices. `%p` is
limited to the existing one-dimensional integral cells; no second array
evaluator or aggregate store is introduced.

## 2026-10-27 census and decision

The fresh 22,065-path census records `NamedValueExpression:2state` in **1,462**
files after the `%p` slice; the item removes eleven named-value spans from the
residual set. Reproduce the source-shape repricing with:

```text
python3.9 extractors/sv/namedvalue_2state_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports aggregate source shapes only and does not allocate an
array store or evaluate a pattern. The `%p` exception reads only the already
flattened one-dimensional cells.
