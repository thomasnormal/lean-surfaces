# Bitwise XNOR boundary — retained four-state operator semantics

`BinaryExpression:BinaryXnor` marks the two SystemVerilog spellings `~^` and
`^~` of bitwise XNOR. The operator remains explicit in this tier, including
constant one-bit truth-table expressions and vector operands.

## Why XNOR remains loud

IEEE 1800-2023 §11.4.8 defines XNOR bit by bit over four-state values; `x` and
`z` propagation follows Table 11-14, and `~^` and `^~` are equivalent spellings.
The legacy binary evaluator has no XNOR arm or four-state complement rule.
Replacing XNOR with a guessed XOR complement could mishandle unknown bits,
width extension and signedness. No operator alias or second evaluator is
introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `BinaryExpression:BinaryXnor` in **7**
files: **5** are sole refusals and 2 co-occur. Re-elaborating the sole files
with the read-only repricer finds **10** XNOR spans:

| source shape | spans | files |
|---|---:|---:|
| `~^` spelling | 7 | 5 |
| `^~` spelling | 3 | 3 |
| variable operands | 6 | 4 |
| literal operands | 4 | 1 |

The labels overlap. Reproduce the table with:

```text
python3.9 extractors/sv/xnor_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reports syntax only. It does not evaluate truth tables or
collapse four-state values to booleans.
