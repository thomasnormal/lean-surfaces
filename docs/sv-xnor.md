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

## 2026-10-30: the symbolic tier lowers it (WP-L2)

The M0 / self-check tier above is unchanged and still loud. The symbolic (sv-0.2) tier, which svGolf
proves in, now accepts the binary operator in SIGNAL expressions: the extractor lowers `a ~^ b` and
`a ^~ b` (one slang operator) to `~(a ^ b)`, built from the two nodes that tier already has
(`_convert_xnor_expr`, `extractors/sv/extract.py`). It is exact because slang has already converted
both operands to the expression's own type: the inner `^` and the outer `~` have the xnor's context
width and signedness, any x/z operand bit gives x (`x ^ y = x`, `~x = x`) and equal known bits give 1
(Table 11-14), and the extension bits of a wider context are `0 ~^ 0 = 1`. Not lowered, and still the
loud `BinaryExpression:BinaryXnor`: a parameter default, a localparam, a generate condition (the
constant tier has its own width rules for `~`). A signed operand pair assigned to a wider target stays
the tier's `ConversionExpression:width`, as for `^`. The reduction form `~^a` was already admitted.
Evidence: `harness/sv/cases2.json` rows `xnor_*` (Icarus 12.0 and pinned Xcelium 24.03-s004),
`extractors/sv/test_xnor_lowering.py`, `Examples/system-verilog/xnor_n/proof.lean` (the value for every
width). Register entry `ex-xnor`.

