# Explicit conversion boundary — retained cast semantics

`ConversionExpression:Explicit` marks an explicit SystemVerilog cast whose
source or target semantics are outside the admitted scalar expression tier.
The boundary covers real-to-integral conversions and a typed assignment
pattern nested inside a cast. The cast is retained as an unsupported node;
its operand is not silently rounded, truncated, flattened or discarded.

## Why explicit casts remain loud

IEEE 1800-2023 §§6.12.1, 10.9.7 and 11.8.3 make a cast type-directed. A
real-to-integral conversion rounds according to the language rule, including
the exact-half behavior, while a typed assignment pattern first determines
the destination aggregate width and shape. The legacy expression value has no
real representation, general cast operator or aggregate assignment-pattern
layout. Replacing either form with an integer literal or an untyped pattern
would fabricate a result and could change the surrounding assignment.

No second evaluator is introduced. Existing admitted integral expressions and
ordinary assignments retain their current behavior; only the unsupported cast
boundary stays explicit until a representation and differential contract for
each source/target family exists.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ConversionExpression:Explicit` in **37**
files: **7** are sole refusals and 30 co-occur. Re-elaborating those sole
files with the read-only repricer finds **22** cast spans:

| source shape | spans | files |
|---|---:|---:|
| real-to-integral rounding | 21 | 6 |
| typed assignment pattern | 1 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/explicit_cast_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument re-elaborates source in memory and writes no output beside the
read-only corpus. Its shape counts are telemetry, not a cast evaluator.
