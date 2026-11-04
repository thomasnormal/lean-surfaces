# User-defined primitives — retained boundary

IEEE 1800-2023 clause 29 defines user-defined primitives (UDPs) through
scalar input/output ports and an ordered combinational or sequential truth
table. Sequential UDPs add current-state fields, transition symbols and an
initial output value. Table rows have required field counts, wildcard and
transition constraints, and diagnostics for conflicting or illegal entries.

The existing primitive-instance boundary concerns built-in gates, switches
and pull sources. UDPs are a separate declaration and table language: the
legacy envelope has no primitive declaration, truth-table state, transition
matcher or UDP diagnostic channel. It therefore retains `PrimitiveSymbol`
loud, without flattening a table into a Boolean expression or introducing a
continuous driver evaluator.

## 2026-10-22 census and decision

The fresh 22,043-path census records `PrimitiveSymbol` in **382** files; **13**
are UDP-only and 369 co-occur. The independent read-only repricer finds 13
UDP spans in the sole files:

| feature | spans | files |
|---|---:|---:|
| UDP port-shape diagnostic | 3 | 3 |
| combinational current-state field | 1 | 1 |
| all-x input with non-x output/next-state | 2 | 2 |
| duplicate input with different outputs | 1 | 1 |
| multiple transitions in one row | 3 | 3 |
| missing input field | 1 | 1 |
| `z` table symbol | 1 | 1 |
| invalid initial output value | 1 | 1 |

The features partition these 13 diagnostic spans. Reproduce the table with:

```text
python3.9 extractors/sv/udp_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without resolving UDP rows, scheduling a primitive driver, or
salvaging a frontend-rejected declaration.
