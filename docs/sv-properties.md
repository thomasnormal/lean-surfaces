# Property declarations — repricing boundary

`PropertySymbol:Property` marks a named concurrent-property declaration. It is
the declaration boundary for the sampled assertion language; the separate
`ConcurrentAssertionStatement` marker covers statements that invoke a
property. A declaration therefore remains loud even when its source body is
short or appears to contain only a boolean expression.

## Why property declarations remain a boundary

A property carries formal arguments, local variables, clocking and sequence
operators. Its evaluation samples values in the Preponed region, retains
attempt state over later ticks, and publishes a result in the Observed or
Reactive path. Abort/disable controls and sampled system functions change the
attempt state rather than computing an ordinary procedural boolean. The
current envelope has no property table, sampled-value history, sequence
automaton or declaration frame.

The public tier therefore keeps every property declaration explicit. It does
not drop a declaration, inline its body into a statement, or add a second
scheduler. Property declarations and property-use statements remain separate
boundaries so a future assertion tier can represent each source role without
losing formal or sampled-state identity.

## 2026-10-21 census and decision

The fresh 22,043-path census records `PropertySymbol:Property` in **471**
files: **10** are property-only and **461** co-occur with another wall. The
sole files contain **11** unsupported property spans. Their recovered source
features overlap:

| source feature | instances | files |
|---|---:|---:|
| clocked (`@(...)`/edge) | 6 | 6 |
| implication (`|->`/`|=>`) | 4 | 4 |
| formal property arguments | 3 | 3 |
| local variables | 2 | 2 |
| sampled functions (`$past`/`$rose`/…) | 2 | 2 |
| abort/disable controls | 1 | 1 |
| `endproperty` label | 1 | 1 |

These labels describe the recovered span, not an admission claim. Reproduce
the table with:

```text
python3.9 extractors/sv/property_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and does not evaluate a property body.
