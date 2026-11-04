# `interconnect` nets — hierarchical connectivity boundary

IEEE 1800-2023 §§6.6.8 and 6.7.1 define `interconnect` as a net spelling for
connectivity between ports and nets across hierarchy. Its effective net type
comes from the connected declarations, so an interconnect can preserve
resolved four-state behavior across a connection and can resolve different
bits of an array to different net types. The declaration has no initializer,
drive strength or charge strength; it may carry dimensions and at most one
delay value.

## Why `Interconnect` remains a boundary

The legacy envelope stores a local scalar or packed net and has no elaborated
port graph, bidirectional connection identity, per-bit net-type resolution or
interconnect delay publication. Rewriting an interconnect as a `wire` would
invent a local net type and lose the connected declarations' resolution. A
declaration with an initializer, explicit data type, strength or a min:typ:max
delay is a frontend diagnostic and cannot be salvaged by dropping the illegal
part. No interconnect is admitted and no second elaborator or scheduler is
introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:Interconnect` in **15** files:
**8** are Interconnect-only and **7** co-occur with another wall. The
read-only repricer finds **10** declarations in the sole files:

| source shape | declarations | files |
|---|---:|---:|
| interconnect declarations | 10 | 8 |
| declaration initializers | 3 | 3 |
| delay specifications | 2 | 2 |
| min:typ:max delay | 1 | 1 |
| explicit data type | 1 | 1 |
| drive or charge strength | 1 | 1 |
| packed dimensions | 2 | 1 |
| unpacked dimensions | 2 | 2 |
| per-bit net-type resolution observation | 1 | 1 |
| compile-error diagnostic shapes | 6 | 6 |

Rows overlap. Reproduce the measurement with:

```text
python3.9 extractors/sv/interconnect_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only. It does not infer connected ports,
resolve net types, or turn an invalid declaration into a partial runtime
design.
