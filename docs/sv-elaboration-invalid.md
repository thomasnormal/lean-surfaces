# Invalid elaboration diagnostics — repricing boundary

IEEE 1800 elaborates generate scopes, constant schemes and their names before
simulation. A frontend error at that stage means there is no valid runtime
design to execute. The legacy envelope may already have flattened a supported
prefix, but it has no diagnostic provenance or partial-elaboration contract
that could make that prefix a replacement for the rejected source.

The public tier therefore retains `Elaboration:invalid-compilation` as a
design-level boundary. It does not drop an invalid generate branch, select the
first elaborated prefix, repair a delimiter, or add a recovery elaborator.
The existing generated-scope and parameter lowering remains available only
when the frontend reports a valid compilation.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Elaboration:invalid-compilation` in **33**
files, all 33 as the sole refusal. The independent read-only repricer finds
one diagnostic span per file. The source-shape telemetry is overlapping (a
name-conflict row may also use an illegal `genvar`, for example):

| shape | spans | files |
|---|---:|---:|
| generate-scope name conflict (including inactive/zero-entry blocks) | 17 | 17 |
| generate-region delimiter or placement | 4 | 4 |
| nested generate region | 3 | 3 |
| generate port declaration | 3 | 3 |
| nonconstant generate scheme | 2 | 2 |
| genvar outside a loop-generate scheme | 4 | 4 |
| generate end-label mismatch | 1 | 1 |
| macro conditional expression | 1 | 1 |

The table counts overlapping features over the 33 one-span sole files; it is
not a partition. Reproduce it with:

```text
python3.9 extractors/sv/elaboration_invalid_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only. It verifies that a source is blocked solely by
the marker, then reports lexical source-shape telemetry without changing
elaboration or interpreting a rejected design.
