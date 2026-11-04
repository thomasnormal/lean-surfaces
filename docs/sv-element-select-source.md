# Element-select source-type boundary — retained selection diagnostics

`ElementSelectExpression:source-type` marks an element selection whose source
type is outside the legacy selected-read representation. The envelope admits
fixed packed scalar/integer sources and selected fixed aggregate cells, but it
does not guess a source layout for nested packed-union members, scalar
bit-select diagnostics or unpacked-array out-of-bounds results.

## Why the source remains loud

IEEE 1800-2023 §11.5.1 makes a bit-select of a scalar illegal. Sections 7.3.1
and 7.4.5 also require packed-union layout/aliasing and state-kind-specific
out-of-bounds values. A scalar zero, a flattened union member or a single
unknown result would fabricate behavior. The envelope has no general aggregate
element type, aliasing layout or out-of-bounds state rule, so no selection is
rewritten and no second evaluator or scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ElementSelectExpression:source-type` in
**662** files. **11** are sole refusals and 651 co-occur. The independent
read-only repricer finds **23** unsupported selection spans in those sole files:

| source shape | spans | files |
|---|---:|---:|
| scalar source bit-select diagnostic | 1 | 1 |
| nested packed-union member selection | 17 | 5 |
| two-state unpacked-array out-of-bounds read | 2 | 2 |
| four-state unpacked-array out-of-bounds read | 2 | 2 |
| enum-array out-of-bounds base-type result | 1 | 1 |

The state and enum labels describe overlapping out-of-bounds rules. Reproduce
the table with:

```text
python3.9 extractors/sv/element_select_source_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without resolving packed-union aliasing or inventing an out-of-bounds
value.
