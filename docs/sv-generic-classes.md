# Parameterized class declarations — repricing boundary

`GenericClassDefSymbol` marks a parameterized class declaration. Value and
type parameters are bound before class members are elaborated, and each
specialization has its own nominal type and static/member scope. The marker
is therefore a class-object boundary as well as an elaboration boundary.

## Why parameterized classes remain a boundary

The current envelope has no generic class table, parameter environment,
specialization identity or class member frame. A parameter can change a
packed aggregate width, a typedef, a localparam or a constant static method;
type parameters can change the entire member type. Flattening one default
specialization would silently change other legal specializations and would
erase class identity. The module executor also has no method or object store.

The public tier keeps every `GenericClassDefSymbol` declaration loud. It does
not choose default parameters, inline a static method, or invent an object
specialization, and it adds no second elaborator or scheduler.

## 2026-10-21 census and decision

The fresh 22,043-path census records `GenericClassDefSymbol` in **146** files:
**10** are generic-class-only and **136** co-occur with another wall. The
sole files contain **10** parameterized class spans. Overlapping source
features are:

| source feature | instances | files |
|---|---:|---:|
| value parameters | 9 | 9 |
| type parameters | 5 | 5 |
| virtual classes | 8 | 8 |
| typedef members | 7 | 7 |
| static methods | 2 | 2 |
| packed aggregate types | 2 | 2 |
| local parameters | 1 | 1 |

These labels describe recovered source spans, not an admission claim.
Reproduce the table with:

```text
python3.9 extractors/sv/generic_class_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and performs no class specialization.
