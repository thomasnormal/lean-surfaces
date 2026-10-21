# Type parameters — repricing boundary

`TypeParameterSymbol:TypeParameter` marks a type parameter or a type-valued
declaration that the legacy envelope cannot bind. A selected type changes
width, signedness, aggregate shape and the legality of dependent expressions;
it is compile-time type identity, not a runtime scalar.

## Why type parameters remain a boundary

The current envelope has no type environment, nominal type identity or
type-operator representation. Overrides at an instance, defaults that depend
on earlier parameters, and `type(...)` expressions all require elaboration
before the module store can be built. Treating the default type as fixed
would silently mis-size dependent declarations and would make legal overrides
answer incorrectly.

The public tier keeps every type-parameter marker loud. It does not choose a
default, erase a type operator, or add a second elaborator.

## 2026-10-21 census and decision

The fresh 22,043-path census records `TypeParameterSymbol:TypeParameter` in
**18** files: **8** are type-parameter-only and **10** co-occur with another
wall. The sole files contain **9** recovered spans. Their source-span
features overlap:

| source feature | instances | files |
|---|---:|---:|
| empty frontend span | 3 | 3 |
| `type(...)` operator | 4 | 3 |
| typed default | 2 | 2 |

These labels describe recovered text, not an admission claim. Reproduce the
table with:

```text
python3.9 extractors/sv/type_parameter_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and performs no type binding or override.
