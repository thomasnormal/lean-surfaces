# Residual module typedefs — retained boundary

Valid scalar and packed integral typedefs, untagged packed structs and unions,
and fixed array metadata are already erased at extraction while preserving the
bound widths and storage identity of their uses. The remaining
`TypeAliasType:TypeAlias` marker covers module-scope aliases that need an
unrepresented aggregate type, an elaboration-time query, or a frontend
diagnostic.

The envelope has no general aggregate type descriptor, enum diagnostic
status, or constant-expression evaluator for default struct members. Dropping
the alias would either erase the type needed by `$bits` or hide a rejected
declaration. The marker therefore remains loud; no aggregate storage or
typedef evaluator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `TypeAliasType:TypeAlias` in **299** files;
**12** are alias-only and 287 co-occur. The independent read-only repricer
finds 12 alias spans in the sole files:

| feature | spans | files |
|---|---:|---:|
| `$bits` query | 8 | 8 |
| aggregate typedef | 9 | 9 |
| enum typedef | 3 | 3 |
| enum-member redefinition | 2 | 2 |
| nonpositive enum range | 1 | 1 |
| nonconstant member initializer | 1 | 1 |

Features overlap. Reproduce the table with:

```text
python3.9 extractors/sv/type_alias_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
features without erasing an unsupported type or admitting a rejected alias.
