# Compilation-unit aggregate typedefs — retained boundary

The admitted typedef slice erases scalar, packed integral and selected
untagged aggregate aliases as compile-time metadata. Compilation-unit aliases
outside that slice still carry aggregate and union rules that cannot be
represented by the legacy envelope: packed-member legality and widths,
tagged-union tags, dynamic members, default initialization and frontend
diagnostics.

`TypeAliasType` remains explicit. The tier does not drop a unit alias, turn a
tagged union into an untagged vector, or fabricate a dynamic aggregate store.

## 2026-10-22 census and decision

The fresh 22,043-path census records `TypeAliasType` in **116** files; **12**
are unit-alias-only and 104 co-occur. The independent read-only repricer finds
**13** alias spans across those 12 files:

| feature | spans | files |
|---|---:|---:|
| nonintegral packed member | 7 | 7 |
| packed union width | 1 | 1 |
| packed-dimension qualifier | 2 | 2 |
| unpacked-struct signing | 1 | 1 |
| union-member default | 2 | 2 |
| void in untagged union | 1 | 1 |
| packed tagged union | 2 | 2 |
| tagged-union dynamic member | 2 | 2 |
| untagged-union dynamic member | 1 | 1 |

Features overlap, and one source file contributes two unsupported spans. Reproduce
the table with:

```text
python3.9 extractors/sv/unit_type_alias_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
features without resolving aggregate layout or admitting a dynamic union.
