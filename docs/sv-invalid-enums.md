# Invalid enumeration boundary — retained base-type diagnostics

`Enum:invalid-compilation` marks an enumeration rejected during elaboration.
The sole rows cover X/Z values assigned to a two-state `bit` base and duplicate
enumeration values.

## Why invalid enums remain loud

IEEE 1800-2023 §6.19 requires enum values to fit the declared base type and
requires each enumeration value to be unique. A two-state base cannot contain
X/Z, while duplicate values invalidate the enumeration declaration. The public
enum representation has no diagnostic or invalid-declaration state. Removing
the bad member, squashing X/Z or renumbering duplicates would fabricate a
different enum. No recovery enum evaluator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Enum:invalid-compilation` in **36** files:
**4** are sole refusals and 32 co-occur. Re-elaborating the sole files finds
four rejected enum spans: three X/Z-in-two-state-base cases and one duplicate
enumeration-value case. Reproduce with:

```text
python3.9 extractors/sv/enum_invalid_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only and does not repair enum values.
