# Empty-member boundary — retained frontend syntax diagnostics

`EmptyMemberSymbol:EmptyMember` marks a frontend recovery point where a design
member has no valid bound AST node. The current sole rows cover soft-keyword
mode, primitive arrays without an instance identifier, nested attribute
expressions and dollar-leading simple identifiers.

## Why empty members remain loud

IEEE 1800-2023 §§5.6, 5.12, 22.14 and 28.3.4 make these forms lexical or
syntactic constraints. The envelope has no diagnostic stream or recovery node
from which to reconstruct the missing declaration/member. Treating `$name` as
a normal identifier, inventing a primitive instance name, accepting a nested
attribute value or ignoring `begin_keywords` would execute source the frontend
rejected. No second parser or recovery evaluator is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `EmptyMemberSymbol:EmptyMember` in **57**
files: **6** are sole refusals and 51 co-occur. Re-elaborating those sole
files with the read-only repricer finds **6** empty-member spans:

| source shape | spans | files |
|---|---:|---:|
| soft keyword under `begin_keywords` | 1 | 1 |
| primitive array without instance name | 1 | 1 |
| nested attribute expression | 2 | 2 |
| dollar-leading simple identifier | 2 | 2 |

Reproduce the table with:

```text
python3.9 extractors/sv/empty_member_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument re-elaborates source in memory and writes no output beside the
read-only corpus. Its shape counts are telemetry, not syntax recovery.
