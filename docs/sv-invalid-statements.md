# Invalid statement markers — repricing boundary

`InvalidStatement` is a frontend recovery marker, not an executable
SystemVerilog statement family. The extractor emits it when slang marks a
statement as bad; its span may contain a whole `begin` block, an empty span,
or a token from an unsupported VPI/system-task surface. The marker preserves
the frontend's diagnostic boundary instead of pretending that the recovered
source is a valid procedural program.

## Why the marker remains a boundary

The envelope can only lower a statement after the frontend has supplied a
valid bound AST node. A bad block may contain otherwise familiar assignments,
delays and `$finish` calls around an unsupported VPI call or malformed syntax.
Dropping the `InvalidStatement` wrapper would either skip those effects or
execute a partial recovery tree whose parse and diagnostic behavior is not
defined. An empty marker has no source semantics to interpret. The proper
future fix is a typed frontend conversion or a separate diagnostic contract,
not a generic `begin` admission.

The current tier therefore keeps the marker loud and leaves the underlying
construct family to its own boundary when the frontend can expose it. No
second parser, recovery interpreter or fabricated statement is introduced.

## 2026-10-21 census and decision

The fresh 22,043-path census records `InvalidStatement` in **1,329** files:
**606** are marker-only and **723** co-occur with another wall. The read-only
repricer finds one recovery marker in each of the 606 sole files:

| recovered span shape | instances | files |
|---|---:|---:|
| bad `begin`/block recovery span | 568 | 568 |
| VPI system-task token | 31 | 31 |
| empty frontend span | 7 | 7 |

The sole files are distributed across simulation, compile-error and
diagnostic corpus rows; chapter 36 contributes 456 of the 606 files because
VPI-oriented bodies frequently make the enclosing block bad. The shape labels
describe the frontend span, not a claim that `begin` itself is unsupported.
No recovery shape is independently admissible. Reproduce the table with:

```text
python3.9 extractors/sv/invalid_stmt_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its recovery-shape counts are telemetry, not a parser or interpreter.
