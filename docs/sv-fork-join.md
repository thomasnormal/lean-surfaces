# Fork/join process control — repricing boundary

`fork ... join`, `join_any` and `join_none` create concurrent child
processes. The parent continuation, child activation order, completion barrier,
early release and detached-child lifetime are scheduler-visible state. Named
fork blocks also interact with disable and cancellation. These are process
semantics, not alternate spellings of a sequential block.

## Why fork/join remains a boundary

The surface envelope has no child-process identity or fork frame. It cannot
retain several child continuations, wait for all or the first child, release a
parent at the correct region, or keep `join_none` children alive after the
parent proceeds. Delays, events, nonblocking publications and named-block
disable add the existing kernel's retained-continuation and cancellation
obligations. Executing only the parent or serializing the children would
change output ordering, shared-store races and completion.

The public tier therefore keeps all three join flavors loud until it can call
the existing scheduler with a typed fork frame. No second scheduler, source
order shortcut or fabricated child completion is introduced. `BlockStatement`
markers for each flavor remain explicit in the envelope.

## 2026-10-21 census and decision

The fresh 22,043-path census records the three fork/join markers in **571**
files. **126** files are blocked solely by one or more join flavors; the other
445 co-occur with another wall. The sole files contain **132** join blocks:

| join flavor | instances | files |
|---|---:|---:|
| `join` (JoinAll) | 90 | 90 |
| `join_any` | 10 | 10 |
| `join_none` | 32 | 29 |

The exact counts are emitted from the frontend markers rather than inferred
from truncated source spans. Reproduce the table with:

```text
python3.9 extractors/sv/fork_join_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its flavor counts are telemetry for the scheduler boundary, not a
fork evaluator.
