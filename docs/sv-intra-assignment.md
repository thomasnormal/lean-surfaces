# Blocking intra-assignment timing

IEEE 1800-2023 §10.4.1 and §9.4.5 blocking assignments with an admitted
intra-assignment control compile to three existing statements:

1. Evaluate and save the integral RHS once, at encounter.
2. Execute the delay or event control through the existing retained continuation.
3. Resolve the destination selectors in the resumed state and copy the saved value.

For example, `word[index+:8] = #3 source` saves `source` immediately. If
another process changes both variables during the delay, copyback uses the
old source value and the new index. Existing packed assignments preserve
neighboring bits and apply each destination's two-state conversion.

The source compiler admits pure integral operands and supported packed
destinations, including concatenations and runtime packed selections. A
delay must be a known nonnegative integral literal below `2^64`. A single
event control must watch a one-bit identifier, with posedge, negedge or any
change. Repeated event control uses the existing repeat-count conversion:
sample once, interpret signedness, and perform no wait for a nonpositive or
unknown count. Subsequent changes to the count do not restart or shorten
the saved wait.

Each source assignment gets collision-checked `$intra:<source-offset>`
capture storage. Its declaration executes at every visit, so a repeated
body captures fresh data. The stepper retains that data, prior output,
pending NBA work and the ordinary statement continuation. No evaluator,
statement constructor, storage primitive or scheduler changes.

Extraction and execution have different boundaries. `#0` remains a real
delay checkpoint; the timed slot delivers it through Inactive and then
resumes the retained continuation. It is never erased or replaced with an
immediate assignment.
Procedural writes to watched clocks still require the existing internal
edge-publication rule. Timed designs with time-zero-only `$time` lowering
remain refused. The time-zero self-check runner refuses waits.

Nonblocking intra-assignment controls remain loud, including `#0`: delayed
NBA publication requires a future-update rule independent of process
lifetime. Creating a sleeping synthetic process would not supply that
rule. Dynamic unpacked destinations, unsupported storage, effectful RHS,
selectors or repeat counts, dynamic/real/unit-bearing delays, event lists,
`iff`, invalid compilations and symbolic-mode controls also remain loud.

The [authored fixtures](../Examples/system-verilog/intra_assignment/README.md)
record independent full transcripts and fixture-bound kernel proofs of
capture-before-wait, resumed-index copyback and retained repeat control.
Their zero-delay and internal-edge examples certify explicit runtime
boundaries and are not counted as execution matches.

## Nonblocking publication — 2026-10-21

The residual `IntraAssignment:publication-or-context` marker is specifically
the nonblocking path. In the fresh 22,043-path census it is the sole wall in
**55** files and occurs **75** times. The spans contain **63** delayed NBA
controls, **2** event controls, **1** explicit `#0`, and **9** repeat/context
forms. These rows are telemetry for the existing refusal, not a new lowering.

An intra-assignment nonblocking control saves a value and schedules a future
publication whose update queue, process lifetime and same-time ordering are
independent of the submitting process. Reusing the blocking capture/wait path
or creating a synthetic sleeper would lose that distinction. The tier keeps
all four shapes loud until the kernel supplies a future-update rule; no
publication or second scheduler is invented. Reproduce the measurement with:

```text
python3.9 extractors/sv/intra_nba_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```
