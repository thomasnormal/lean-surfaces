# Simple immediate assertion actions

The sources exercise IEEE 1800-2023 §16.3 through the existing conditional
statement and retained continuation interfaces.

| Source | Complete independent output | Purpose |
|---|---|---|
| `table.sv` | Sixteen `row` lines, reproduced in `proof.lean` | Every two-bit four-state condition for assert, assume and cover |
| `actions.sv` | `actions 15` | Nested source actions, wide truthiness and empty failure blocks |
| `timers.sv` | `failure_tail 22 live 1`, then `success_tail 33 live 0` | Selected actions retain their tails despite changed conditions |
| `implicit_pass.sv` | `implicit_pass` | Successful checks do not take the implicit error branch |
| `implicit_error.sv` | Error diagnostic between `before_error` and `after_error`; nonzero status | Deliberate runtime refusal |
| `deferred.sv` | `deferred` | Deliberate deferred-region refusal |
| `null_failure.sv` | Independent compilation rejects the null failure action | Deliberate parser-disagreement refusal |

Independent observations completed on 2026-10-20. Runnable action checks use
`-ii_val -abvcoveron -abvrecordcoverall -abvdisableasrtst`, enabling all cover
actions and disabling additional assertion-engine status reports. The
implicit-error diagnostic uses ordinary `-ii_val`. No further output
filtering is applied. Default configuration differences are documented in
[the contract](../../../docs/sv-immediate-assertions.md).

In the table, `%b` preserves the two-bit source condition and each `%0d`
prints a signed 32-bit action result directly: zero means no action, one
means success, two means failure. All rows and `actions`/`implicit_pass`
occur at time zero. Timer observations occur at module ticks three and five;
`choice` is a signed 32-bit integer and the current one-bit condition prints
in four-state binary. There is no time rescaling or value projection.

`proof.lean` compares complete transcripts under both schedule oracles,
checks the three refusal boundaries, and certifies exact compiled subtrees
used by its four kernel theorems. Regenerate the envelopes with
`extractors/sv/extract.py`; they are generated artifacts.
