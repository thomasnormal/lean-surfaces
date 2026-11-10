# E Step 11: `case` in `always_ff`

This clean-room fixture is
[`Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv`](../Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv).
It has one `always_ff @(posedge clk)` process with two plain `case` statements,
including exact `1x` and `z1` case items, a `default`, and a data operand that
is driven with `x`/`z`. The parser envelope is checked by `agree.lean`, which
executes the unchanged loaded body in E and proves its trace agrees with the
simulators. No statement is lowered into an if-chain.

IEEE 1800-2023 §12.5 defines plain case matching with case equality, so every
bit of the selector, including `x` and `z`, participates in the match.  The
items are considered in source order and the first matching item executes; a
`default` executes when none matches.  The right-hand side is sampled in the
active region and the nonblocking update is committed in the NBA region.  The
`always_ff` event and single-writer restrictions are those of §9.2.2.4.

The E-core-1 rule in `LeanModels/Sv/Kernel/Core1Edge.lean` is: at an edge, evaluate the
selector once from the pre-edge view, evaluate each case item's expressions in
source order with four-state `caseHit`, run the first matching body (or the
default), and return its NBA queue for the common commit step. An absent
default is a no-op; an empty matching body still stops the arm walk. `casez`,
`casex`, `case … inside`, blocking statements, dynamic targets, delays, and
multiple event controls remain loud until their own Step 11 items land.  A
selector or data value containing `x`/`z` is retained; it is never coerced to a
two-state Boolean. Qualified cases (`unique`, `unique0`, `priority`) also
remain loud in this edge fragment.

`execFFArm` and `execFFCase` use structural mutual recursion with `execFF`;
there is no semantic fuel. `Stmt2.ffOkB` checks the selector, patterns, arm
bodies and default. `execFFArm_mem`/`execFFCase_mem` extend `execFF_mem`'s
static-window frame, and their totality twins extend `execFF_total`.
`EdgeProfile.ofChecks` and R-EDGE apply unchanged. The fixture proves its
profile and slot result for every legal process-atomic schedule and every
typed store. Its concrete trace alternates clock-low input slots and
clock-high edge slots; each successful test-executor result is an E closed
slot by `exec1_sound`. This four-state execution evidence does not change
the separate resolution-aware observation boundary.

## Differential rows

The testbench is [`case_always_ff_step11_tb.sv`](../Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11_tb.sv).
Icarus Verilog 13.0 and Xcelium 24.03-s004 produced the same rows:

| row | selector | data | `q` | `q_default` |
| --- | --- | --- | --- | --- |
| `first` | `xx` (before the first edge) | `xxxx` | `xxxx` | `xxxx` |
| `case_00_d_xz01` | `00` | `xz01` | `xz01` | `xz01` |
| `case_01_d_zzzz` | `01` | `zzzz` | `1010` | `1101` |
| `case_1x_d_0000` | `1x` | `0000` | `1011` | `1101` |
| `case_1z_d_1111` | `1z` | `1111` | `1111` | `1101` |
| `case_z1_d_0001` | `z1` | `0001` | `1100` | `1101` |
| `case_x0_d_0000` | `x0` | `0000` | `1111` | `1101` |
| `case_zz_d_0000` | `zz` | `0000` | `1111` | `1101` |

The second clean-room source,
[`case_always_ff_order_step11.sv`](../Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_order_step11.sv),
covers comma labels, a duplicate label, a default written before the explicit
labels, an absent default, an empty matching body, and a nested case whose
last NBA overwrites the earlier NBA to the same variable. Both simulators
agree with E on these additional rows:

| selector/data | `q` | `q_hold` | `q_empty` | `q_nested` |
| --- | --- | --- | --- | --- |
| initial | xxxx | xxxx | xxxx | xxxx |
| 00/0101 | 0101 | 0101 | xxxx | 0101 |
| 01/zzzz | zzzz | 0101 | zzzz | 0011 |
| 1x/xxxx | 1011 | 0101 | xxxx | 0011 |
| z1/xz01 | 1100 | 0101 | xz01 | 0011 |
| 11/0110 | 1111 | 0101 | 0110 | 0011 |
| 00/1010 | 1010 | 1010 | 0110 | 0010 |

Reproduce the E-to-source comparison after building the fixture:

```sh
lake build 'Examples.«system-verilog».sem2.case_always_ff_step11.agree'
python3 Examples/system-verilog/sem2/case_always_ff_step11/check.py
```

The checker prints the simulator versions, gates Xcelium with its readiness
simulation, and compares both complete source-testbench traces with E's
`oracle.lean` output. A refusal or exhausted test budget fails. The trace
equalities and new frame/totality lemmas are kernel checked; their axiom
audits contain only subsets of `propext`, `Classical.choice`, `Quot.sound`.

## Earlier public review

The public-master review on 2026-11-10 recorded this boundary before the
implementation on this review branch:

> The fixture was reviewed against the current E-core-1 proof surface on
> 2026-11-10. The refusal remains deliberate. Supporting this construct requires
> the first-match arm walk, NBA queue construction, and totality/frame lemmas to
> be added together. The existing `execFF_mem` and `execFF_total` theorems cover
> the accepted statement fragment and reject a partial arm evaluator; a local
> implementation that only handled direct NBA arm bodies therefore was not
> landed. The source-shaped parser envelope and all eight simulator rows remain
> the acceptance target for the later E packet.

This branch adds the complete arm walk, NBA construction, and frame/totality
packet described above. Landing remains subject to owner review.
