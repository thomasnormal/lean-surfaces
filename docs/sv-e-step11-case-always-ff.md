# E Step 11: `case` in `always_ff`

This clean-room fixture is
[`Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv`](../Examples/system-verilog/sem2/case_always_ff_step11/case_always_ff_step11.sv).
It has one `always_ff @(posedge clk)` process with two plain `case` statements,
including exact `1x` and `z1` case items, a `default`, and a data operand that
is driven with `x`/`z`.  The parser envelope is checked by `agree.lean`; no
core-specific rewrite or new run2 meaning is involved.

IEEE 1800-2023 §12.5 defines plain case matching with case equality, so every
bit of the selector, including `x` and `z`, participates in the match.  The
items are considered in source order and the first matching item executes; a
`default` executes when none matches.  The right-hand side is sampled in the
active region and the nonblocking update is committed in the NBA region.  The
`always_ff` event and single-writer restrictions are those of §9.2.2.4.

The E rule proposed for Step 11 is therefore: at an edge, evaluate the
selector once from the pre-edge view, evaluate each case item's expressions in
source order with four-state `caseHit`, run the first matching body (or the
default), and return its NBA queue for the common commit step.  `casez`,
`casex`, `case … inside`, blocking statements, dynamic targets, delays, and
multiple event controls remain loud until their own Step 11 items land.  A
selector or data value containing `x`/`z` is retained; it is never coerced to a
two-state Boolean.

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

The old E edge executor reports `12.5: case statement in always_ff is outside
E-core-1`; this is the intended Step 11 input to the later implementation and
review.  `casez`/`casex` are separate fixtures and are not silently covered by
these rows.

## E-core review boundary

The fixture was reviewed against the current E-core-1 proof surface on
2026-11-10. The refusal remains deliberate. Supporting this construct requires
the first-match arm walk, NBA queue construction, and totality/frame lemmas to
be added together. The existing `execFF_mem` and `execFF_total` theorems cover
the accepted statement fragment and reject a partial arm evaluator; a local
implementation that only handled direct NBA arm bodies therefore was not
landed. The source-shaped parser envelope and all eight simulator rows remain
the acceptance target for the later E packet.
