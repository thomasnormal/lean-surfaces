# `casez` and `casex` in `always_ff`

The clean-room fixture is
[`Examples/system-verilog/sem2/casez_casex_always_ff_step11/casez_casex_always_ff_step11.sv`](../Examples/system-verilog/sem2/casez_casex_always_ff_step11/casez_casex_always_ff_step11.sv).
One `always_ff @(posedge clk)` contains a `casez` and a `casex`, each with
wildcard patterns, a default, and a nonblocking target.  The extractor keeps
both `CaseStmt` nodes and their source order.  No wildcard pattern is expanded
into a collection of assignments.

IEEE 1800-2023 §§9.2.2.4 and 12.5.1 distinguish the match rules:
`casez` treats z and `?` as wildcard bits, while `casex` treats x, z, and `?`
as wildcard bits on either operand. E reuses the existing `caseHit` with the
retained mode; `execFFCase` still stops at the first source-order hit and
returns that body's NBA queue. A missing match selects the default. NBA
values are sampled from the unchanged pre-edge view. No new matching
definition or semantic fuel is introduced.

The rows cover the first x state, known selectors, a z pattern, x/z selectors,
all-wildcard selectors, and x/z data. The last row distinguishes the first
overlapping match from the default. Icarus 13.0 and Xcelium 24.03-s004 agree
with E on all thirteen rows:

```text
first              qz=xxxx qx=xxxx
sel_0000_d9        qz=0011 qx=0110
sel_0001_d8        qz=0010 qx=0101
sel_00z1_d7        qz=0010 qx=0101
sel_01xz_d6        qz=0001 qx=0100
sel_1x00_d5        qz=0101 qx=0101
sel_1z11_d4        qz=0100 qx=0100
sel_zzzz_d3        qz=0011 qx=0011
sel_xxxx_d2        qz=0011 qx=0010
sel_1x00_dxz       qz=xz01 qx=xz01
sel_1z11_dz        qz=zzzz qx=zzzz
sel_1000_dx        qz=xxxx qx=xxxx
sel_zzzz_da        qz=1010 qx=1010
```

`agree.lean` checks that the loaded nodes retain `.casez` and `.casex`, proves
their `EdgeProfile`, and proves their slot result for every typed store and
every legal process-atomic schedule via R-EDGE. Its trace equality is kernel
checked, including every original row and startup. The generalized arm/list
frame and totality lemmas preserve the `execFF_mem`/`execFF_total` contract.
Their axiom audits contain only the standard three axioms.

Reproduce the direct E-to-source comparison after building the fixture:

```sh
lake build 'Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree'
python3 Examples/system-verilog/sem2/casez_casex_always_ff_step11/check.py
```

The checker emits E's actual trace, prints both simulator versions and gates
Xcelium through its readiness simulation. A refused or incomplete E trace
fails. `case … inside` and qualified cases remain loud in this fragment.
This four-state execution evidence keeps the existing resolution-aware
observation boundary unchanged.
