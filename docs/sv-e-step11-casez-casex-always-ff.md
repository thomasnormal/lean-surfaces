# `casez` and `casex` in `always_ff`

The clean-room fixture is
[`Examples/system-verilog/sem2/casez_casex_always_ff_step11/casez_casex_always_ff_step11.sv`](../Examples/system-verilog/sem2/casez_casex_always_ff_step11/casez_casex_always_ff_step11.sv).
One `always_ff @(posedge clk)` contains a `casez` and a `casex`, each with
wildcard patterns, a default, and a nonblocking target.  The extractor keeps
both `CaseStmt` nodes and their source order.  No wildcard pattern is expanded
into a collection of assignments.

IEEE 1800-2023 §§9.2.2.4, 12.5.1, and 12.5.4 distinguish the match rules:
`casez` treats z and `?` as wildcard bits, while `casex` treats x, z, and `?`
as wildcard bits.  The rows cover the first x state, known selectors, a z
pattern, x/z selectors, and all-wildcard selectors.  Icarus 13.0 and Xcelium
24.03-s004 agree on all nine rows:

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
```

The source-oracle rows remain in the testbench and differential harness.
The preparatory legacy cycle witness has been retired. E-core-1 currently
refuses case bodies at its explicit 12.5 boundary (`execFF`), so `agree.lean`
retains that admission result pending review of the native E rule. The rule
must preserve source-order first-hit
matching, four-state wildcard distinctions, immediate NBA RHS sampling, and
the default path; qualified/range/pattern case forms remain separate walls.

## E-core review boundary

Reviewed against E-core-1 on 2026-11-10. The retained `casez`/`casex` modes,
source order, and nine Icarus/Xcelium rows pass the focused agreement proof.
The current refusal remains deliberate: wildcard matching needs a four-state
`caseMode` arm walk and an NBA frame/totality proof, while `Stmt2.ffOkB` still
requires plain static-window statements. `casez`, `casex`, wildcard `?`, and
x/z selector handling therefore remain named at the explicit 12.5 boundary;
no wildcard expansion or partial E evaluator was added.
