# Dynamic-index NBA targets in E

IEEE 1800-2023 §10.4.2 fixes the RHS and the left-hand index when a
nonblocking assignment is issued. Section 11.5.1 defines packed element
selection: an unknown or out-of-range index writes nothing. The queued
update carries the selected bit offset and resized value; the NBA region
never re-evaluates either. A signed negative index is out of range. The
RHS is evaluated even when selection produces no update.

`Kernel/Core1Targets.lean` defines `Lhs2.edgeWindows` directly on the retained
`Lhs2.index` node, using E's `evalPure2` and the existing `indexInt?` signedness
rule. Declaration widths determine bounds. `Lhs2.edgeOkB` requires a declared
target, positive element width and a well-formed index expression. Existing
whole signals, constant slices and static concatenations retain their rule.
Dynamic concatenations, unpacked storage and unsupported nodes refuse loudly.
There is no semantic fuel, target enumeration or source rewrite.

The old exact-membership frame `execFF_mem` has been replaced by
`execFF_covered`: every issued update is contained in some static footprint
from `Stmt2.nbaBounds`. Static targets retain their precise footprints; a
runtime select reserves the entire declared signal, its longest static prefix
(§11.5.3). `Lhs2.edgeWindows_covered` proves containment for every sampled view.
`Lhs2.edgeWindows_total` and the extended `execFF_total` prove totality on
admitted bodies. `EdgeProfile.ofChecks` uses containment to derive disjoint
updates and exclusion of clock/reset writes from the executable checks.
Its statement, `EdgeProfile`, and `rEdge` are unchanged.

The original clean-room source and seven rows are preserved in
[`dynamic_nba_target_step11/`](../Examples/system-verilog/sem2/dynamic_nba_target_step11/).
Its source-shaped `always_ff @(posedge clk) if (en) q[idx] <= d` now has a
kernel-checked E trace instead of a legacy-run witness and a negative E guard:

```text
first             q=xxxx
nba_idx_0_d1      q=xxx1
nba_idx_3_d0      q=0xx1
nba_idx_x_d1      q=0xx1
nba_idx_z_d0      q=0xx1
nba_idx_4_d1      q=0xx1
nba_idx_1_disabled q=0xx1
```

The additional `dynamic_nba_issue_step11.sv` retains two source processes,
three same-signal NBA writes, a two-bit packed-element select and a signed
index. Its thirteen rows cover startup, reset, old-state RHS sampling across
processes, an NBA to the selector before its use, overlapping destinations
(last issued wins), x/z on indices and both data bits, signed negative and
positive out-of-range indices, and a second reset. Both loaded designs have
`EdgeProfile` proofs and `rEdge` corollaries for every typed store and every
legal process-atomic schedule. Negative guards pin the overlapping-writer,
clock-write, invalid-index-expression, missing-target and dynamic-concat
boundaries. An invalid select cannot hide an unsupported RHS.

Run the direct E comparisons with:

```sh
LEAN_NUM_THREADS=2 nice -n 19 python3 Examples/system-verilog/sem2/dynamic_nba_target_step11/check.py
```

The checker executes E directly, fails on refusal or test-budget exhaustion,
and compares all 20 rows with Icarus and readiness-gated Xcelium. Measured:
Icarus 13.0 and Xcelium 24.03-s004 each match all 20 rows. The fixture
uses the proved-equivalent store cache from the plain-always fixture; it does
not replace E's transition rule. The row proofs use kernel `decide` because
they evaluate a fixed small source fixture. All new lemmas are axiom-audited.
The x/z rows describe the four-state executor; no shared resolution relation,
`DecisionKnown`, `Spec2` guard or binary-refinement premise is changed.

## Current E review

On 2026-11-11, public master `bfe33dfb` was checked with the complete
source-shaped packet from `4e70a500c`.  The focused E target built in 50 jobs;
the kernel-checked target and issue traces matched all seven and thirteen rows,
respectively.  The differential checker then matched all twenty rows against
Icarus Verilog 13.0 and readiness-gated Xcelium 24.03-s004.  The proof audit
reported only `propext`, `Classical.choice`, and `Quot.sound`, as for the
surrounding E packets.

This review covers packed runtime selects on the retained `Lhs2.index` node,
including x/z, signed negative, and out-of-range indices, pre-edge RHS
sampling, overlapping issue-order updates, and the containment frame.  It does
not admit unpacked storage, dynamic concatenations, or unsupported index/RHS
expressions.  No `Stmt2` constructor, resolution relation, `DecisionKnown`,
`Spec2` guard, run2 meaning, or MemCycle meaning was changed.
