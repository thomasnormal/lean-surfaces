# SystemVerilog verification frontier

This page sets the public path from the current source-shaped SystemVerilog
tier to properties over complicated blocks and, eventually, a small complete
chip. The exact SystemVerilog profile remains the authority. E is the
semantics route; cycle views and contracts must refine it. The scheduler and
event rules belong to `ls-spec`, so an SVA sampling rule that is not present in
the kernel is recorded as a request rather than reimplemented here.

The scale target is Harmonic's public Tensordyne case study: a 12.2M-gate
equivalent partition, 1.24M flops, 45 Mbit of SRAM, hundreds of concurrent
FSMs, and 241 whole-block properties proved from power-on with deep
counterexamples. It is a scope reference only. This repository uses public
RTL, kernel-checked Lean over E, and differential witnesses; it does not copy
that case study's methods or contain private-chip material.

## Pinned first targets

The first targets are OpenTitan primitive FPV sets. The source snapshot is the
public `lowRISC/opentitan` repository at commit
[`0a6ff6855bd9c6489110df167501e4d5f5c9bdbd`](https://github.com/lowRISC/opentitan/commit/0a6ff6855bd9c6489110df167501e4d5f5c9bdbd),
checked out on 2026-11-04. The repository and the selected files carry the
Apache License 2.0 (`LICENSE`, with SPDX headers in each source file).

| target | RTL and FPV sources | assertion set | first measured refusal census (before F1 retention) |
|---|---|---:|---|
| `prim_fifo_sync` | `hw/ip/prim/rtl/prim_fifo_sync.sv`; `hw/ip/prim/fpv/vip/prim_fifo_sync_assert_fpv.sv`; `hw/ip/prim/fpv/tb/prim_fifo_sync_bind_fpv.sv`; `hw/ip/prim/fpv/tb/prim_fifo_sync_tb.sv` | 27 `ASSERT`/`ASSERT_INIT` sites in the FPV VIP | 46 unsupported nodes: 9 `PortSymbol:type` (the `NumDuts` unpacked TB ports), 10 explicit conversions, 9 `ProceduralBlockSymbol:NoEventControl` (SVA), 6 `PortSymbol:net-z`, 4 calls, 3 uninstantiated definitions, 2 immediate symbolic assertions, 2 unresolved identifiers, and 1 delay. |
| `prim_arbiter_ppc` | `hw/ip/prim/rtl/prim_arbiter_ppc.sv`; `hw/ip/prim/fpv/tb/prim_arbiter_ppc_tb.sv` | 15 `ASSERT`/`ASSERT_INIT` sites in the RTL | 26 unsupported nodes: 15 `ProceduralBlockSymbol:NoEventControl` (SVA), 3 `ForLoopStatement`, 2 `PortSymbol:type` (`data_i [N]`), 2 calls, and one each of `NamedValueExpression:type`, `ImmediateAssertion:symbolic`, `VariableSymbol:default-point-array`, and `AssignmentExpression:target`. |
| `prim_packer` | `hw/ip/prim/rtl/prim_packer.sv`; `hw/ip/prim/fpv/tb/prim_packer_tb.sv` | 10 `ASSERT`/`ASSERT_INIT` sites in the RTL | 32 unsupported nodes: 14 explicit conversions, 12 `ProceduralBlockSymbol:NoEventControl` (SVA), 2 `ImmediateAssertion:symbolic`, 1 `ForLoopStatement`, 1 `PortSymbol:net-z`, 1 call, and 1 uninstantiated definition. |

The census is a source census, not an admission claim. It was produced with
the checked-in `extractors/sv/extract.py` symbolic frontend at the pinned
commit, using each target's `.core` file list plus the primitive RTL files
needed to name its instances. No source was edited. The dominant common wall
is the SVA process form; unpacked parameterized ports and explicit casts are
the next walls. A target becomes an F1 success only when its own assertions
load as Lean propositions over E, not when the extractor merely emits an
envelope.

### F1 wall delta after source retention

The same target file lists were rerun after the property metadata route landed.
The change removes SVA process refusals without changing any other admission
rule:

| target | unsupported nodes before | retained properties | unsupported nodes after |
|---|---:|---:|---:|
| `prim_fifo_sync` | 46 | 9 | 37 |
| `prim_arbiter_ppc` | 26 | 15 | 11 |
| `prim_packer` | 32 | 12 | 20 |

The remaining first causes are parameterized unpacked ports and arrays,
explicit casts, procedural loops, and unresolved primitive dependencies. They
are the loader work that can unblock the next OpenTitan F1/F2 target; property
members are no longer the first executable-process wall.

The first array packet retains parameter-dependent unpacked declarations as
`UnpackedDecl` with symbolic bounds. The flat scalar store does not fabricate
default-point cells. The one-rank sequential memory packet now routes that
retained source form through `MemDesign2` and `MemState` instead.

The first E memory packet is now present in `LeanModels.Sv.Kernel.CoreMem`.
`MemShape` retains the source labels and element width, `MemBlock` stores
array-valued cells without expansion, and `MemState` names memory objects.
Read and write laws cover same-cell updates, other-cell preservation,
out-of-range reads and writes, and unknown memory names. `Kernel/MemElab`
now evaluates a retained one-rank `UnpackedDecl` at a parameter point and
constructs its native memory state; nested ranks remain a named refusal. The
`Kernel/MemCycle` view admits the clean one-rank FIFO shape with scalar
conditions, direct cell RHSs, scalar or cell NBAs, and a continuous scalar
assign from a cell. Its refinement target is the E memory state; the legacy
`run2` route remains unchanged for scalar designs.

`MemElab` now resolves one-rank `PLhs.arrayElem` targets against source labels
and delegates their reads and writes to `MemState`, with guards for an updated
cell and an out-of-range all-x/no-op access. Dynamic indices, partial array
targets, and process scheduling remain explicit boundaries. `Kernel/MemProc`
now carries those targets through a source-shaped NBA queue and commits them
through `MemState`; scalar RHS evaluation and direct cell reads are covered by
kernel guards, while compound memory expressions remain loud. The
`async_mem_fifo` clean-room fixture is differentially matched against Icarus
over reset, write, and read cycles.

The clean-room `sem2/unpacked_register_memory` fixture extends this route to a
parameter-sized register file with run-time read and write indices. The
symbolic envelope retains both `ArraySel` operations; E evaluates known
indices against `MemState`, returns all-x for an unknown read, and drops an
unknown or out-of-range write. Its three-cycle trace matches Icarus. Nested
memories, compound memory expressions, and hierarchy remain loud.
The PicoRV32 R2 item is now started from the re-probe's generic walls. A
source-shaped `always_comb` memory read is admitted after the sequential
`MemState` commit; `sem2/unpacked_memory_comb` covers this exact form. The
memory route still refuses unsupported module members such as `net-z` wires.
The generic undriven-wire boundary remains source-shaped metadata: a plain
four-state `wire` with no driver is retained in `pdesign.others`, and the
memory route keeps its named unsupported-member refusal until net resolution is
represented. `sem2/unpacked_memory_netz` guards this behavior.
The item-2 clean-room PicoRV32 wall pair is pinned under
`Examples/system-verilog/cores/picorv32/walls`: `unpacked_cpuregs` checks the
ordinary unpacked-memory refusal, while `net_z_memory` checks the memory-route
unsupported-member refusal and `NetSymbol:net-z` metadata. `walls/probe.lean`
checks both exact messages.

### Initial ROM loading remains an explicit F4 boundary

The clean-room `sem2/readmemh_rom` fixture measures the next memory wall:
`initial $readmemh("rom.hex", rom)` is retained in the envelope and becomes a
named `ProceduralBlockSymbol:Initial` refusal in `PDesign` and `Design2`.
The generated ROM cells and the combinational `rom[addr]` read remain visible,
so the loader does not invent time-zero contents from the file. This row is
loud in
`harness/sv/cases2.json`; admitting it requires initial-process scheduling and
file-loading semantics in E, followed by a differential witness.

## Ladder

### F1 — SVA safety fragment in E (clause 16)

**Started 2026-11-04:** `LeanModels.Sv.Sva` provides the retained, fuel-free
predicate over clocked Preponed samples for the finite safety core.
Concurrent assertion members now stay in the symbolic envelope's `properties`
metadata instead of becoming runnable `NoEventControl` processes. The clean
`sva_property_retained` witness loads its async-reset process and retains one
assert, one assume, and one cover property. OpenTitan's own files still have
independent walls (unpacked ports, casts, arrays, and simulator SVA support),
which remain in the measured census. Its three-cycle property stimulus passes
through Verilator 5.052 with assertions enabled; Icarus remains unavailable
for concurrent SVA syntax.

The E route proves `clockSamples_final_irrel` and
`evalRegion_final_irrel`: changing a slot's post-NBA/final state cannot change
an assertion result, because concurrent properties consume only the Preponed
sample. This is the first refinement fact for exposing E's sampled cycle view
to property contracts.

`LeanModels.Sv.SvaContract` connects retained `PProperty` metadata to a
structured `SvaCheck` and the observation model's `Safe` judgment. It checks
the source assertion kind and clock, preserves the source text, and maps
trusted pre/post port samples into the E slot view. The structured body is
supplied explicitly at this boundary; forms outside the finite F1 vocabulary
remain loud until their parser and contract rule are added.

`SvaContract.parseSimple` now supplies the first source parser rule for
`assert/assume/cover property (@(posedge clk) a |-> b);` and its non-overlapped
`|=>` twin. It checks the retained kind and clock and admits only simple signal
operands; delays, reset guards, and richer expressions remain explicit parser
refusals. Exact `##n` delays are now mapped to the finite `SvaSeq.delay`
fragment, and finite `##[m:n]` ranges map to `SvaSeq.range`; dynamic delays
remain explicit refusals. Simple `$past(signal)` maps to the sampled
`SvaBool.past` form, and `$rose(signal)` maps to `SvaBool.rose`.
`$fell(signal)` maps to `SvaBool.fell` as well.
`$stable(signal)` maps to `SvaBool.stable`.
Simple `disable iff (reset)` guards map to `SvaProp.disable`.
Simple boolean conjunctions and disjunctions map to `SvaBool.and` and
`SvaBool.or`.
Simple case equality (`a === b`) maps to `SvaBool.caseEq`.
Simple boolean negation (`!a`) maps to `SvaBool.not`.
The retained `cover property` spelling is directly guarded through the same
source-to-contract parser.
The corresponding `assume property` spelling is guarded through the same path.
Unbased unsized SVA literals (`'0`, `'1`, `'x`, and `'z`) are retained as
width-directed fills in the expression tree. The clean-room
`sem2/sva_unbased_literal` witness checks a passing and a failing sampled
trace; the source also passes Verilator's assertion-capable lint path.
On the pinned OpenTitan `prim_fifo_sync` assertion VIP, the same adapter keeps
all 27 assertion properties in metadata and removes its 27
`UnbasedUnsizedLiteralExpression` refusals; 29 unrelated loader nodes remain
for later target-enabling packets.
Parenthesized property expressions now unwrap before implication and sequence
classification; the same VIP's residual census falls to 18 nodes without
losing any retained property.
Logical implication (`->`) and equivalence (`<->`) inside finite property
expressions now map to the existing four-state boolean layer. The clean-room
`sem2/sva_logical_ops` witness covers both a passing and failing trace, with a
Verilator differential row. The pinned VIP census falls to 15 residual nodes;
the four remaining invocation nodes are `$past` values nested inside arithmetic
comparisons and remain the next expression wall.
The finite value route now retains `$past` inside equality and arithmetic
expressions, with previous-sample lookup performed before the arithmetic fold.
The clean-room `sem2/sva_past_value` witness and Verilator row cover both
`depth == $past(depth)` and `depth == $past(depth) + 1`; the VIP census falls to
11 residual nodes, all outside this finite value fragment.
Finite literal `inside` sets now lower to case-equality disjunctions with
width-directed fills. The clean-room `sem2/sva_inside` witness and Verilator
row cover the admitted membership form; the VIP census falls to 10 residual
nodes, with no retained-property loss.
Qualified signal paths in SVA expressions now retain their elaborated
instance/generate spelling as one observation key (for example
`u.g.flag`). The clean-room `sem2/sva_scoped` witness and Verilator row cover
the path form; the VIP census falls to 9 residual nodes, with the remaining
walls outside the finite SVA value fragment.
Reduction operators in finite SVA expressions now use the existing `PExpr`
`Reduce` vocabulary, preserving four-state reduction semantics. The clean-room
`sem2/sva_reduce` witness and Verilator row cover reduction-OR; on the pinned
`prim_arbiter_ppc` set, property-expression refusals fall from 20 to 12 across
all 15 retained properties.
Dynamic packed element selects in SVA now retain the existing `BitSel` and
`Expr2.index` path, with declaration widths supplied from the observation
environment. The clean-room `sem2/sva_select` witness covers the sampled
selector form; the arbiter property-expression census falls from 12 to 9,
leaving only nested temporal calls and a shift expression.
Indexed packed part-selects (`base +: width` and `base -: width`) now retain
their source-shaped `PartSel` bounds, and sized based literals retain their
declared width and x/z digits in the existing literal node. The clean-room
`sem2/sva_indexed_part` witness covers both forms. On the pinned `prim_packer`
set, its four dynamic-selector and four integer-vector property walls are
removed; the remaining property nodes are outside this finite fragment.
Boolean conjunction, disjunction, and negation now recurse through structured
SVA leaves, so a finite `$past` operand remains a sampled `SvaPast` node inside
the boolean tree. The clean-room `sem2/sva_past_logic` witness covers the
conjunction form; the remaining arbiter invocation walls are system calls,
arithmetic temporal terms, and shifts. The arbiter property-expression census
falls from 9 to 6, with five system-call invocations and one shift remaining.
`$isunknown(expr)` now maps to an explicit sampled knownness predicate that
returns true exactly when the evaluated vector contains x/z. The clean-room
`sem2/sva_isunknown` witness covers the form; the arbiter census falls from 6
to 3, leaving `$onehot0` and two other system-call boundaries plus the shift.
`$onehot0(expr)` now maps to a finite four-state predicate: known vectors pass
when at most one bit is one, while unknown vectors pass only when no more than
one known one exists and no unknown can make the count exceed one. The clean
`sem2/sva_onehot0` witness covers the admitted form; the arbiter census falls
from 3 to 2, leaving one shift and one other invocation.
`$countones(expr)` now maps to a sampled four-state known-one count, with x/z
bits contributing zero as required by the SVA bit query. The clean-room
`sem2/sva_countones` witness and Verilator row cover the retained value form.
On the pinned `prim_packer` set, the eight `$countones` invocation walls are
removed from the property AST; eight unrelated property nodes remain outside
the finite value fragment.
Sampled order comparisons (`<`, `<=`, `>`, `>=`) now retain temporal operands
as `SvaValueCmp` and evaluate them at the sampled width. The clean-room
`sem2/sva_past_cmp` witness covers `a > $past(b)`; the arbiter remains at two
independent walls for the parameter-sized cast and one system invocation.
Fixed-width shift expressions now use the existing sampled value-binary path.
The clean-room `sem2/sva_shift` witness covers `a << 1`; the parameter-sized
`N'(1)` cast in the arbiter remains loud because its width context is not yet
represented in the SVA environment.

F1 acceptance for the first pinned target is now measured: the current
`prim_fifo_sync` extraction retains all 27 assertion properties and contains
zero `Unsupported` nodes inside their structured property ASTs. Its remaining
9 nodes are design-level loader boundaries outside the property set.

F1 keeps the four-state sampled value until the assertion boundary. IEEE
1800-2023 §16.6 then converts an x/z-only boolean result to false; an unknown
value is never turned into a true result by `!`, `$past`, or `$stable`. Missing
signals, unsupported expression evaluation, and timing failures remain named
`SVA:` errors. `$rose` and `$fell` use the sampled-value edge table, with the
first sampled tick forced false because it has no preceding sampled value.

#### Downstream clean-room wall audit

The first downstream clean-room repros put the remaining target blockers in
this order:

| rank | source shape | measured boundary |
|---:|---|---|
| 1 | `always @(posedge clk)` | **Resolved in this packet:** `SeqProfile.ffOnlyProfileB` now admits a plain edge-triggered `always` when its body is NBA-only, while `Process2.alwaysPlain` preserves the source kind. The retained profile has a kernel guard and an Icarus differential row. |
| 2 | `always_ff @(posedge clk or negedge rstn)` | **Resolved in this packet:** `ffResetProfileB` admits the retained `Process2.alwaysFFR` shape, and `resetPass2_ffResetOnly` bridges selected reset events to source-shaped NBA updates. Kernel guards cover assertion and release; the differential row matches Icarus over five cycles. |
| 3 | an unpacked memory written in `always_ff` | **Resolved in this packet:** one-rank parameter-sized memories retain `UnpackedDecl` and `ArraySel`, then run through `MemState`/`MemCycle` without expansion. Nested ranks, loops, partial targets, and compound memory expressions remain loud. |
| 4 | one module instance | `sv_structure` refuses hierarchy because the combinational tactics do not summarize instances yet. |
| 5 | a user function in a combinational expression | **Resolved in this packet:** the extractor's pure automatic input-only function path inlines return expressions and straight-line local temporaries, including plain and statically safe qualified `case` over an argument. Qualified claims require distinct concrete labels and a `default`; dynamic, overlapping, and incomplete forms remain loud. The `function_case_eval` and `function_unique_case_eval` witnesses match Icarus; side effects, loops, recursion, static functions, tasks, and unsupported bodies remain loud. |
| 6 | `assign n = d` beside an async-reset `always_ff` | **Resolved in this packet:** `ffResetProfileB` admits comb processes before/after the retained reset process, while `ffMixedProfileB` covers the corresponding no-reset profile. `cycleStep2_mixedProfile` settles comb logic before reset, edge/NBA, and final settle under an explicit acyclic-comb settle contract. The `async_reset_comb_profile` witness matches Icarus over five cycles. |
| 7 | `initial $readmemh(...)` ROM initialization | `sv_structure` refuses `ProceduralBlockSymbol:Initial`; initial-process semantics remain a named boundary. |

The F4 clock rung now has an exact E instant route. `ClockInstant.rises` is a
set of simultaneous input-clock edges and `runMulti` commits all selected
edge-process NBAs together, so a coincident edge observes old values. The
legacy one-clock harness transport still records `Clock:multiple` until its
stimulus schema carries instant lists.

The same audit exercises the F1 property forms. Finite concurrent assertions,
bounded ranges, and assumptions with `disable iff` load with their retained
metadata and connect to `SvaContract`; the finite assert and assumption forms
also pass the source parser's kernel guards, including `$rose`, `$past` with a
finite depth, and `$stable`. A bare cover sequence such as
`cover property (@(posedge clk) req ##[1:3] ack);` remains loud with the parser
reason `expected posedge implication form`: the current E contract vocabulary
requires an implication around a sequence. Immediate assertions remain outside
the finite concurrent-property envelope, and `s_eventually` remains an
unbounded liveness operator outside F1 by design. These boundaries preserve a
named refusal until their E meaning and refinement rule exist.

Assertions nested in a constant generate scope are retained in the same module
metadata list, with the structural generate body left empty for executable
processes. Their lexical generate labels are now carried in each property's
`path`; generated instance indices remain a hierarchy-contract concern.

The E-core-1 async-reset edge packet is also in place for the first target
shape: kernel guards cover reset assertion and release, the `1 -> x` and
`x -> 0` reset edges, and a clock edge while reset is asserted. The seven-cycle
`clk_arst_reset_edges` witness matches Icarus; the existing Xcelium golden
`clk_arst` row covers the same reset phase. This closes the edge-table proof
wall while the target files still have independent array, cast, loop, and
primitive-dependency refusals.

The loader soundness boundary is now explicit as well: active-high `areset`
is retained in E with its polarity, while negative-edge clocks and `iff`
guards remain named refusals rather than silently being read as positive-edge
`alwaysFF`. No target census counts a silently reinterpreted process as loaded.

The E edge primitive now carries a `ClockEdge` selector, defaulting to
`posedge` and supporting the IEEE four-state `negedge` predicate with kernel
guards. The source loader and clocked observation harness still keep negative
edge process forms at their named boundary until their full source-shaped
process path is wired.

Admit concurrent `assert`, `assume`, and `cover` properties with clocking and
`disable iff`; the boolean layer; `|->` and `|=>`; `##n` and bounded
`##[m:n]`; `$past`, `$rose`, `$fell`, and `$stable`. Their meaning is a trace
predicate over E's cycle semantics, with sampling delegated to the kernel's
named rule. Unbounded and liveness operators remain loud initially.

Every admitted construct gets a differential witness: simulator assertion
outcomes and a formal-tool verdict on a clean fixture. F1 is complete when the
FPV assertion set of one pinned OpenTitan primitive, starting with
`prim_fifo_sync`, loads as Lean propositions about that RTL. `prim_arbiter_ppc`
and `prim_packer` are the next F1 targets after the first wall is measured.

### F2 — unbounded safety from reset and counterexample replay

Provide an inductive-invariant route. The base case and one-cycle step are
discharged by symbolic E evaluation plus `bv_decide`, `omega`, or
`sv_exhaustive`. A concrete BMC or simulator trace is replayed through E to
prove a failed property false. The target is every FPV assertion of two
OpenTitan primitives, proved or refuted as written, with assumptions and reset
conditions preserved.

### F3 — structural composition

Use E-core-2's hierarchy and per-instance contracts. Prove a submodule once,
assume its contract at the parent, and discharge an assume-guarantee
composition theorem. Proofs keep the instance structure; flattening is not a
substitute for composition. The target is a complete public `uart` or
`spi_host` peripheral, including its assertions and one functional property.

### F4 — memories, clocks, and scale

Model SRAM macros and large unpacked arrays as abstract memories, beginning
with `prim_ram_1p` and a contract. Add asynchronous resets and multiple clocks
through the CDC primitives. The performance bar is an invariant-step proof for
a design with at least 10,000 flops within the slot budget.

### F5 — a whole small public SoC

Prove selected end-to-end properties from reset on a small public SoC. The
property set, environment assumptions, trace horizon, and any refutation must
remain explicit and kernel checked.

## Working rule

Qualified-case diagnostics are attached to process execution rather than
post-trace snapshots; `sem2/qualified_case_timing` pins pre-edge and
post-edge-created violations.

The Wally items (casts, instances, `ifndef`, `'x`, loop variables, and structs)
remain on the critical path whenever they unblock an F1–F3 target. Other
loader work waits behind the target census. Each rung records its before/after
refusal census, adds differential rows, and lands only with a theorem or a
loud named boundary. SVA properties are never silently treated as comments or
plain procedural statements.
