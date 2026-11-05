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
`UnpackedDecl` with symbolic bounds. The current flat E store refuses this
node with `UnpackedDecl:memory`; no default-point cells are fabricated. The
array-valued memory state needed by F4 is the next packet for this boundary.

The first E memory packet is now present in `LeanModels.Sv.Kernel.CoreMem`.
`MemShape` retains the source labels and element width, `MemBlock` stores
array-valued cells without expansion, and `MemState` names memory objects.
Read and write laws cover same-cell updates, other-cell preservation,
out-of-range reads and writes, and unknown memory names. `Kernel/MemElab`
now evaluates a retained one-rank `UnpackedDecl` at a parameter point and
constructs its native memory state; nested ranks remain a named refusal. The
process evaluator still stops at `UnpackedDecl:memory` until array targets are
wired into the edge evaluator.

`MemElab` now resolves one-rank `PLhs.arrayElem` targets against source labels
and delegates their reads and writes to `MemState`, with guards for an updated
cell and an out-of-range all-x/no-op access. Dynamic indices, partial array
targets, and process scheduling remain explicit boundaries. `Kernel/MemProc`
now carries those targets through a source-shaped NBA queue and commits them
through `MemState`; scalar RHS evaluation and direct cell reads are covered by
kernel guards, while compound memory expressions remain loud.

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

The Wally items (casts, instances, `ifndef`, `'x`, loop variables, and structs)
remain on the critical path whenever they unblock an F1–F3 target. Other
loader work waits behind the target census. Each rung records its before/after
refusal census, adds differential rows, and lands only with a theorem or a
loud named boundary. SVA properties are never silently treated as comments or
plain procedural statements.
