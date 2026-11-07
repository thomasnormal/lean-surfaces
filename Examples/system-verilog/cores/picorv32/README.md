# PicoRV32 R2 integration status

PicoRV32 is the first R2 candidate selected by the admission census.  The
source is YosysHQ's `picorv32` repository at commit
[`ef203c2b0a3fb793280f5114941416c425c5b461`](https://github.com/YosysHQ/picorv32/commit/ef203c2b0a3fb793280f5114941416c425c5b461),
under the ISC license (`COPYING`).  The pinned source tree was cloned
read-only; no RTL adaptation was made.

The current symbolic envelope was generated from the single upstream
`picorv32.v` source with:

```text
python3 extractors/sv/extract.py --top picorv32 \
  -o /tmp/picorv32-ls-current.sv.json /tmp/picorv32-ls/picorv32.v
```

Its SHA-256 is
`009cc39591b3fcb1c88403ca44f822cb1854d2ebc0b5c728c7cade06a2e47b1b` and its
size is 3,178,052 bytes.  The envelope has one module, 26 parameters, 216
declarations after parsing, 43 process entries and three generate entries.

At the pinned default parameter point, the loader declaration succeeds, but
the semantic family is loud:

```text
picorv32_current.sem defaults: hasUnsupported = true
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The default argument list, in source order, is
`[1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
4294967295, 0, 16, 4294967295]`.  The source envelope contains 70 static
unsupported nodes; the most common classes are unsized/XZ parametric literals
(16), call expressions (13), width conversions (11), net-z ports (8), and
assignment targets (6).  These counts are telemetry, not admitted semantics.

The existing one-rank memory adapter can inspect the same `PDesign`, but its
current source-shaped route reports the next generic wall before constructing a
memory design:

```text
memory cycle route does not yet admit generate members
```

This packet therefore does not claim an R1 refinement theorem for PicoRV32.
The exact memory wall is already requested from the owner lane in
`/var/tmp/thomas-ahle/fleet2/inbox/ls-sv.md` (the 2026-11-05 R2 request and
the parameter-sized-array follow-up).  Once that generic route is integrated,
the generated members and the remaining source-shaped process forms must be
re-measured before core-specific proof glue is added.

## Re-probe after the generic memory route

On 2026-11-05, the unchanged pinned envelope was re-probed against
`origin/master` at `38288d414` (which includes the generic one-rank memory
adapter).  The normal semantic family still reports exactly the
`cpuregs` unpacked-memory wall above, and
`pdesign.instantiateMemD2` still returns
`unsupported "Instantiate" "memory cycle route does not yet admit generate members"`.
The route has therefore not silently advanced past the source's generate
members; no core-specific proof was started.  The CV32E40P and Ibex probes
were also rerun from their pinned envelopes: their first loader diagnostics
remain `AlwaysPosedge:edge` and `AlwaysLatch`, respectively.  These are
measurements of the current tool, not adaptations of any upstream RTL.

## Generated-member clean-room repro

The next wall is independent of PicoRV32's source.  The clean-room fixtures
[`generate_memory_if.sv`](generate_memory_if.sv) and
[`generate_memory_for.sv`](generate_memory_for.sv) combine a one-rank unpacked
memory with a source-shaped `generate if` or `generate for`.  Their approved
envelopes are checked by [`generate_memory_if_probe.lean`](generate_memory_if_probe.lean)
and [`generate_memory_for_probe.lean`](generate_memory_for_probe.lean): the
loader declaration succeeds, while
`pdesign.instantiateMemD2 [4]` reduces exactly to
`unsupported "Instantiate" "memory cycle route does not yet admit generate members"`.
These fixtures are generic repros for the owner lane; they do not alter or
lower the pinned PicoRV32 RTL.

## RVFI and memory-port witness

The unchanged source also exposes an RVFI port under `RISCV_FORMAL`.  The
clean-room harness [`rvfi_probe.v`](rvfi_probe.v) drives the real memory port
with `mem_ready = 1` and runs this five-instruction program:

```text
addi x1, x0, 5
sw   x1, 0x100(x0)
lw   x2, 0x100(x0)
addi x3, x2, 1
ebreak
```

Compile it against the pinned source (without modifying that source) with:

```text
iverilog -g2012 -DRISCV_FORMAL -s tb_picorv32_rvfi \
  -o /tmp/picorv32_rvfi_tb <PINNED_PICORV32>/picorv32.v \
  Examples/system-verilog/cores/picorv32/rvfi_probe.v
vvp /tmp/picorv32_rvfi_tb
```

Icarus Verilog 13.0 and Verilator 5.052 produced the same five RVFI rows.  The
first four are the non-trapping RV32I stream (orders 0 through 3); the fifth is
the `ebreak` row with `trap=1`.  The rows include `sw`'s `wmask=f` and data 5,
then `lw`'s `rmask=f`, address `0x100`, and data 5.  The Lean witness
[`rvfi_proof.lean`](rvfi_proof.lean) normalizes all five rows through
`RvfiObservation.toRetirement?` after explicitly annotating the trap with
`Cause.breakpoint`; it also proves that the raw trap row without that
proof-side annotation is refused.  This validates the RVFI observation
boundary against two simulators; it does not bypass the loader's
unpacked-memory/generate wall or claim a core refinement theorem.  The same
Lean witness also checks that all five observed instruction words decode to
the expected RV32I/system constructors in `LeanModels.Rv`.

The witness also feeds the complete list to `normalizeRvfiTrace? 0`.  This
order-aware checker treats `valid = false` rows as bubbles, requires each valid
row to carry the next consecutive `order`, and refuses a valid row that does
not normalize to a semantic retirement.  The pinned five-row list produces
`some expected`; a two-row list with the second order changed to 3 produces
`none`, so the boundary never sorts or silently drops an out-of-order commit.

The reusable raw `ADDI` contract in `LeanModels.Refine.RvfiAddi` keeps the
wire-level facts alongside the semantic equality: the fetched 32-bit word must
decode as `ADDI`, `pcWdata` is exactly `pcRdata + 4`, the `rs1` read and `rd`
writeback carry the ISA values, trap and data-memory masks are clear, and the
row's `toRetirement?` is the corresponding `addiRetirement`.  The concrete
reset-state witness [`rvfi_addi_boundary.lean`](rvfi_addi_boundary.lean)
applies this predicate to PicoRV32's measured `addi x1, x0, 5` row and also
checks x0 and memory preservation.  It remains a boundary certificate for the
measured stream; the same witness now derives the exact `isaStepMemWith` result
and the `rvMachineWith` commit from the raw predicate, while the symbolic RTL
proof still waits on the generic loader wall.

The raw ADDI predicate also has a stateful-machine bridge.  The reset and
post-prefix witnesses use `RvfiObservation.addiBoundary_rvMemoryMachineWith`
to show that the row's commit leaves its explicit byte-memory state unchanged
while producing the exact `addiNext` architectural state and retirement.
`rvfiCycleStepRefines_of_addi_memory` lifts that boundary to a strict
cycle-level invariant over `RvMemoryState`: it requires the cycle input's
memory view to equal the threaded architectural memory, then carries the
updated architectural state and unchanged memory through the relation.  This
keeps the memory equality visible at the point where a loaded-core proof will
consume it.

The generic RVFI layer now also exposes `RvfiCycleStepRefines`.  Its valid
cycle branch requires the raw observation to normalize to a retirement that
matches the ISA step; a malformed valid row cannot be silently projected to a
bubble.  `rvfiCycleStepRefines_toCycleStepRefines` transports this strict raw
contract to the existing cycle bridge, so a loaded-core invariant can be
proved against packed fields first and use the trace/state theorems afterward.
`rvfiCycleStepRefines_valid_step` projects a valid cycle to the row's
`wellFormed` proof, post-cycle relation, and equality between the concrete
packed retirement and the ISA retirement.  It is the direct raw-row boundary
for a loaded-core invariant and does not infer validity from the optional
adapter.
The dual `rvfiCycleStepRefines_invalid_step` projection exposes an invalid
row as an explicit bubble and carries the relation while the ISA stutters.
The combined `rvfiCycleStepRefines_step` projection dispatches every raw cycle
to exactly one of those two branches, retaining the validity bit alongside
the corresponding well-formed retirement or stutter relation.
Its dual constructor `rvfiCycleStepRefines_of_step` packages the same
exhaustive case split into the strict contract, including the valid row's
existential optional-retirement witness.
The reverse bridge `cycleStepRefines_to_rvfiCycleStepRefines_of_rel` lifts an
existing optional `CycleStepRefines` proof when a separate wire invariant
proves every valid raw row well formed on related, admitted states.  The global
specialization `cycleStepRefines_to_rvfiCycleStepRefines` is available when a
stronger all-state premise is convenient.  Both premises are explicit:
without one, the optional adapter could hide a malformed valid row as a bubble.
Under this invariant, `cycleStepRefines_iff_rvfiCycleStepRefines_of_rel`
packages the two directions as an equivalence, so a loaded-core proof may
choose the optional or raw contract without changing its wire obligations.
The global-row `cycleStepRefines_iff_rvfiCycleStepRefines` specialization remains
available for callers with the stronger premise.
The equivalence `rvfiCycleStepRefines_iff_step` exposes this case split as the
canonical packed-field statement of the strict contract.
The companion `rvfiCycleStepRefines_trace_refines` and
`rvfiCycleStepRefines_stateAfter_refines` wrappers expose those trace and
post-window-state results directly from the strict contract.
`rvfiCycleStepRefines_normalized_trace_refines` composes the strict contract
with a successful raw `normalizeRvfiTrace?` certificate, yielding the
normalized retirement list's equality with the ISA trace.  The conditional
`pinned_cycle_normalized_trace_refines_of` witness fixes that composition on
the measured eight-cycle window; its hypotheses are exactly the future
loaded-core invariant and input-admission obligations.
`normalizeRvfiTrace?_wellFormed` independently classifies every row in a
successful raw certificate as either an invalid bubble or a well-formed valid
row, without using the optional-adapter theorem.
`normalizeRvfiTrace?_eq_none_iff` gives the failure-side companion: a `none`
result is exactly the absence of any order/decode certificate, so malformed
valid rows and order gaps cannot be reinterpreted as an empty stream.
`RvfiTraceRefines.functional` closes the corresponding success-side ambiguity:
the same raw observation window and starting order cannot certify two different
retirement lists.  A loaded-core proof may therefore transport a certificate
without choosing between competing normalized streams.
At the single-row adapter boundary,
`RvfiObservation.toRetirement?_eq_some_iff` characterizes a successful decode
as `valid ∧ wellFormed` together with equality to the observation's concrete
retirement, so callers can invert or introduce the option without reopening
its executable branches.
The companion `RvfiObservation.toRetirement?_eq_none_iff` records the other
outcome: `none` means either an invalid bubble or a malformed row, so a strict
contract must still carry the separate well-formedness obligation.
`normalizeRvfiCycleTrace_input_length` additionally proves that a successful
normalization has exactly as many retained retiring inputs as decoded
retirements, and `pinned_cycle_normalized_input_length` records that count for
the measured window.
The bundled `rvfiCycleStepRefines_normalized` theorem exposes the trace and
post-window relation together; `pinned_cycle_normalized_refines_of` fixes that
pair on the same measured machine while leaving the actual invariant as its
premise.
For an invariant already stated against the optional cycle adapter,
`cycleStepRefines_normalized_trace_refines` composes the raw well-formedness
premise and normalization certificate directly into the same ISA trace
equality, without requiring callers to rebuild the strict contract by hand.
`cycleStepRefines_normalized_of_rel` exposes that equality together with the
carried post-window relation while restricting the wire invariant to related,
admitted states.  The global-row `cycleStepRefines_normalized` specialization
remains available for the stronger premise.
`cycleStepRefines_normalized_append_of_rel` carries the paired result across
adjacent optional windows while restricting the wire invariant to related,
admitted states.  The global-row `cycleStepRefines_normalized_append`
specialization remains available, including the exact raw-state boundary
between windows.
`cycleStepRefines_normalized_chain_of_rel` additionally exposes the
intermediate relation and second ISA state needed to resume a segmented
optional proof while keeping the wire invariant reachability-sensitive.  The
global-row `cycleStepRefines_normalized_chain` specialization remains
available.
`rvfiCycleStepRefines_normalized_append` carries the same pair across adjacent
normalized windows, and `pinned_cycle_normalized_append_refines_of` exercises
the first/second measured window split with its carried order offset.
`rvfiCycleStepRefines_normalized_chain` additionally exposes the relation at
that boundary and the second window's ISA state, while
`pinned_cycle_normalized_chain_refines_of` instantiates those four segmented
facts on the same measured split.

`rvfiCycleStepRefines_of_addi` is the first instruction-class constructor for
the strict raw-cycle contract.  Given a core relation and admission predicate,
it packages an invariant whose valid rows satisfy `addiBoundary` and advance
the ISA through `addiNext`, while invalid rows carry the relation across an
ISA stutter.  The profile, core relation, and input admission remain explicit,
so a future loaded-core proof can discharge the ADDI row case without
reconstructing the packed valid/invalid dispatch.
The companion `rvfiCycleStepRefines_of_sw` applies the same strict dispatch to
the measured store class: valid rows use `swBoundary`, advance through
`swNext`, and agree with `swRetirement`, while invalid rows remain bubbles.
`rvfiCycleStepRefines_of_lw` completes the three-instruction memory prefix:
valid rows use the input-memory-sensitive `lwBoundary`, advance through
`lwNext`, and agree with `lwRetirement`, with malformed valid rows still
excluded by the strict contract.

The witness also reconstructs the measured `ADDI x3, x2, 1` row after the
`ADDI/SW/LW` prefix.  It retains the source fields (`rs1_addr = 2`,
`rs1_rdata = 5`), proves the threaded architectural state has `pc = 12`,
`x2 = 5`, and `x0 = 0`, and applies the same raw-to-ISA step bridge at that
non-reset boundary.

[`rvfi_sw_boundary.lean`](rvfi_sw_boundary.lean) applies the corresponding
profile-parametric raw boundary to the measured `SW x1, 0x100(x0)` row.  Its
`RvfiObservation.swBoundary` predicate checks both source reads, the word
write mask and payload, the effective address, and the absence of a register
write or trap.  The state-threaded witness starts after the first ADDI and
derives the exact `storeVal` memory transition and `swRetirement` commit.

[`rvfi_lw_boundary.lean`](rvfi_lw_boundary.lean) completes that prefix with
the measured `LW x2, 0x100(x0)` row.  `RvfiObservation.lwBoundary` checks the
word read mask, address and returned data, the source read and destination
writeback, and the unchanged memory result.  Its witness threads the state
through the first two instructions and consumes the explicit memory view
where address `0x100` contains 5.

The store and load witnesses now also apply their raw predicates directly to
`rvMemoryMachineWith`: the store produces the exact `storeVal` memory update,
while the load retains the supplied byte memory.  Both stateful commits keep
the raw RVFI row and the architectural memory transition in one theorem.

The generic `rvfiCycleStepRefines_of_memory_step` constructor exposes the
stateful raw boundary without fixing an instruction family.  A valid row must
show input-memory equality, `wellFormed`, its concrete retirement, the exact
`rvMemoryMachineWith` step, and the related post-state; invalid rows remain
explicit stutters.  The ADDI/SW/LW constructors below specialize this contract
with their decoded wire predicates.

The `RvfiObservation.luiBoundary` predicate and
`rvfiCycleStepRefines_of_lui_memory` add the same stateful contract for RV32I
LUI.  Its raw fields identify the decoded U-immediate operation through the
explicit x0 source read, require the no-memory/no-trap RVFI facts, and tie the
row to `luiRetirement`.  The valid cycle case advances the threaded
`rvMemoryMachineWith` state through `luiNext` while preserving byte memory;
invalid rows remain explicit ISA stutters.

The generic `rvfiCycleStepRefines_of_sw_memory` constructor now lifts the
store boundary to the same threaded-memory contract as ADDI.  A valid row must
show that its input memory view is the current architectural memory, satisfy
`swBoundary`, and carry the relation to the exact `storeVal` update and
`swRetirement`; invalid rows remain explicit ISA stutters.  The raw memory
equality therefore stays visible at the point where a loaded-core invariant
consumes the store case.

The companion `rvfiCycleStepRefines_of_lw_memory` constructor lifts the load
boundary as well.  Its valid case requires the same input-memory equality and
`lwBoundary`, then carries the relation through `lwNext` with the loaded value
and unchanged byte memory, matching `lwRetirement`; invalid rows remain
explicit ISA stutters.  This completes the threaded-memory constructors for
the measured ADDI/SW/LW prefix.

The prefix witness bundles all four raw RVFI predicates with their four
stateful-machine commit equations in `pinned_raw_stateful_window_certificate`.
This is the concrete window certificate a future loaded-core invariant can
consume without choosing between the wire-level and stateful premises.

[`rvfi_prefix_boundary.lean`](rvfi_prefix_boundary.lean) also runs the
first three non-trapping instructions through `rvMemoryMachineWith`.  It
proves the concrete threaded state (`pc = 12`, `x2 = 5`, `x0 = 0`) and the
pointwise equality of its memory with `memFive`, making the state consumed by
the later `ADDI x3, x2, 1` witness explicit.

The same witness extends that state through the fourth `ADDI` in `fullState`:
the final `pc` is 16, `x2` remains 5, `x3` is 6, `x0` remains 0, and the
threaded memory is still `memFive`.

The prefix witness now also exposes the full-window endpoint through the
stateless adapter's `machineStateAfter` on the memory views produced by
`threadRvInputs`.  Its `pinned_full_window_trace` theorem checks that the
stateful machine emits exactly the four measured non-trapping retirements, and
`pinned_full_window_observed` connects the normalized RVFI observations to
that stateful trace.  Thus the final state and observed commit stream share
one four-instruction certificate; no symbolic RTL refinement is claimed until
the generated-memory loader wall is removed.

## Finite ISA trace witness

[`trace_proof.lean`](trace_proof.lean) feeds the first four non-trapping RVFI
rows to the R1 `rvMachine` adapter with explicit byte memories: the store is
followed by a load response of 5 at address `0x100`.  The axiom-free theorem
`pinned_nontrap_trace_refines_isa` proves that this measured retirement stream
equals the ISA trace, including the register writes and memory effects.  The
`ebreak` row remains in `rvfi_proof.lean` but is deliberately outside this
equality: the measured core reports `pcWdata = 16` on the trap, while the
architectural model enters `mtvec = 0`.  This is a visible RVFI/ISA contract
boundary, not a guessed correction or a whole-core refinement claim.

`pinned_nontrap_observed_trace_refines_isa` composes the order-aware RVFI
certificate with that ISA calculation.  Its left side is the normalized
measured stream and its right side is the finite architectural trace, so this
is the direct observation-to-ISA bridge for the four-row witness.

The same proof file defines the two measured data requests (`SW` at `0x100`
followed by `LW` at `0x100`) and proves their effects with the generic
byte-addressed `directRun` memory contract.  The resulting write of 5 and load
of 5 are checked independently of the packed RVFI row conversion.

It also places the four valid rows into an eight-cycle `RvfiCycleMachine` with
an invalid observation before each retirement.  The cycle bridge proves that
the four bubbles disappear, the retained inputs are exactly the four measured
instruction inputs, and the filtered cycle trace equals the same finite ISA
trace.  This is a finite stuttering witness for the RVFI cycle boundary.

The generic `RvMemoryState` adapter is exercised on the same input list: its
state carries the byte memory across instructions, and
`rvMemoryMachine_trace` proves equality with the stateless ISA trace after
`threadRvInputs` supplies each preceding memory view.  The separate
`directRun` certificate records the concrete write/read values.

The generic RVFI normalizer is also exercised on two observation windows.  The
first ends at order 1; the second starts at order 2, and
`normalizeRvfiTrace?_append` proves that their concatenation is the same
four-row normalized stream.  This is the chunking rule a streamed RVFI capture
can use without resetting the architectural order.

