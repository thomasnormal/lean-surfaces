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

The initial one-rank memory probe was run before the generic generate-member
route landed and therefore reported the following historical wall:

```text
memory cycle route does not yet admit generate members
```

This packet therefore did not claim an R1 refinement theorem for PicoRV32.
The historical memory wall was requested from the owner lane in
`/var/tmp/thomas-ahle/fleet2/inbox/ls-sv.md`.

## Re-probe after the generic memory route

On 2026-11-05, the unchanged pinned envelope was re-probed against
`origin/master` at `38288d414` (which includes the generic one-rank memory
adapter).  That historical run still reported the `cpuregs` unpacked-memory
wall and the pre-generate route refusal.  The CV32E40P and Ibex probes were
also rerun from their pinned envelopes: their first loader diagnostics remain
`AlwaysPosedge:edge` and `AlwaysLatch`, respectively.  These are measurements
of the tool, not adaptations of upstream RTL.

## 2026-11-07 re-probe on current `github/master`

The pinned source was re-extracted with the current extractor and no RTL was
changed:

```text
source commit: ef203c2b0a3fb793280f5114941416c425c5b461
ls-sv revision: 83638b50fccf1dfe7980f2ca1ab49e1366f34ef4
envelope: 2d2d3c1b5cdd459b61a29ab38e6384db20f1f4a6cdbf5b211fe47cc2a1e785c8
size: 2,986,551 bytes
```

The declaration still loads.  At the default arguments (26 parameters, 216
declarations, 43 processes, three generate entries), the ordinary semantic
family's first refusal is unchanged:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

After rebuilding the current memory-route modules, the first memory-design
refusal is now the top-level `PDesign.others` gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is `NetSymbol:net-z` for `pcpi_mul_wr`, the
`wire` declaration at `picorv32.v:257`.  This is an existing net-z boundary,
not a new generate-member shape, so no additional `REQUEST ls-sv` repro is
filed.  The symbolic PicoRV32 invariant remains parked at these loader walls.

## 2026-11-07 re-probe after dynamic parameterized-memory admission

`github/master` advanced to `cb99d49c6` (`[ls-sv] admit dynamic parameterized
register memories`) after the previous probe.  The pinned source was extracted
again without any RTL change:

```text
source commit: ef203c2b0a3fb793280f5114941416c425c5b461
ls-sv revision: cb99d49c69db72421ab3c7b16447b47311f60890
envelope: bbdf7aee9e200a35f228adfa891eeaa10addb3b1608f3776f0bd9d61c42d4f9c
size: 2,992,406 bytes
```

The declaration still loads as a 26-parameter family (216 declarations, 43
processes, three generate entries).  The ordinary semantic family still first
refuses `cpuregs` at `picorv32.v:203` with the same unpacked-memory message.
The memory route reaches its existing top-level unsupported-member gate before
it can exercise the newly admitted dynamic register-memory path:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

Its first retained member remains `NetSymbol:net-z` for `pcpi_mul_wr`, the
`wire` at `picorv32.v:257`.  This is an existing generic boundary, so no new
clean-room request is filed and no symbolic ADDI invariant is claimed.

## 2026-11-07 re-probe on current `github/master`

The pinned source was extracted once more without any RTL change.  This probe
uses `github/master` revision `43a471fe3dc36b4b2f14fa0ef9d566c25101c962`:

```text
source commit: ef203c2b0a3fb793280f5114941416c425c5b461
envelope: bbb534099237338b0c945ef56634407d9918a03f802a3fb1e11753d920a245be
size: 2,992,422 bytes
```

The declaration still loads as a 26-parameter family.  At the default
parameters, the ordinary semantic route's exact first refusal remains at
`picorv32.v:203`:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route now reaches its existing unsupported-module-member gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

Its first retained member is still the net-z wire `pcpi_mul_wr` at
`picorv32.v:257`.  Generated members are therefore not the current wall; no
new `REQUEST ls-sv:` repro, RTL adaptation, or finite-window extension is
justified.

## Generated-member clean-room repro

The generic route is independently confirmed by the clean-room fixtures in
`Examples/system-verilog/seq_mem/gen_members`: freshly extracted envelopes
produce one memory declaration and one process for the `generate if`, and two
memory declarations and five expanded processes for the `generate for`.  The
older core-local [`generate_memory_if.sv`](generate_memory_if.sv) probe now
records its admitted assignment; the [`generate_memory_for.sv`](generate_memory_for.sv)
probe retains a separate refusal because its `wire`/default-point array shape
is still an unsupported module member.  Neither fixture alters or lowers the
pinned PicoRV32 RTL.

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

The same upper-immediate boundary now covers RV32I `AUIPC` through
`RvfiObservation.auipcBoundary` and
`rvfiCycleStepRefines_of_auipc_memory`.  AUIPC uses the architectural pc as
its first ALU operand, so its raw contract keeps the RVFI source-register
fields at zero while tying the destination writeback to `pc + imm`; the
threaded byte memory remains unchanged.

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

The jump-family boundary now covers both RV32I `JAL` and `JALR`.  The
`RvfiObservation.jalBoundary` predicate identifies the pc-relative decode,
the link writeback (`pc + 4`), and the redirected pc; its
`rvfiCycleStepRefines_of_jal_memory` constructor threads the unchanged byte
memory through the valid row.  The corresponding `jalrBoundary` contract
keeps the source-register read and the target's low-bit clearing explicit,
with `rvfiCycleStepRefines_of_jalr_memory` carrying the resulting state and
retirement.  Both constructors retain invalid rows as explicit ISA stutters.

The conditional-branch boundary now covers all six RV32I conditions through
`RvfiObservation.branchBoundary` and
`rvfiCycleStepRefines_of_branch_memory`.  The raw contract records both source
register reads, the signed or unsigned condition's selected target, and the
absence of register, memory, and trap effects.  A valid cycle advances only
the architectural pc and preserves threaded byte memory; invalid rows remain
explicit ISA stutters.

The generic ALU boundary now covers the complete decoded `.alu` family:
register-register and immediate operations, plus the LUI/AUIPC operand forms.
`RvfiObservation.aluBoundary` keeps the operation, destination, source muxes,
writeback value, sequential pc advance, and no-memory/no-trap facts explicit;
register sources are checked against the architectural state while immediate
sources carry no fictitious RVFI register read.  Its
`rvfiCycleStepRefines_of_alu_memory` constructor advances a valid row through
`aluNext` and preserves the threaded byte memory, while invalid rows remain
explicit ISA stutters.  The contract is generic over all ten RV32I ALU
operations, so a loaded-core invariant can specialize it by the decoded
operation rather than duplicating ten wire predicates.

The fence boundary covers both `fence` and `fence.i` through the explicit
`FenceKind` parameter.  `RvfiObservation.fenceBoundary` requires the decoded
system operation, sequential `pc + 4`, a valid well-formed row, and no
register, data-memory, or trap effect; unspecified RVFI register payloads are
left unconstrained because fences read and write no architectural register.
`rvfiCycleStepRefines_of_fence_memory` carries a valid row through
`fenceNext` while preserving threaded byte memory, and keeps invalid rows as
explicit ISA stutters.

The generic memory boundary now covers every RV32I byte, halfword, and word
load/store through `MemOp`.  Loads retain their signed or zero-extended result
in the architectural writeback and RVFI read data, while stores retain their
source-register data and exact width mask.  `memBoundary` connects those raw
fields to the shared `memNext`/`memAfter` equations, and
`rvfiCycleStepRefines_of_mem_memory` carries the corresponding load-preserve or
store-update through the threaded byte-memory relation; invalid rows remain
explicit ISA stutters.  The earlier `SW`/`LW` predicates remain as measured
word-width specializations.

The system-transfer boundary now covers ECALL, EBREAK, MRET, and no-wake WFI
through `SysKind`.  Its raw predicate keeps trap causes and handler pc values
for ECALL/EBREAK, the CSR-derived return pc for MRET, and the WFI stutter
explicit, while requiring no register or data-memory effect.  The
`rvfiCycleStepRefines_of_system_memory` constructor carries the exact
trap/return/stutter state through the threaded memory relation; invalid rows
remain explicit ISA stutters.  CSR read-modify-write parcels and interrupt
wake behavior remain outside this no-interrupt boundary.

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

## Unified RV32I RVFI dispatcher

`LeanModels.Refine.RvfiRv32i` unifies the raw RVFI contracts into the indexed
`Rv32iBoundary` family.  Its index is the post-`RvMemoryState` and
`Retirement`, so a loaded-core invariant retains the exact architectural
transition supplied by an ALU, branch, jump, memory, fence, system, CSR, or
trap row.  `Rv32iBoundary.rvMemoryMachineWith` projects any family witness to
the corresponding profile-parametric memory-threaded ISA step, and
`rvfiCycleStepRefines_of_rv32i_memory` packages the one-cycle invariant
obligation for a core proof; its valid-row premise needs only the indexed
family witness because that witness projects `wellFormed` itself.  The
dispatcher is scoped to RV32I plus the admitted machine-mode system/CSR and
trap cases; interrupts and M-extension operations remain outside this R2
boundary.

Every indexed witness also exposes `Rv32iBoundary.observation_spec`, which
recovers `valid = true`, `wellFormed`, and the equality between the packed
row's decoded retirement and the indexed retirement.  This projection is
derived from the generic `toRetirement?` characterization, so callers do not
depend on the tuple layout of any individual family constructor.

The instruction-specific contracts remain useful when a core invariant retains
raw fields that the indexed family intentionally abstracts.  The adapters
`addiBoundary_rv32i`, `luiBoundary_rv32i`, `auipcBoundary_rv32i`,
`swBoundary_rv32i`, `lwBoundary_rv32i`, `branchBoundary_rv32i`,
`jalBoundary_rv32i`, `jalrBoundary_rv32i`, `fenceBoundary_rv32i`,
`systemBoundary_rv32i`, `csrBoundary_rv32i`, `illegalBoundary_rv32i`, and
`illegalCsrBoundary_rv32i` convert those contracts into the corresponding
`Rv32iBoundary` index without changing the wire-level premises.  Thus a proof
may preserve an instruction-specific RVFI fact while consuming the same
stateful dispatcher as the generic row cases.

The measured four-row prefix is instantiated in
[`rvfi_rv32i_boundary.lean`](rvfi_rv32i_boundary.lean).  Its four theorems
consume the measured specialized ADDI/SW/LW predicates through the indexed
adapters, constructing the corresponding ALU/store/load witnesses, and
`pinned_unified_machine_commits` applies the dispatcher projection to each
threaded state transition.  This is a concrete boundary certificate for the
captured rows; it does not discharge the symbolic PicoRV32 invariant while
the upstream memory/generate loader refusal remains.

The same file contains `pinnedAddiCycleMachine`, a finite core-facing cycle
machine that emits the measured ADDI row once and then an invalid bubble.
`pinned_addi_cycle_refines` proves its strict packed-cycle obligation through
`rvfiCycleStepRefines_of_rv32i_memory`, using the indexed boundary's threaded
post-state and retaining relation stuttering for the bubble.  This is finite
proof plumbing for the RVFI boundary; it does not stand in for the symbolic
PicoRV32 RTL invariant while the upstream loader refusals remain.

`pinned_addi_cycle_observations_normalize` certifies the same two-cycle raw
window (ADDI followed by the invalid bubble) with the executable order and
decoding checker.  `pinned_addi_cycle_trace_refines` then applies
`rvfiCycleStepRefines_normalized_trace_refines` to show that the normalized
retirement is exactly the profile-parametric ISA ADDI step; the bubble supplies
no ISA input.

`pinned_addi_cycle_normalized_refines` uses the paired normalized theorem to
retain the post-window relation as well: after the two cycles, the finite RVFI
state is related to the stateful ISA machine's state by the expected ADDI
architectural post-state.

The same boundary file now carries `pinnedWindowMachine`, a finite strict
cycle witness for the measured eight-cycle prefix: bubble, ADDI, bubble, SW,
bubble, LW, bubble, and the second ADDI.  `pinned_window_cycle_refines`
discharges every phase through the indexed RV32I memory dispatcher, including
the threaded store-to-load memory equality, and
`pinned_window_observations_normalize` certifies that the raw rows normalize
to the four measured retirements.  The phase relation records each
architectural and memory endpoint through `pinnedWindowS0`--`pinnedWindowS4`.
This is still a finite boundary certificate for the captured stream; it does
not claim the symbolic PicoRV32 RTL invariant while the upstream loader
refusals remain.

`pinned_window_trace_refines` composes the strict eight-cycle contract with
the raw normalization certificate and shows that the four normalized
retirements equal the profile-parametric stateful ISA trace after the same
input filtering.  This keeps the trace-level claim separate from the
cycle-phase relation and preserves an explicit input-admission obligation for
future loaded-core proofs.

`pinned_window_normalized_refines` exposes the paired result: the same trace
equality together with the final `PinnedWindowRel.done` relation between the
finite RVFI state and the stateful ISA state.  The initial relation and all
eight input-admission facts are named separately so a later loaded-core proof
can reuse them without reopening the finite list cases.

The endpoint bridge is explicit as well.  `pinned_window_retire_inputs`
identifies the phase machine's retained instruction inputs with
`nontrapInputs`, `pinned_window_final_phase` reaches the `.done` phase, and
`pinned_window_trace_refines_measured` connects the normalized list to the
existing `nontrapExpected` certificate.

`pinned_window_final_state` inverts the final relation through
`pinned_window_done_eq` and identifies the stateful ISA endpoint with
`pinnedWindowS4`; `pinned_window_final_architecture` records its concrete
pc and register values for the measured input stream.

## Symbolic ADDI program certificate

`LeanModels.Refine.RvfiAddiProgram` now carries the ADDI boundary through an
arbitrary program length.  `AddiInstruction` retains the original word and a
`Fetched.decode` proof; `addiProgramState`, `addiProgramInputs`, and
`addiProgramRetirements` are the corresponding architectural folds.  The
profile-parametric `rvMemoryMachineWith_addi_program_state` and
`rvMemoryMachineWith_addi_program_trace` theorems prove the state and
retirement equations for every ADDI list, with unchanged threaded memory and
with `addiProgramState_preserves_WF` preserving the x0 invariant.

`AddiRvfiTrace` is the core-facing certificate: it permits arbitrary invalid
RVFI bubbles and requires each retiring row to carry the indexed
`Rv32iBoundary` for the next ADDI post-state and retirement.  Its
`toRvfiTraceRefines`, `normalize`, and `trace_refines` theorems turn that
inductive invariant into an order-checked normalized stream equal to the
stateful ISA trace.  This is quantified over every ADDI program and every
bubble placement; it is refinement infrastructure for the eventual loaded
PicoRV32 state relation, not a finite capture or a PicoRV32 model.  The
actual RTL instantiation remains parked at the unpacked `cpuregs` and
unsupported-member/net-z loader walls recorded above.

`AddiRvfiCycleTrace` closes the input association needed at a real cycle
boundary.  Its step indices retain the actual packed-RVFI machine state and
cycle input; bubble inputs are arbitrary, while each retirement input is
definitionally tied to the corresponding `AddiInstruction`.  The
`normalize`, `retireInputs_eq`, and `trace_refines` projections therefore give
the direct theorem for a loaded machine's own cycle list: normalized RVFI rows
equal the stateful ISA trace on exactly the inputs that the cycle adapter
retains.

`AddiRvfiCycleTrace.append` composes two such certificates at the exact
`rvfiStateAfter`/`addiProgramState` boundary.  The first chunk may contain any
number of bubbles; the second chunk starts at the first chunk's next order
index and threaded core/architectural states, and the result covers the
concatenated cycle and program lists.  This is the reusable segmented proof
shape for a future invariant, without treating a captured finite window as
the theorem's domain.

The companion fold laws `addiProgramInputs_append`,
`addiProgramState_append`, and `addiProgramRetirements_append` expose the same
join for inputs, architectural state, and semantic retirements.  A segmented
proof can therefore rewrite either side of the certificate composition to the
single whole-program folds before applying the stateful ISA equations.

## Symbolic ALU program certificate

`LeanModels.Refine.RvfiAluProgram` extends the unbounded program surface to
the complete RV32I ALU family.  `AluInstruction` retains the fetched word,
`AluOp`, both operand-source forms, and its decoder proof; the corresponding
input, architectural-state, and retirement folds preserve x0 and threaded
memory for every program list.  `rvMemoryMachineWith_alu_program_state` and
`rvMemoryMachineWith_alu_program_trace` connect those folds to the existing
profile-parametric ISA machine.

`AluRvfiTrace` accepts arbitrary invalid bubbles and requires an indexed
`Rv32iBoundary.alu` witness for every retiring row, so its `normalize` and
`trace_refines` theorems give the stateful ISA trace for any ALU program and
bubble schedule.  `AluRvfiCycleTrace` ties the same certificate to an actual
`RvfiCycleMachine`: bubble inputs remain arbitrary, while each retiring input
is exactly the corresponding `aluProgramInput`; its `normalize`,
`retireInputs_eq`, and `trace_refines` projections use the machine's own cycle
stream.  The certificate is generic refinement infrastructure; the PicoRV32
RTL remains parked at the existing unpacked `cpuregs` and unsupported-member/
net-z loader walls.
`AluRvfiTrace.append` composes raw observation certificates at the next
retirement order and folded architectural state, retaining arbitrary bubble
prefixes while concatenating ALU programs.  The machine-aware
`AluRvfiCycleTrace.append` composes two such certificates at the exact
`rvfiStateAfter`/`aluProgramState` boundary.  The second segment starts at
`start + firstProgram.length`, with the first segment's post-cycle core state
and architectural state, and covers the concatenated cycle and program lists.
The ALU input, state, and retirement fold append laws expose the same join for
a later loaded-core invariant; this does not promote the finite PicoRV32
witness or bypass its current loader walls.
The stateful-machine bridges
`rvMemoryMachineWith_alu_program_state_append` and
`rvMemoryMachineWith_alu_program_trace_append` expose the same split directly:
the first segment's threaded memory-machine state is the second segment's
starting state.

The next generic surface is
`LeanModels.Refine.RvfiMemProgram`.  It retains each memory instruction's
decoder proof and threads the exact byte memory through mixed loads and
stores, with state, retirement, and append equations for the existing
`rvMemoryMachineWith` semantics.  `MemRvfiTrace` now consumes those folds: it
admits arbitrary invalid bubbles, requires consecutive retirement order and an
indexed `Rv32iBoundary` witness for every retiring load/store, and normalizes
to the exact stateful ISA trace.  `MemRvfiTrace.append` composes adjacent
certificates at the next retirement order and exact threaded memory state.  The
certificate is generic and state-threaded;
the loaded PicoRV32 invariant remains parked at the existing unpacked
`cpuregs` and unsupported-member/net-z loader walls.

`MemRvfiCycleTrace` now retains the actual `RvfiCycleMachine` step and input
for every cycle.  Bubble inputs stay arbitrary; a retiring input is tied to
the corresponding `memProgramInput`, and its `normalize`, `retireInputs_eq`,
and `trace_refines` projections connect the machine's own stream to the
stateful ISA memory trace.
`MemRvfiCycleTrace.append` composes adjacent input-aware certificates at the
exact `rvfiStateAfter`/`memProgramState` boundary, preserving the core state,
threaded byte memory, and next retirement order.

## Zicsr boundary

The generic refinement layer now covers the implemented machine-mode Zicsr
family through `LeanModels.Refine.Rv32iCsr` and
`LeanModels.Refine.RvfiCsr`.  `CsrOpKind` retains the operation (`CSRRW`,
`CSRRS`, or `CSRRC`), destination, source form, and CSR address.  The
`findCsr?` row is an explicit premise, so an unimplemented CSR remains the
ISA's illegal-instruction trap rather than being guessed as a no-op.  The
state equation reads the old row value into `rd`, applies the exact
`csrRmw`/`csrWrites` condition, and routes writes through the row's WARL
legalizer.  `RvfiObservation.csrBoundary` carries the same row lookup, source
readback for register forms, destination readback, sequential pc, and clear
memory/trap fields.  `rvfiCycleStepRefines_of_csr_memory` threads the updated
CSR file through the stateful architectural relation while preserving data
memory.

This boundary assumes the no-interrupt input subset (`irq = 0`) and the
implemented CV32E40P machine-mode table (`mstatus`, `mie`, `mtvec`,
`mscratch`, `mepc`, and `mcause`).  CSR addresses outside that table and
interrupt-dispatch rows remain separate boundaries.

## Illegal-instruction traps

`LeanModels.Refine.Rv32iTrap` and `LeanModels.Refine.RvfiTrap` keep malformed
words as explicit trap commits.  `illegalBoundary` requires a decode failure,
the exact `illegalInstr` cause, the handler pc from `trapEnter`, and clear
register/data-memory effects.  A decoded Zicsr word whose address is absent
from `csrTable` uses the separate `illegalCsrBoundary`; its source and
destination payloads remain unconstrained because the ISA traps before the
CSR operation reads or writes state.  The two
`rvfiCycleStepRefines_of_*_memory` constructors carry the trap state through
`RvMemoryState` while preserving byte memory.  Interrupt-dispatch rows remain
outside the no-interrupt subset.


The reusable branch-family surface is now provided by
`LeanModels.Refine.RvfiBranchProgram`.  It carries arbitrary decoded
conditional branches through the exact stateful RV32I machine, including the
selected branch target and retirement fields, and supplies raw and cycle-aware
RVFI certificates with append laws.  The certificate is generic refinement
infrastructure and does not claim a symbolic PicoRV32 invariant while the
pinned RTL remains blocked by the unpacked `cpuregs` and
unsupported-member/net-z loader walls.


The reusable jump-family surface is provided by
`LeanModels.Refine.RvfiJumpProgram`.  It covers arbitrary decoded JAL and JALR
streams, including link writes and JALR target-bit clearing, with raw and
cycle-aware RVFI certificates and append laws.  This remains generic
refinement infrastructure; the pinned PicoRV32 RTL is still blocked by the
unpacked `cpuregs` and unsupported-member/net-z loader walls.


The upper-immediate program certificate in
`LeanModels.Refine.RvfiUpperProgram` covers arbitrary LUI/AUIPC streams and
retains their exact writeback values in raw and cycle-aware RVFI certificates.
It is generic proof infrastructure; the pinned RTL remains parked at the
existing loader walls.

The fence program certificate in `LeanModels.Refine.RvfiFenceProgram` covers
arbitrary decoded `FENCE` and `FENCE.I` streams.  Its raw and cycle-aware
certificates retain arbitrary bubble inputs and exact machine transitions,
normalize to the stateful RV32I fence trace, and compose at the architectural,
core-state, and retirement-order boundaries.  Fence instructions preserve the
threaded data memory; PicoRV32 remains parked at the existing unpacked-memory
and unsupported-member/net-z loader walls.

The system-operation program certificate in
`LeanModels.Refine.RvfiSystemProgram` covers arbitrary decoded `ECALL`,
`EBREAK`, `MRET`, and no-interrupt `WFI` streams.  It retains exact trap and
return effects, arbitrary bubble inputs, cycle-step equalities, and the
unchanged threaded data memory in raw and cycle-aware certificates, with
append laws at the core, architectural-state, and retirement-order boundaries.

The implemented Zicsr program certificate in
`LeanModels.Refine.RvfiCsrProgram` covers arbitrary machine-mode `CSRRW`,
`CSRRS`, and `CSRRC` streams whose addresses resolve to the explicit CSR table.
It retains old-value readback, source forms, WARL updates, arbitrary bubble
inputs, and exact cycle transitions while preserving threaded data memory and
composing at the core, architectural-state, and retirement-order boundaries.

`LeanModels.Refine.RvfiIllegalProgram` adds the symbolic decode-failure trap
surface.  It retains arbitrary undecodable words, exact illegal-instruction
causes and handler pcs, bubble inputs, cycle transitions, and unchanged
threaded data memory while composing at the same core, architectural-state,
and retirement-order boundaries.  Unimplemented CSR rows remain covered by
the separate raw illegal-CSR boundary.

`LeanModels.Refine.RvfiTrapProgram` unifies the symbolic trap-program surface
for undecodable words and decoded Zicsr words with absent rows.  It keeps both
parser-derived proofs explicit while retaining exact illegal causes, handler
pcs, cycle inputs, and threaded memory through compositional raw and
cycle-aware certificates.

## 2026-11-07 re-probe after generated-member admission (`bf85f330a`)

The pinned YosysHQ source was re-extracted once more without RTL changes after
the generic generated-member regression landed.  The semantic files in the
working tree are identical to `origin/master` at `27e7d5d62`; that revision
contains `bf85f330a` and only later documentation commits change the tree.
The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`.  The fresh envelope is
2,992,406 bytes with SHA-256
`bbdf7aee9e200a35f228adfa891eeaa10addb3b1608f3776f0bd9d61c42d4f9c`.

The declaration loads as a 26-parameter family with 216 declarations, 43
processes, and three generate entries.  At the default parameters, the
ordinary semantic route's exact first refusal is still:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route now expands the generic generated-member shapes, but the
PicoRV32 instance first refuses at the existing unsupported-module-member
gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is `NetSymbol:net-z` for `pcpi_mul_wr`, the `wire`
at `picorv32.v:257`.  The clean-room `generate if` and `generate for`
fixtures both remain admitted, so this is not a new generated-member shape and
no `REQUEST ls-sv:` repro is filed.  The symbolic ADDI invariant remains
parked at the unpacked `cpuregs` and unsupported-member/net-z walls.

## Mixed RV32I program certificate

`LeanModels.Refine.RvfiRv32iProgram` now combines the admitted ALU, branch,
jump, memory, fence, system, implemented-CSR, and illegal/trap families in one
`Rv32iInstruction` union.  Its input, architectural-state, byte-memory, and
retirement folds thread arbitrary mixed programs, and their append laws expose
the exact state boundary for segmented proofs.  `Rv32iRvfiTrace` and
`Rv32iRvfiCycleTrace` consume the existing indexed `Rv32iBoundary`, preserve
arbitrary bubble cycles and actual retiring inputs, and normalize the mixed
stream to the stateful RV32I machine trace.  This is generic refinement
infrastructure; the pinned PicoRV32 RTL remains parked at the loader walls
above.

The companion `rvfiCycleStepRefines_of_rv32i_program` constructor is the
core-facing one-step form: a valid row must identify an `Rv32iInstruction`,
its exact input, indexed post-state, and retirement, while invalid rows remain
ISA stutters.

## Constructing mixed cycle certificates from an invariant

The generic `Rv32iCycleStepRefines` contract and
`rv32iRvfiCycleTrace_of_step` constructor now turn a loaded-core invariant into
an arbitrary finite mixed RV32I cycle certificate.  Every valid row retains
its order tag, exact cycle input, indexed post-state, and retirement; bubbles
retain their inputs and core transitions.  The constructor threads the final
core relation to the mixed architectural state.  PicoRV32 itself remains
parked at the existing loader walls, so this adds no finite captured-window
claim.

`rv32iRvfiCycleTrace_of_step_refines` packages the same result for a future
loaded-core proof: from the indexed step invariant and an admitted finite
window it returns the mixed certificate, its normalized equality to the
stateful ISA trace, and the final core-to-ISA relation together.

## Clean-room repros for the two current walls

The owner-lane request for the remaining PicoRV32 walls is backed by two
minimal source-shaped fixtures in [`walls/`](walls/).  They use the approved
Slang extractor and preserve the parameterized memory structure; neither is a
PicoRV32 adaptation.

[`unpacked_cpuregs.sv`](walls/unpacked_cpuregs.sv) has a run-time indexed
register file read and write.  Its 14,071-byte envelope has SHA-256
`8d6c16562fa48475c8ecd4eb83ec52ebadfdf01b99222fd6cabee3950db6decd`, and the
ordinary route at `sem 32` returns the exact first refusal:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

[`net_z_memory.sv`](walls/net_z_memory.sv) places the undriven plain
`wire pcpi_mul_wr;` beside a parameter-sized memory.  Its 7,792-byte envelope
has SHA-256
`d040779e40a76d13d2fedcf826dd02726fca0565560a724f3173b1331024de09`;
`pdesign.others` retains `NetSymbol:net-z` for `pcpi_mul_wr`, and
`instantiateMemD2 [4]` returns:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

[`probe.lean`](walls/probe.lean) guards both exact results.  The corresponding
dated `REQUEST ls-sv:` asks the owner lane to admit these constructs with exact
IEEE 1800 semantics while preserving loud refusal outside the supported shape.
