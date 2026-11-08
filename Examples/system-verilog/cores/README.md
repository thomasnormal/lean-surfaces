# R2 core scouting

This is the R2 admission census for three real RISC-V cores.  The source trees
were cloned at the pins below and were not modified.  The extractor and
`load_design_sv2` were run from this repository with Lean 4.33.0-rc1.  The
envelopes were kept outside the repository; their SHA-256 values make the
measurements reproducible without vendoring third-party RTL.

## Pins and licenses

| core | upstream pin | license | top | source files in envelope |
| --- | --- | --- | --- | ---: |
| CV32E40P | [`openhwgroup/cv32e40p`](https://github.com/openhwgroup/cv32e40p), tag `v1.0.1`, `6148cf567f2450052458c21c5b3cc2a02423c69d` | Solderpad Hardware License 0.51 (`LICENSE`) | `riscv_core` | 31 |
| Ibex | [`lowRISC/ibex`](https://github.com/lowRISC/ibex), `master`, `d513671dae09e701ceb6cd732d2da5fb52c13856` | Apache-2.0 (`LICENSE`) | `ibex_top` | 224 |
| PicoRV32 | [`YosysHQ/picorv32`](https://github.com/YosysHQ/picorv32), `main`, `ef203c2b0a3fb793280f5114941416c425c5b461` | ISC (`COPYING`) | `picorv32` | 1 |

The CV32E40P input is every `rtl/*.sv`.  The Ibex input is `rtl/*.sv` plus
the primitive and common-cell SystemVerilog dependency directories selected
by `ibex_top.core` (the broad set keeps unresolved primitive dependencies
visible).  PicoRV32 uses the single `picorv32.v` source from its default
FuseSoC target.  No RTL adaptation was made.

## Commands and measurements

For each clone, the command was the symbolic extractor invocation below, with
the listed source set passed as the final arguments:

```text
python3 extractors/sv/extract.py --top TOP -o RESULT.sv.json SOURCE...
```

The loader probe was a small Lean file containing:

```lean
import LeanModels.Sv.Ingest2
load_design_sv2 NAME from "RESULT.sv.json"
#check NAME
```

| core | extraction wall | envelope bytes / SHA-256 | hierarchy modules | static `Unsupported` nodes | loader result |
| --- | ---: | --- | ---: | ---: | --- |
| CV32E40P | 17.08 s | 21,289,394 / `e588884691159820eac0a28eff5315e721b99fdf989f6611540931e5f264a6de` | 23 | 293 | **refused** |
| Ibex | 39.13 s | 13,914,127 / `ae014736a66a58b0f725d0bf358ee8ebab6fb05ef75e0645ea1507137ce2f7d4` | 20 | 396 | **refused** |
| PicoRV32 | 4.37 s | 3,178,052 / `009cc39591b3fcb1c88403ca44f822cb1854d2ebc0b5c728c7cade06a2e47b1b` | 1 | 70 | **loaded** |

The loader diagnostics below are the complete first errors, copied from the
Lean probes:

```text
CV32E40P:
envelope: module: AlwaysPosedge: AlwaysPosedge:edge — edge-qualified clock requires its retained event semantics

Ibex:
envelope: module: AlwaysLatch: unknown process kind "AlwaysLatch"
```

PicoRV32 loads as a 26-`Nat` parameter family.  Loading is not a claim that
the semantic tier is admitted: at the default values,

```text
(picorv32.sem defaults).hasUnsupported = true
processes.size = 1
[(Instantiate, decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory))]
```

Thus its first semantic wall is the register-file unpacked memory, while the
envelope loader itself succeeds.  Its most frequent static walls are
unsized/XZ parametric literals (16), call expressions (13), width
conversions (11), net-z (8), and assignment targets (6); these counts are
telemetry, not silently admitted semantics.

The first admission pass recorded a 2.21-second, 3,181,105-byte envelope with SHA-256
`25ac7e444bd6f4171348484fcba4d99e9c5192036764dabb8b64a6ef8c77be26` before the
extractor was re-run for the current re-probe.  The canonical measurement for
the pinned source is now the reproducible 3,178,052-byte envelope above
(`009cc395…`); the source commit and all loader diagnostics are unchanged.
Later R2 decisions use the canonical envelope, rather than mixing the two
extractor snapshots.

## Ranking and next requests

Measured distance to an R2 proof target is:

1. **PicoRV32** — closest: one-module load succeeds and the remaining first
   semantic wall is a concrete unpacked memory shape (`cpuregs`).
2. **CV32E40P** — next: 23 modules extract, but the loader stops at retained
   edge-process semantics (`AlwaysPosedge`).
3. **Ibex** — last for this tier: the broad dependency closure extracts 20
   modules, but `AlwaysLatch` is encountered before a design family can load;
   primitive/dependency unsupported nodes add further work after that wall.

The result is a scouting decision, not a core selection for the proof rung:
PicoRV32 is the first candidate to revisit after the remaining unpacked-memory
and module-member boundaries land in the SV tier.  No core was rewritten to
fit the loader.

## Current PicoRV32 re-probe

The table above is the original cross-core census.  On 2026-11-07, after the
generic memory route admitted generated members, the pinned PicoRV32 source was
re-extracted with the current extractor and loaded against `github/master`
revision `83638b50fccf1dfe7980f2ca1ab49e1366f34ef4`:

```text
source commit: ef203c2b0a3fb793280f5114941416c425c5b461
envelope: 2d2d3c1b5cdd459b61a29ab38e6384db20f1f4a6cdbf5b211fe47cc2a1e785c8
size: 2,986,551 bytes
```

The declaration still loads as a 26-parameter family.  Its ordinary semantic
family still first refuses at `picorv32.v:203`:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The rebuilt memory route now expands the source-shaped generated members; its
first PicoRV32 refusal is instead the top-level unsupported-member gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is `NetSymbol:net-z` for `pcpi_mul_wr`, the `wire`
at `picorv32.v:257`.  This is an existing generic net-z boundary.  The
symbolic R2 invariant therefore remains parked at the unpacked `cpuregs` and
net-z/unsupported-member walls; no core-specific adaptation or finite-window
extension was made.

## Latest PicoRV32 re-probe after dynamic parameterized-memory admission

After `github/master` advanced to `cb99d49c69db72421ab3c7b16447b47311f60890`
(`[ls-sv] admit dynamic parameterized register memories`), the unchanged
PicoRV32 source was extracted again.  The fresh envelope is
`bbdf7aee9e200a35f228adfa891eeaa10addb3b1608f3776f0bd9d61c42d4f9c` and
2,992,406 bytes.  The declaration still loads as a 26-parameter family.  The
ordinary semantic family still first refuses the unpacked `cpuregs` memory at
`picorv32.v:203`:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route reaches its existing unsupported-module-member gate before
the new dynamic-memory path can run:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is still `NetSymbol:net-z` for `pcpi_mul_wr` at
`picorv32.v:257`, an already catalogued generic boundary.  No new owner-lane
request or core adaptation is justified by this probe.

The owned refinement layer now has a symbolic ADDI-program certificate in
`LeanModels.Refine.RvfiAddiProgram`: arbitrary decoded ADDI lists, arbitrary
invalid RVFI bubbles, and indexed `Rv32iBoundary` witnesses normalize to the
exact stateful ISA trace.  This advances the reusable invariant surface while
the real PicoRV32 instantiation remains blocked by the existing loader walls.
The input-aware `AddiRvfiCycleTrace` extension also retains actual cycle-step
equalities and proves that the adapter's `retireInputs` are exactly the
symbolic ADDI inputs before applying the same trace theorem.
The companion `LeanModels.Refine.RvfiAluProgram` certificate lifts this
surface to arbitrary decoded RV32I ALU instructions, including register,
immediate, pc-based, and upper-immediate operand shapes.
Its `AluRvfiCycleTrace` extension retains actual cycle-step equalities and
retiring inputs, then normalizes the machine's own cycle stream to the same
stateful ALU trace.
`AluRvfiTrace.append` composes raw observation certificates at the next
retirement order and folded architectural state, preserving arbitrary bubble
prefixes while concatenating ALU programs.  The machine-aware
`AluRvfiCycleTrace.append` composes two such certificates at the exact
`rvfiStateAfter`/`aluProgramState` boundary: the second segment starts at the
first segment's next retirement order and receives its threaded core and
architectural states.  The corresponding ALU input, state, and retirement
fold append laws expose the same join for a segmented loaded-core proof.
The stateful-machine bridges `rvMemoryMachineWith_alu_program_state_append`
and `rvMemoryMachineWith_alu_program_trace_append` expose the corresponding
`machineStateAfter` and retirement-trace splits directly, with the first
segment's threaded state feeding the second.

`LeanModels.Refine.RvfiMemProgram` starts the corresponding memory-program
surface.  `MemInstruction` retains a generic RV32I load/store operation and
decoder proof; its input, state, and retirement folds thread the byte memory
through mixed programs.  The stateful-machine equations and append bridges
reuse the existing `memNext`, `memAfter`, and `Rv32iBoundary.mem` semantics.

`MemRvfiTrace` is the raw certificate for that surface.  It admits arbitrary
invalid RVFI bubbles and requires the next retirement order plus an indexed
`Rv32iBoundary` witness for every load/store row.  Its normalization theorem
feeds the existing order-checked RVFI normalizer, and `trace_refines` identifies
the result with the profile-parametric stateful ISA trace for the same
threaded memory program.  `MemRvfiTrace.append` composes adjacent certificates
at the next retirement order and the exact threaded architectural and byte
memory state.  This is generic refinement infrastructure; the
PicoRV32 RTL remains parked at the existing unpacked `cpuregs` and
unsupported-member/net-z loader walls.

`MemRvfiCycleTrace` ties the same certificate to an actual
`RvfiCycleMachine`: bubble inputs remain arbitrary, while each retiring input
is definitionally the corresponding `memProgramInput`.  Its normalization,
`retireInputs_eq`, and `trace_refines` projections expose the machine's own
cycle stream to a future loaded-core invariant.

`MemRvfiCycleTrace.append` composes two such certificates at the exact
`rvfiStateAfter`/`memProgramState` boundary, carrying the first segment's
core state, byte memory, and next retirement order into the second segment.

## Current PicoRV32 re-probe on `github/master` 43a471fe3

The pinned YosysHQ source was freshly extracted again on 2026-11-07 without
RTL changes.  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the current envelope is 2,992,422
bytes with SHA-256
`bbb534099237338b0c945ef56634407d9918a03f802a3fb1e11753d920a245be`.

At the recorded default parameters, the ordinary semantic route's exact first
refusal is:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route advances past generated members but first refuses:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is the net-z wire `pcpi_mul_wr` at
`picorv32.v:257`.  This confirms the existing unpacked-memory and
unsupported-member/net-z walls; no new clean-room request or core adaptation
is justified.

The owned refinement layer now also includes
`LeanModels.Refine.RvfiBranchProgram`.  `BranchInstruction` retains the fetched
word, branch condition, source registers, offset, and decoder proof; the input,
architectural-state, and retirement folds preserve the exact conditional-branch
semantics for arbitrary lists.  `BranchRvfiTrace` and
`BranchRvfiCycleTrace` normalize raw RVFI observations, retain arbitrary bubble
inputs and cycle-step equalities, and identify the result with the stateful
RV32I machine trace.  Their append theorems compose adjacent certificates at
the exact architectural state, core state, and retirement-order boundary.
This is generic refinement infrastructure; the PicoRV32 RTL remains parked at
the existing unpacked `cpuregs` and unsupported-member/net-z loader walls.


The generic refinement layer now includes
`LeanModels.Refine.RvfiJumpProgram`.  `JumpInstruction` retains the fetched
word, semantic JAL/JALR kind, and decoder proof; the state and retirement folds
cover arbitrary mixtures of the two jump forms.  `JumpRvfiTrace` and
`JumpRvfiCycleTrace` normalize raw RVFI rows, retain arbitrary bubble inputs and
cycle-step equalities, and compose at the exact core, architectural-state, and
retirement-order boundary.  The bridges use the existing JAL/JALR target and
link-address semantics without introducing a second decoder.


`LeanModels.Refine.RvfiUpperProgram` now provides the corresponding
state-threaded LUI/AUIPC surface.  `UpperKind` keeps the two upper-immediate
forms distinct, while the program folds and raw/cycle RVFI certificates reuse
the exact writeback and pc semantics and compose at the same architectural and
retirement-order boundaries.

`LeanModels.Refine.RvfiFenceProgram` provides the matching state-threaded
`FENCE`/`FENCE.I` surface.  `FenceInstruction` retains the decoded fence kind
and fetched word; raw and cycle-aware certificates normalize arbitrary bubble
streams, retain the actual cycle inputs, and compose at the exact core,
architectural-state, and retirement-order boundaries.  Fence execution keeps
the threaded data memory unchanged through the existing profile-parametric
RV32I machine.

`LeanModels.Refine.RvfiSystemProgram` provides the corresponding no-interrupt
system-operation surface for `ECALL`, `EBREAK`, `MRET`, and `WFI`.
`SystemInstruction` retains the decoded operation and fetched word; its raw
and cycle-aware certificates preserve arbitrary bubbles, exact cycle inputs,
trap and return transitions, and the unchanged threaded data memory while
composing at the same core/state/retirement-order boundaries.

`LeanModels.Refine.RvfiCsrProgram` adds the implemented machine-mode Zicsr
surface.  `CsrInstruction` retains its CSR row, operation, decoder proof, and
row-lookup proof; raw and cycle-aware certificates preserve CSR readback,
WARL state updates, arbitrary bubbles, actual inputs, and the unchanged data
memory while composing at the same boundaries.  An absent CSR row remains
outside this certificate and follows the illegal-instruction boundary.

`LeanModels.Refine.RvfiIllegalProgram` supplies the corresponding
decode-failure trap certificate.  `IllegalInstruction` retains an undecodable
word and its proof; raw and cycle-aware certificates preserve the precise
illegal-instruction cause, trap handler transition, arbitrary bubbles, actual
inputs, unchanged data memory, and compositional core/state/order boundaries.

`LeanModels.Refine.RvfiTrapProgram` combines both illegal-instruction shapes
in one trap-program certificate: undecodable words and decoded Zicsr words
whose CSR rows are absent.  The indexed constructors retain the parser proofs
for each case while normalizing arbitrary bubbles and composing exact trap
transitions at the core, architectural-state, and retirement-order boundaries.

## Current PicoRV32 re-probe after generated-member admission (`bf85f330a`)

The pinned YosysHQ source was re-extracted on 2026-11-07 without RTL changes.
The semantic files used for the probe are identical to `origin/master` at
`27e7d5d62`, which contains the generated-member regression
`bf85f330a`; the later commits only add documentation.  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the fresh envelope is 2,992,406
bytes with SHA-256
`bbdf7aee9e200a35f228adfa891eeaa10addb3b1608f3776f0bd9d61c42d4f9c`.

The declaration loads as a 26-parameter family with 216 declarations, 43
processes, and three generate entries.  The ordinary semantic route's exact
first refusal remains:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route now admits the clean-room generated-member shapes, then first
refuses the PicoRV32 instance at the existing unsupported-module-member gate:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

Its first retained member is `NetSymbol:net-z` for `pcpi_mul_wr` at
`picorv32.v:257`.  No new clean-room request or core adaptation is justified;
the symbolic ADDI invariant remains parked at the unpacked `cpuregs` and
unsupported-member/net-z walls.

## 2026-11-08 PicoRV32 re-probe on the owner branch

The pinned YosysHQ source was re-extracted without RTL changes against the
owner lane's generated-member revision `ac176c933` (the public merge was still
pending at this probe).  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the fresh envelope is 2,991,521
bytes with SHA-256
`5cf47d7aed28c2e63a0ab0dc3f3ac414f27fe326eab59ffe232b348bace45a3b`.

The declaration has 26 parameter declarations (18 local parameters), 189
declarations, 43 processes, and three generate entries.  The ordinary route's
exact first refusal remains:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route passes the generated members and then first refuses:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first retained member is `NetSymbol:net-z` for `pcpi_mul_wr` at
`picorv32.v:257`.  This is an existing generic wall, so no new clean-room
request or RTL adaptation is justified; the symbolic ADDI invariant remains
parked at the unpacked-memory and unsupported-member/net-z boundaries.

## 2026-11-08 PicoRV32 re-probe after undriven-net admission (`3d11ff8f7`)

The pinned YosysHQ source was re-extracted without RTL changes against the
owner lane's memory-route revision `3d11ff8f7` (the public merge was still
pending at this probe).  The source remains
`ef203c2b0a3fb793280f5114941416c425c5b461`; the fresh envelope is 2,991,521
bytes with SHA-256
`5cf47d7aed28c2e63a0ab0dc3f3ac414f27fe326eab59ffe232b348bace45a3b`.

The ordinary route still first refuses the unpacked `cpuregs` memory:

```text
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The memory route admits the eight source-shaped PCPI `NetSymbol:net-z`
members, including `pcpi_mul_wr`, then first refuses:

```text
unsupported "Instantiate"
  "memory cycle route does not yet admit unsupported module members"
```

The first remaining denied member is the already catalogued
`IntegerLiteral:unsized-xz-parametric` (`'bx`) at `picorv32.v:1038`.
The generic x/z refusal family already has its own fixtures and oracle
records, so no duplicate clean-room request or RTL adaptation is justified;
the symbolic ADDI invariant remains parked at the unpacked-memory and
parametric-x/z boundaries.

## Mixed RV32I program certificate

`LeanModels.Refine.RvfiRv32iProgram` combines the admitted ALU, branch, jump,
memory, fence, system, implemented-CSR, and illegal/trap families in one
`Rv32iInstruction` union.  The mixed input, state, byte-memory, and retirement
folds expose append boundaries for arbitrary programs.  Its raw and
cycle-aware RVFI certificates consume the indexed `Rv32iBoundary`, preserve
bubbles and actual retiring inputs, and identify the normalized observations
with the stateful RV32I machine trace.  PicoRV32 remains blocked at the
unpacked `cpuregs` and unsupported-member/net-z loader boundaries.

The companion `rvfiCycleStepRefines_of_rv32i_program` constructor packages the
core-facing one-step invariant: each valid row identifies one mixed
instruction, its exact input, indexed post-state, and retirement; invalid rows
remain explicit ISA stutters.

## Constructing mixed cycle certificates from an invariant

`LeanModels.Refine.RvfiRv32iProgram` now defines
`Rv32iCycleStepRefines` and `rv32iRvfiCycleTrace_of_step`.  A loaded-core
invariant supplies the current order tag, exact cycle input, indexed mixed
boundary, and relation update for each valid row; invalid rows carry the
relation across an ISA stutter.  The constructor then produces a certificate
for every admitted finite cycle window, retaining every bubble input and core
state transition and threading the final relation to the mixed program state.
This is generic refinement infrastructure and does not model or extend a
finite PicoRV32 capture.

The companion `rv32iRvfiCycleTrace_of_step_refines` corollary now composes the
indexed step invariant with any admitted finite cycle window.  It returns the
mixed cycle certificate, the normalized equality to the stateful ISA trace,
and the final core-to-ISA relation in one quantified result.

## 2026-11-08 combined PicoRV32 memory/xz clean-room repro

Item 389 adds the source-shaped fixture
`Examples/system-verilog/cores/picorv32/walls/xz_memory.sv`.  It combines a
parameter-sized unpacked memory with a continuous assignment of the unsized
x/z literal `'bx`; it is a generic measurement fixture, not a rewrite of the
pinned YosysHQ source and not a new owner-lane request.

The approved pyslang-11 extractor emits a 9,020-byte envelope whose SHA-256 is
`cc40cd919372a91246472303ea75f1a9bb6cb569af0e4f9ad15161507fb3a610` (source
SHA-256 `b2f937bcacf45a96a2958dfc46c5b8239589dfcdc98c3e521f26bd4a04b0ed2f`).
The exact probe records the ordinary unpacked-memory refusal, the retained
`IntegerLiteral:unsized-xz-parametric`/`'bx` metadata, and the memory-route
`memory cycle route does not yet admit unsupported module members` refusal.
The owner-branch measurement at `3d11ff8f7` agrees and leaves the first denied
member in the already catalogued parametric x/z family.
