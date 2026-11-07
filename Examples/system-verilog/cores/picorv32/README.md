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

The witness also reconstructs the measured `ADDI x3, x2, 1` row after the
`ADDI/SW/LW` prefix.  It retains the source fields (`rs1_addr = 2`,
`rs1_rdata = 5`), proves the threaded architectural state has `pc = 12`,
`x2 = 5`, and `x0 = 0`, and applies the same raw-to-ISA step bridge at that
non-reset boundary.

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

