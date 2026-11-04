# The RV32IMC + M-mode ISA model (`LeanModels/Rv/**`)

The single source of truth for the CV32E40P program: an executable
RV32IMC + machine-mode (priv v1.11, `PULP_SECURE = 0`) ISA model in plain
Lean over `BitVec 32`, whose named definitions are the projection sources
for the module specs of `docs/cv32e40p-spec-surface.md`. No axioms — every
ISA fact is a definition (design law L3); tables transliterated from
sail-riscv sources are attributed in file headers (BSD-2-Clause), semantics
re-derived in this tree's idiom.

## Files

| File | Contents |
|---|---|
| `LeanModels/Rv/Ast.lean` | `Instr` (six semantic constructor families — not opcode-per-constructor; see the module docstring for the `no_confusion` rationale), operand sources, `ArchState`, `CsrFile` |
| `LeanModels/Rv/Decode.lean` | `decodeTable` (57 disjoint wildcard rows), `decode`, the RVC expander `expandC : BitVec 16 → Option (BitVec 32)`, `decode16` |
| `LeanModels/Rv/Exec.lean` | `aluSem`, width-generic `divRem`, `mulDivSem`, `branchSem`, byte-addressed little-endian memory, `Effects`, the non-privileged step `execInstr` |
| `LeanModels/Rv/Csr.lean` | `CsrBehavior` rows with WARL legalization as data (`legalize_<csr>` shape), `csrTable` for {mstatus, mie, mtvec, mscratch, mepc, mcause} |
| `LeanModels/Rv/Priv.lean` | `Cause`, `trapEnter`/`mret` (the mstatus stack dance, defined once), `trapVector`, `pendingSet`/`irqPriority`/`selectIrq`/`takeInterrupt?` |
| `LeanModels/Rv/Step.lean` | `Fetched` parcels, CSR read-modify-write, WFI wake, the full architectural step `isaStep` and its projection index |

The projection table (which def feeds which gallery spec) lives in
`Step.lean`'s module docstring.

## Differential validation (`harness/rv/diff_test.py`)

**Oracle: the sail-riscv C emulator**, pinned prebuilt release binary
0.13.1 under `tools/rv-oracle/` (gitignored; `tools/rv-oracle/README.md`
has the one-command fetch). Spike/QEMU fallbacks were unnecessary — no
RISC-V toolchain exists on this host, and sail publishes Linux-x86_64
binaries; sail is also the preferred oracle (SYNTHESIS: validation oracle
only, never a term source). The emulator runs with `--rv32
--config-override harness/rv/sail_rv32imc_override.json`, which scopes it
to exactly the model's fragment: `rv32imc_zicsr_zifencei`, M-mode only,
**priv v1.11** (sail supports selecting it), PMP absent, misaligned data
access allowed.

**Method.** Each case is a self-contained flat program assembled by the
harness's own RV32IMC encoder (no toolchain): trap handler at the
256-aligned mtvec base (16 vectored slots), normalization prologue,
register preamble, the instruction under test between compressed-nop
landing pads (so branch/jump targets — including 2-mod-4 misaligned ones —
always rejoin), a `csrr` postamble (CSR state is observed through the
architecture, so it lands in the compared GPR stream), and an HTIF
terminator. The same bytes go to sail as a handcrafted ELF and to
`harness/rv/isa_run.lean` (one `lake env lean --run` batch) as JSON
segments. Compared per case: every retired pc, every value-changing GPR
write in order, every data-memory write `(addr, width, value)`, the final
register file, the x0 = 0 kernel on both sides, and termination.
Interrupts are injected through sail's simple-interrupt-generator MMIO
device (MSI/MEI set/clear by store), mirrored by a platform layer in the
Lean runner — dispatch timing, vectoring, and masking are compared, not
just CSR values.

**Result: 257 cases, 257 PASS** (seeded random + corner vectors per family:
ALU R/I, LUI/AUIPC, all eight M ops with the §7.2 div/rem quirk battery,
branches taken/not-taken/misaligned-target/into-own-encoding, JAL/JALR
(odd-target bit-0 clearing, rd = rs1), loads/stores at every width and
misalignment with sign/zero-extension corners, ~40 RVC cases (enumerated
expansions incl. `c.jal` linking pc+2, plus filtered random halfwords),
exceptions (ecall/ebreak/c.ebreak/17 illegal encodings/unimplemented CSRs)
with full trap-entry/mret round trips, the CSR RMW matrix with WARL
corners and the no-write forms, interrupt dispatch (MSI/MEI, vectored and
direct, MEI-beats-MSI priority, mie/mstatus masking, mid-RVC-stream
dispatch), WFI wake, and the x0-write-discard kernel. A deliberate
mutation of the runner's fetch path makes the harness fail, so it detects
what it claims to detect.

### Divergences found and their resolutions

Genuine behavior differences surfaced by the harness, all resolved as
*documented WARL/platform scope choices* (CV32E40P RTL choice vs sail's
choice, both spec-legal) — none required a model change, and each
CV32E40P-specific behavior is pinned by `#guard`s in the model files:

1. **mstatus reset value**: sail resets mstatus to `0x0` (MPP = 00); the
   model — like `cv32e40p_cs_registers.sv` — resets to `0x1800` (MPP reads
   M). v1.11 only pins MIE = MPRV = 0 at reset. The harness prologue
   normalizes with a write (both sides then read MPP = 11; sail's write
   legalization agrees exactly with `mkMstatus` — all-ones lands `0x1888`
   on both).
2. **mie writable mask**: CV32E40P's `IRQ_MASK = 0xFFFF0888` keeps the
   sixteen fast-interrupt bits; sail M-only keeps `0x888`. Vectors stay
   ⊆ `0x888`; the fast bits are `#guard`-pinned (`Csr.lean`).
3. **mtvec WARL**: CV32E40P keeps base[31:8] and hardwires mode bit 1
   (reserved modes 10/11 legalize to 00/01); sail keeps base[31:2] and
   *ignores* reserved-mode writes (keeps the old mode — the
   `Xtvec_Ignore` config). Vectors use 256-aligned bases with mode ∈
   {00, 01} plus the one agreeing reserved-mode case (mode 10 from
   direct).
4. **mcause writes**: CV32E40P's 6-bit register narrows the WLRL code
   field to bits {31, 4:0}; sail keeps every written bit. Vectors stay
   ⊆ `0x8000001F`.
5. **Platform scope**: fast interrupts 16–31 (and their priority above
   MEI) are not injectable in sail's platform (its mip has MEI/MTI/MSI
   only) — the cascade is `#guard`-pinned in `Priv.lean`; MTI is not
   driven (sail's CLINT has mtimecmp = 0 at reset, so MTIP pends
   immediately — vectors simply never enable MTIE). Bus/access faults do
   not exist in the model (CV32E40P's fault inputs are asserted away), so
   all accesses stay inside sail's RAM and stores wrapping the 2^32 edge
   are `#guard`-covered instead (`Exec.lean`).
6. **WFI-first rule**: with `mstatus.MIE = 1` and a pending interrupt, the
   model retires a fresh WFI first and takes the interrupt at the next
   step with mepc past the WFI (the CV32E40P/v1.11 "resume after WFI"
   reading); sail traps on the WFI itself. Both v1.11-legal; the harness
   compares the MIE = 0 wake case (identical on both sides) and the
   WFI-first behavior is `#guard`-pinned in `Step.lean`.

`tools/ci.sh` runs the harness as the `rv-harness` step, gated on the
oracle binary's presence (SKIP when absent, like the other lab-host-only
oracles).

## Verification notes

* `#print axioms` over every public def: nothing beyond the standard
  kernel axioms (`propext`, `Quot.sound`) — no `Classical.choice`, no
  `sorryAx`, no custom axioms anywhere.
* The four projection exports elaborate against their consumers' shapes
  (mock `decoder_conforms` / `alu_conf_base` / width-generic `alu_div_tx`
  / `csr_write_conforms` / `controller_irq_boundary` statements, plus the
  `isaStep` refinement shape).
* Goal legibility: goals stay entirely in model vocabulary (`trapEnter`,
  `mret`, `execInstr`, `findCsr?` — no AST/fuel/encoding scrambles). The
  working idiom for concrete instructions is decode-first: `have hd :
  (Fetched.word w).decode = some i := by decide`, then `simp only
  [isaStep, takeInterrupt?, h, hd, ...]` collapses the dispatcher to the
  family arm. One rough edge: full `simp` renormalizes `BitVec` literals
  (`OfNat` vs `BitVec.ofNat`), which can decouple a prepared decode fact
  from the goal — prefer `simp only`, which avoids the renormalization.
