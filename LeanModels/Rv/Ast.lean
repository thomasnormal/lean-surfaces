/-!
# RV32IM(C) ISA model — abstract syntax and architectural state

The single source of truth for the CV32E40P program: the spec-side artifacts of
`docs/cv32e40p-spec-surface.md` (decode table, `aluSem`, `Rv.divRem`, the CSR
behavior table) are projections of the definitions in `LeanModels/Rv/**`.
Everything here is an ordinary Lean `def`/`inductive` — no axioms; ISA facts are
definitions (design law L3).

## The family design (semantic buckets, not opcode-per-constructor)

`Instr` has **six semantic constructor families**, not one constructor per
opcode. Rationale (docs/litreview/SYNTHESIS.md, adoption #3): opcode-per-
constructor encodings fight the prover — Lean's `no_confusion` generation is
quadratic in the constructor count, and a 60-constructor `Instr` makes every
case split in every future proof goal pay for it. Independent confirmation from
Carneiro (leanprover Zulip "RISC-V ISA in Lean"), LNSym, and riscv-coq: bucket
by *semantic shape* and make orthogonality explicit. The buckets:

* `.alu`     — writeback computation `rd := f a b`; operand-1 from a register
               or the pc, operand-2 from a register or an immediate. One family
               covers OP, OP-IMM, LUI (`add x0 imm`) and AUIPC (`add pc imm`)
               — exactly the operand muxes of `cv32e40p_alu`
               (`alu_op_a_mux_sel` can select the current PC in the RTL).
* `.mulDiv`  — the M extension. A separate family, not extra `AluOp` rows: its
               operand shape is genuinely different (always reg×reg, no
               immediate forms exist), and in CV32E40P it targets different
               hardware (`cv32e40p_mult` / `cv32e40p_alu_div`), with its own
               semantics functions (`mulDivSem`, `Rv.divRem`).
* `.branch`  — compare-and-relative-jump, no writeback.
* `.jump`    — unconditional transfer with link writeback; the base reuses
               `Src1` (JAL = pc-relative, JALR = register-relative).
* `.mem`     — one data-memory access; direction carries the load-only
               sign-extension flag (sign extension is meaningless for stores,
               so the type does not let a store have one).
* `.system`  — environment interaction: ECALL/EBREAK/MRET/WFI, the CSR
               read-modify-write family, and the fences. FENCE/FENCE.I live
               here although their opcode is MISC-MEM: the bucketing is
               *semantic*, and in this single-hart in-order model a fence's
               semantics is "no architectural effect beyond pc+4" — the same
               shape as the rest of the bucket.

Immediates are stored **pre-extended** as `BitVec 32`: the decoder does the
encoding-format scrambling and sign extension once, so the semantics in
`Exec.lean` (and every proof goal mentioning it) is plain 32-bit arithmetic
with no re-extension noise.

RVC (compressed) instructions do **not** get families of their own: the RVC
decoder in `Decode.lean` is an expander `BitVec 16 → Option (BitVec 32)` into
the 32-bit encoding, matching `cv32e40p_compressed_decoder.sv`, so every
compressed instruction decodes into the same six families.

## Sources

* RISC-V Unprivileged ISA, document version 20191213 (the version CV32E40P
  implements per its user manual `intro.rst`).
* sail-riscv (github.com/riscv/sail-riscv, BSD-2-Clause, RISC-V International)
  as reference model and table cross-check — used as a validation oracle and
  table mine, never as a term source (docs/litreview/SYNTHESIS.md §2).
* `cv32e40p_compressed_decoder.sv` (read directly) for the RVC expansion
  behavior at `FPU = 0`.
-/

namespace LeanModels.Rv

/-- Architectural register index (`x0`–`x31`). `x0` reads as zero; the zero is
enforced by the *writer* (`ArchState.writeReg` drops writes to `x0`), so reads
stay a bare function application. -/
abbrev Reg := Fin 32

/-! ## Operand sources

The two operand-source types are the model's copy of the ALU operand muxes:
`Src1` is "register or current pc" (OP/OP-IMM vs. AUIPC/JAL), `Src2` is
"register or immediate" (OP vs. OP-IMM/LUI). Keeping them as data (rather than
duplicating instruction families per operand shape) is the orthogonality the
bucketing exists for. -/

/-- First operand: a register, or the pc of the instruction itself. -/
inductive Src1 where
  | reg (r : Reg)
  | pc
  deriving DecidableEq, Repr

/-- Second operand: a register, or a pre-extended 32-bit immediate. -/
inductive Src2 where
  | reg (r : Reg)
  | imm (v : BitVec 32)
  deriving DecidableEq, Repr

/-! ## Operation enums -/

/-- The ten RV32I computational operations (`aluSem` in `Exec.lean` gives each
its `BitVec 32 → BitVec 32 → BitVec 32` meaning). Projection target for the
`cv32e40p_alu` conformance table (spec-surface entry 5). -/
inductive AluOp where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, Repr

/-- The eight M-extension operations (RV32M). Semantics: `mulDivSem`; the four
division ops share `Rv.divRem`, the projection target for `cv32e40p_alu_div`
(spec-surface entry 6). -/
inductive MulDivOp where
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr

/-- The four division operations, as their own enum because `Rv.divRem` is a
spec-surface artifact of its own (`cv32e40p_alu_div`'s `OpCode_SI`; the listing
order `divu, div, remu, rem` matches its `2'b00…2'b11` encoding). -/
inductive DivOp where
  | divu | div | remu | rem
  deriving DecidableEq, Repr

/-- Branch comparisons (funct3 order; `010`/`011` do not exist — the decoder
returns `none` for them). -/
inductive BranchCond where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

/-- Data-memory access width. -/
inductive MemW where
  | byte | half | word
  deriving DecidableEq, Repr

/-- Memory access direction. Sign extension is a load-only concept (LB/LH vs.
LBU/LHU), so the flag lives on `load` and a store cannot carry one. `LW`
decodes as `load (signed := true)`; at word width the extension is the
identity. -/
inductive MemDir where
  | load (signed : Bool)
  | store
  deriving DecidableEq, Repr

/-- CSR read-modify-write operator (CSRRW/CSRRS/CSRRC). -/
inductive CsrOp where
  | rw | rs | rc
  deriving DecidableEq, Repr

/-- CSR write operand: register (`csrrw/s/c`) or 5-bit zero-extended immediate
(`csrrw/s/ci`). -/
inductive CsrSrc where
  | reg (r : Reg)
  | imm (z : BitVec 5)
  deriving DecidableEq, Repr

/-- The system/environment family. `fence`/`fenceI` are MISC-MEM by opcode but
belong here semantically (see module docstring). The non-privileged `execInstr`
treats `ecall`, `ebreak`, `mret` and `csr` as *escapes* — state unchanged, the
op reported in `Effects.sys` — because their meaning (trap entry, CSR file) is
owned by the privileged phase. -/
inductive SysOp where
  | ecall | ebreak | mret | wfi | fence | fenceI
  | csr (op : CsrOp) (rd : Reg) (src : CsrSrc) (addr : BitVec 12)
  deriving DecidableEq, Repr

/-! ## Instructions -/

/-- One decoded RV32IM(C) instruction, in six semantic families (see the module
docstring for the bucketing rationale). All immediates/offsets are pre-extended
to 32 bits by the decoder. -/
inductive Instr where
  /-- `rd := aluSem op src1 src2`; covers OP, OP-IMM, LUI, AUIPC. -/
  | alu (op : AluOp) (rd : Reg) (src1 : Src1) (src2 : Src2)
  /-- `rd := mulDivSem op rs1 rs2` (RV32M; always register×register). -/
  | mulDiv (op : MulDivOp) (rd rs1 rs2 : Reg)
  /-- `if cond rs1 rs2 then pc += offset else pc += 4`; `offset` is the
  sign-extended, even B-immediate. -/
  | branch (cond : BranchCond) (rs1 rs2 : Reg) (offset : BitVec 32)
  /-- `rd := pc + 4; pc := base + offset` (JAL: `base = .pc`; JALR:
  `base = .reg rs1`, target bit 0 cleared per unpriv spec §2.5). -/
  | jump (rd : Reg) (base : Src1) (offset : BitVec 32)
  /-- One data-memory access at `rs1 + offset`. For loads `r` is the
  destination; for stores `r` is the data source (rs2). -/
  | mem (dir : MemDir) (width : MemW) (r rs1 : Reg) (offset : BitVec 32)
  /-- Environment interaction (see `SysOp`). -/
  | system (op : SysOp)
  deriving DecidableEq, Repr

/-! ## Architectural state -/

/-- The machine-mode CSR file: the scoped priv v1.11 subset ({`mstatus`
restricted to MIE/MPIE/MPP, `mtvec`, `mepc`, `mcause`, `mie`, `mscratch`},
`PULP_SECURE = 0`). Each field stores the CSR's full 32-bit *architectural
read value*, kept legalized as an invariant: reset defaults are fixed points
of the row legalizers in `Csr.lean`, and every write goes through
`CsrBehavior.legalize` (sail-riscv's `legalize_<csr>` shape, re-derived at
v1.11 field values against `cv32e40p_cs_registers.sv`). Nothing in the
non-privileged fragment reads this; `Csr.lean`/`Priv.lean`/`Step.lean` own
its semantics.

Reset values are the RTL's (`cv32e40p_cs_registers.sv` reset block):
`mstatus = 0x1800` (MPP reads as M, MIE/MPIE clear), `mtvec = 0x1` (base 0,
*vectored* mode — `MTVEC_MODE = 2'b01`; the RTL additionally loads the boot
base from the `mtvec_addr_i` port via `csr_mtvec_init_i`, which the model
expresses by starting from a non-default `CsrFile`), all others zero. -/
structure CsrFile where
  /-- `mstatus` (0x300) read value. Only bits 3 (MIE) and 7 (MPIE) are
  writable state; bits 12:11 (MPP) read as `11` (M) always. -/
  mstatus : BitVec 32 := 0x00001800
  /-- `mtvec` (0x305) read value: `base[31:8] ++ 0#6 ++ mode`; mode bit 1 is
  hardwired 0, so mode is `00` (direct) or `01` (vectored). -/
  mtvec : BitVec 32 := 0x00000001
  /-- `mepc` (0x341); bit 0 always clear (16-bit alignment, C extension). -/
  mepc : BitVec 32 := 0
  /-- `mcause` (0x342) read value: `interrupt ++ 0#26 ++ code[4:0]`. -/
  mcause : BitVec 32 := 0
  /-- `mie` (0x304); always a subset of `irqMask` (= RTL `IRQ_MASK`). -/
  mie : BitVec 32 := 0
  /-- `mscratch` (0x340); plain 32-bit scratch, no legalization. -/
  mscratch : BitVec 32 := 0
  deriving DecidableEq, Repr, Inhabited

/-- The architectural state of the non-privileged fragment: the integer
register file and the pc (plus the CSR-file placeholder). Data memory is *not*
state — `execInstr` consumes a memory view and reports accesses as `Effects`,
so the core-level proof can own the memory/bus model. -/
structure ArchState where
  regs : Reg → BitVec 32
  pc   : BitVec 32
  csrs : CsrFile := {}

/-- Read a register. `x0` reads as `0` on any state satisfying
`ArchState.WF` — maintained by `writeReg`, established by `init`. -/
def ArchState.readReg (s : ArchState) (r : Reg) : BitVec 32 :=
  s.regs r

/-- Write a register, enforcing the `x0` discipline: writes to `x0` are
dropped, so `regs 0 = 0` is an invariant of stepping, not a read-side patch.
This also makes encoded HINTs (e.g. RVC expansions targeting `x0`) execute as
architectural no-ops for free. -/
def ArchState.writeReg (s : ArchState) (r : Reg) (v : BitVec 32) : ArchState :=
  if r = 0 then s
  else { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Well-formedness: `x0` holds zero. `init` establishes it; `writeReg`
preserves it. -/
def ArchState.WF (s : ArchState) : Prop :=
  s.regs 0 = 0

/-- The all-zero register file at a given reset pc. -/
def ArchState.init (pc : BitVec 32) : ArchState :=
  { regs := fun _ => 0, pc := pc }

end LeanModels.Rv
