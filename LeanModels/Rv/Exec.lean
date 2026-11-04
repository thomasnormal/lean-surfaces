import LeanModels.Rv.Decode

/-!
# RV32IM execution: semantics tables and the non-privileged step

The semantics functions here are the projection sources for the CV32E40P
gallery (docs/cv32e40p-spec-surface.md):

* `aluSem`    — entry 5's `aluBaseSem` op table (`cv32e40p_alu` conformance);
* `Rv.divRem` — entry 6's width-generic division conventions
  (`cv32e40p_alu_div`'s `⊨tx` response, `OpCode_SI` order documented on
  `DivOp`);
* `mulDivSem` — the M-extension table (`cv32e40p_mult` + `alu_div`);
* `loadVal`/`storeVal` over byte-addressed little-endian memory — entry 9's
  `memSem` slice (any alignment, no misaligned trap: the LSU/controller
  replay makes misaligned accesses work, so the ISA-level semantics is total);
* `execInstr` — the fetch-free step: `Instr → ArchState → Mem → ArchState ×
  Effects`. "Fetch-free" = no instruction fetch is modeled (the instruction
  arrives decoded); data memory *is* consumed, because a load's writeback
  needs its data — the access is simultaneously reported in `Effects.mem`, and
  the produced write is **not** applied to memory by `execInstr` (memory is
  the platform's state; `execStep` is the convenience that applies it).

`Effects` is the per-instruction observable tuple (pc target + optional
memory access + optional system event) — the seed of the RVFI-style effect
tuple the retirement spec will consume (SYNTHESIS adoption #6).

Non-privileged fragment: `ecall`, `ebreak`, `mret` and the CSR family are
*escapes* — `execInstr` leaves the state unchanged (`pcTarget = pc`) and
reports the op in `Effects.sys`; the privileged phase owns the actual
transfer/CSR semantics. `wfi` and the fences retire as `pc + 4` no-ops (WFI
as nop is spec-legal, and is architecturally what CV32E40P's sleep+resume
amounts to), also flagged in `Effects.sys` so a platform can model
sleep/icache-flush.

Division conventions cross-checked against sail-riscv (BSD-2-Clause, RISC-V
International) and the golden vectors below.
-/

namespace LeanModels.Rv

/-! ## Computational semantics -/

/-- The RV32I ALU semantics table (spec-surface entry 5's `aluBaseSem`).
Shifts use only the low 5 bits of the second operand (unpriv spec 20191213
§2.4) — for immediate shifts the decoder already delivers the bare shamt. -/
def aluSem : AluOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add,  a, b => a + b
  | .sub,  a, b => a - b
  | .sll,  a, b => a <<< (b.extractLsb' 0 5)
  | .slt,  a, b => if a.slt b then 1 else 0
  | .sltu, a, b => if a.ult b then 1 else 0
  | .xor,  a, b => a ^^^ b
  | .srl,  a, b => a >>> (b.extractLsb' 0 5)
  | .sra,  a, b => a.sshiftRight' (b.extractLsb' 0 5)
  | .or,   a, b => a ||| b
  | .and,  a, b => a &&& b

/-- The M-extension division/remainder conventions, width-generic (this is the
`Rv.divRem` of spec-surface entry 6, the `cv32e40p_alu_div` transaction
response; `W = 32` in the ISA).

RISC-V Unprivileged ISA 20191213, §7.2 "Division Operations" (Table 7.1):

* **Division by zero**: quotient has *all bits set* (`DIV`: −1, `DIVU`:
  2^W − 1); remainder equals the *dividend*. No trap — the spec makes the
  result total so the M extension needs no exception path.
* **Signed overflow** (`intMin / −1`, the only overflowing case): `DIV`
  quotient = `intMin` (the dividend), `REM` remainder = 0. `DIVU`/`REMU`
  have no overflow case — for them `intMin`/`allOnes` are ordinary operands.
* Otherwise: quotients round toward zero; remainders take the dividend's
  sign (`BitVec.sdiv`/`srem` are exactly this t-division pair — the special
  cases above are spelled out anyway so the convention is visible in the
  definition, not buried in library behavior).

`DivOp`'s listing order (`divu, div, remu, rem`) matches `alu_div`'s 2-bit
`OpCode_SI`. -/
def divRem (W : Nat) (op : DivOp) (dividend divisor : BitVec W) : BitVec W :=
  match op with
  | .divu =>
    if divisor = 0 then BitVec.allOnes W
    else dividend / divisor
  | .div =>
    if divisor = 0 then BitVec.allOnes W  -- = −1
    else if dividend = BitVec.intMin W ∧ divisor = BitVec.allOnes W then
      BitVec.intMin W                     -- overflow: quotient = dividend
    else dividend.sdiv divisor
  | .remu =>
    if divisor = 0 then dividend
    else dividend % divisor
  | .rem =>
    if divisor = 0 then dividend
    else if dividend = BitVec.intMin W ∧ divisor = BitVec.allOnes W then
      0                                   -- overflow: remainder = 0
    else dividend.srem divisor

/-- The RV32M semantics table (unpriv spec 20191213 §7.1–7.2). The `MULH*`
family is the upper word of the widened product with the operands extended
per their signedness; the division ops delegate to `divRem` at `W = 32`. -/
def mulDivSem : MulDivOp → BitVec 32 → BitVec 32 → BitVec 32
  | .mul,    a, b => a * b
  | .mulh,   a, b => (a.signExtend 64 * b.signExtend 64).extractLsb' 32 32
  | .mulhsu, a, b => (a.signExtend 64 * b.setWidth 64).extractLsb' 32 32
  | .mulhu,  a, b => (a.setWidth 64 * b.setWidth 64).extractLsb' 32 32
  | .div,    a, b => divRem 32 .div  a b
  | .divu,   a, b => divRem 32 .divu a b
  | .rem,    a, b => divRem 32 .rem  a b
  | .remu,   a, b => divRem 32 .remu a b

/-- Branch comparison semantics (unpriv spec 20191213 §2.5). -/
def branchSem : BranchCond → BitVec 32 → BitVec 32 → Bool
  | .eq,  a, b => a == b
  | .ne,  a, b => a != b
  | .lt,  a, b => a.slt b
  | .ge,  a, b => !(a.slt b)
  | .ltu, a, b => a.ult b
  | .geu, a, b => !(a.ult b)

/-! ## Memory -/

/-- Byte-addressed little-endian memory view (spec-surface entry 9's
`AbstractMem`). Not part of `ArchState`: the platform owns it. -/
abbrev Mem := BitVec 32 → BitVec 8

/-- Bytes moved by an access width. -/
def MemW.bytes : MemW → Nat
  | .byte => 1
  | .half => 2
  | .word => 4

/-- Load a value: assemble `width` bytes little-endian from `addr` (any
alignment; addresses wrap mod 2^32), then sign- or zero-extend. At word width
the extension is the identity. -/
def loadVal (m : Mem) (width : MemW) (signed : Bool) (addr : BitVec 32) :
    BitVec 32 :=
  match width with
  | .byte => if signed then (m addr).signExtend 32 else (m addr).setWidth 32
  | .half =>
    let v : BitVec 16 := m (addr + 1) ++ m addr
    if signed then v.signExtend 32 else v.setWidth 32
  | .word => m (addr + 3) ++ m (addr + 2) ++ m (addr + 1) ++ m addr

/-- Store the low `width.bytes` bytes of `v` at `addr`, little-endian, any
alignment, wrapping mod 2^32. -/
def storeVal (m : Mem) (width : MemW) (addr v : BitVec 32) : Mem :=
  fun x =>
    let off := (x - addr).toNat
    if off < width.bytes then v.extractLsb' (8 * off) 8 else m x

/-! ## Effects and the step -/

/-- One data-memory access, as the instruction issues it (pre-split, any
alignment — the LSU's misaligned two-beat protocol is an implementation
refinement of this single access). -/
inductive MemEffect where
  | read  (addr : BitVec 32) (width : MemW)
  | write (addr : BitVec 32) (width : MemW) (data : BitVec 32)
  deriving DecidableEq, Repr

/-- The per-instruction observable effect tuple: the next pc the instruction
architecturally selects, the data-memory access it performs (if any; for
writes, `data` is the full rs2 value — `width` governs the bytes that land),
and the system event it raises (if any). For system *escapes* `pcTarget = pc`:
the non-privileged fragment does not define the transfer. -/
structure Effects where
  pcTarget : BitVec 32
  mem : Option MemEffect := none
  sys : Option SysOp := none
  deriving DecidableEq, Repr

/-- First-operand value: register read or the instruction's pc. -/
def src1Val (s : ArchState) : Src1 → BitVec 32
  | .reg r => s.readReg r
  | .pc    => s.pc

/-- Second-operand value: register read or pre-extended immediate. -/
def src2Val (s : ArchState) : Src2 → BitVec 32
  | .reg r => s.readReg r
  | .imm v => v

/-- Jump target. JAL (`base = .pc`): `pc + offset`, even by decode. JALR
(`base = .reg`): `(rs1 + offset)` with bit 0 cleared (unpriv spec 20191213
§2.5). -/
def jumpTarget (s : ArchState) (base : Src1) (offset : BitVec 32) : BitVec 32 :=
  match base with
  | .pc    => s.pc + offset
  | .reg r => (s.readReg r + offset) &&& ~~~(1#32)

/-- Does this system op escape the non-privileged fragment? (Trap entry and
CSR semantics belong to the privileged phase.) -/
def SysOp.isEscape : SysOp → Bool
  | .ecall | .ebreak | .mret | .csr .. => true
  | .wfi | .fence | .fenceI => false

/-- The non-privileged, fetch-free step: execute one decoded instruction.
Consumes a memory view for load data; reports the access (and never applies
its own write — see `execStep`). Invariants worth reading off the definition:
the returned state's `pc` always equals `Effects.pcTarget`; register writes go
through `writeReg`, so `x0` stays zero; JALR's target uses the *pre-write*
rs1, so `jalr x1, x1, imm` is correct by construction.

`ilen` is the byte length of the instruction's *encoding* (4, or 2 when it
came from a compressed halfword): it is where the sequential `pc` advances to
and what `jump` links (`c.jal` writes `pc + 2` to `x1`). Defaults to 4, so
plain 32-bit callers read as before; `Step.lean` passes `Fetched.size`. -/
def execInstr (i : Instr) (s : ArchState) (mem : Mem) (ilen : BitVec 32 := 4) :
    ArchState × Effects :=
  match i with
  | .alu op rd a b =>
    let next := s.pc + ilen
    ({ s.writeReg rd (aluSem op (src1Val s a) (src2Val s b)) with pc := next },
     { pcTarget := next })
  | .mulDiv op rd rs1 rs2 =>
    let next := s.pc + ilen
    ({ s.writeReg rd (mulDivSem op (s.readReg rs1) (s.readReg rs2)) with pc := next },
     { pcTarget := next })
  | .branch c rs1 rs2 offset =>
    let target :=
      if branchSem c (s.readReg rs1) (s.readReg rs2) then s.pc + offset
      else s.pc + ilen
    ({ s with pc := target }, { pcTarget := target })
  | .jump rd base offset =>
    let target := jumpTarget s base offset
    ({ s.writeReg rd (s.pc + ilen) with pc := target }, { pcTarget := target })
  | .mem (.load signed) width rd rs1 offset =>
    let addr := s.readReg rs1 + offset
    let next := s.pc + ilen
    ({ s.writeReg rd (loadVal mem width signed addr) with pc := next },
     { pcTarget := next, mem := some (.read addr width) })
  | .mem .store width rs2 rs1 offset =>
    let addr := s.readReg rs1 + offset
    let next := s.pc + ilen
    ({ s with pc := next },
     { pcTarget := next, mem := some (.write addr width (s.readReg rs2)) })
  | .system op =>
    if op.isEscape then
      (s, { pcTarget := s.pc, sys := some op })
    else
      ({ s with pc := s.pc + ilen }, { pcTarget := s.pc + ilen, sys := some op })

/-- Apply an instruction's memory effect to a memory (reads are no-ops). -/
def applyMemEffect (m : Mem) : Option MemEffect → Mem
  | some (.write addr width v) => storeVal m width addr v
  | _ => m

/-- Convenience driver: step state *and* memory together. -/
def execStep (i : Instr) (s : ArchState) (m : Mem) (ilen : BitVec 32 := 4) :
    ArchState × Mem :=
  let (s', eff) := execInstr i s m ilen
  (s', applyMemEffect m eff.mem)

/-! ## `#guard` battery: golden vectors per family

Values hand-derived from the unpriv spec 20191213 (§2.4–2.6, §7.1–7.2) and
cross-checked against sail-riscv's semantics; spike is not installed on this
machine, so the independent cross-check of encodings is llvm-mc (Decode.lean)
and of arithmetic the spec text itself. -/

private def m0 : Mem := fun _ => 0
private def mW : Mem := storeVal m0 .word 0x100 0xDEADBEEF
private def st (xs : List (Reg × BitVec 32)) : ArchState :=
  xs.foldl (fun s rv => s.writeReg rv.1 rv.2) (ArchState.init 0x1000)

/-! ### `aluSem` -/

#guard aluSem .add 0xFFFFFFFF#32 1 = 0            -- wraparound
#guard aluSem .sub 0 1 = 0xFFFFFFFF#32
#guard aluSem .sll 1 31 = 0x80000000#32
#guard aluSem .sll 1 32 = 1                       -- only the low 5 shift bits count
#guard aluSem .srl 0x80000000#32 31 = 1
#guard aluSem .sra 0x80000000#32 31 = 0xFFFFFFFF#32  -- arithmetic, not logical
#guard aluSem .sra 0xFFFFFF00#32 4 = 0xFFFFFFF0#32
#guard aluSem .slt 0xFFFFFFFF#32 0 = 1            -- −1 < 0 signed
#guard aluSem .slt 0 0xFFFFFFFF#32 = 0
#guard aluSem .sltu 0xFFFFFFFF#32 0 = 0           -- 2^32−1 not < 0 unsigned
#guard aluSem .sltu 0 0xFFFFFFFF#32 = 1
#guard aluSem .xor 0xF0F0F0F0#32 0xFFFFFFFF#32 = 0x0F0F0F0F#32

/-! ### `mulDivSem`: multiply family -/

#guard mulDivSem .mul 7 6 = 42
#guard mulDivSem .mul 0x80000000#32 2 = 0                          -- low word wraps
#guard mulDivSem .mulh 0xFFFFFFFF#32 0xFFFFFFFF#32 = 0             -- (−1)·(−1) = 1
#guard mulDivSem .mulhu 0xFFFFFFFF#32 0xFFFFFFFF#32 = 0xFFFFFFFE#32
#guard mulDivSem .mulhsu 0xFFFFFFFF#32 0xFFFFFFFF#32 = 0xFFFFFFFF#32 -- (−1)·(2^32−1)
#guard mulDivSem .mulh 0x80000000#32 0x80000000#32 = 0x40000000#32 -- (−2^31)² = 2^62
#guard mulDivSem .mulhu 0x80000000#32 0x80000000#32 = 0x40000000#32

/-! ### `Rv.divRem`: the §7.2 quirk battery (Table 7.1) -/

-- division by zero: quotient all ones, remainder = dividend — all four ops
#guard divRem 32 .div  10 0 = 0xFFFFFFFF#32
#guard divRem 32 .divu 10 0 = 0xFFFFFFFF#32
#guard divRem 32 .rem  10 0 = 10
#guard divRem 32 .remu 10 0 = 10
-- signed overflow (intMin / −1): quotient = intMin, remainder = 0
#guard divRem 32 .div 0x80000000#32 0xFFFFFFFF#32 = 0x80000000#32
#guard divRem 32 .rem 0x80000000#32 0xFFFFFFFF#32 = 0
-- …while the same operands are ordinary for the unsigned ops
#guard divRem 32 .divu 0x80000000#32 0xFFFFFFFF#32 = 0
#guard divRem 32 .remu 0x80000000#32 0xFFFFFFFF#32 = 0x80000000#32
-- rounding toward zero, remainder takes the dividend's sign
#guard divRem 32 .div 0xFFFFFFF9#32 2 = 0xFFFFFFFD#32              -- −7 / 2 = −3
#guard divRem 32 .rem 0xFFFFFFF9#32 2 = 0xFFFFFFFF#32              -- −7 % 2 = −1
#guard divRem 32 .div 7 0xFFFFFFFE#32 = 0xFFFFFFFD#32              -- 7 / −2 = −3
#guard divRem 32 .rem 7 0xFFFFFFFE#32 = 1                          -- 7 % −2 = 1
#guard divRem 32 .div 0xFFFFFFF9#32 0xFFFFFFFE#32 = 3              -- −7 / −2 = 3
#guard divRem 32 .rem 0xFFFFFFF9#32 0xFFFFFFFE#32 = 0xFFFFFFFF#32  -- −7 % −2 = −1
#guard divRem 32 .divu 7 2 = 3
#guard divRem 32 .remu 7 2 = 1
-- the conventions are width-generic (the alu_div crown jewel is ∀-width)
#guard divRem 8 .div 0x80#8 0xFF#8 = 0x80#8   -- overflow at W = 8
#guard divRem 8 .rem 0x80#8 0xFF#8 = 0
#guard divRem 16 .div 5 0 = 0xFFFF#16

/-! ### `branchSem` -/

#guard branchSem .eq 5 5 = true
#guard branchSem .lt 0xFFFFFFFF#32 0 = true    -- signed
#guard branchSem .ltu 0xFFFFFFFF#32 0 = false  -- unsigned
#guard branchSem .geu 0xFFFFFFFF#32 0 = true

/-! ### `execInstr` per family (base pc = 0x1000) -/

-- .alu: writeback + pc advance; wraparound add
#guard (execInstr (.alu .add 5 (.reg 6) (.reg 7)) (st [(6, 0xFFFFFFFF), (7, 1)]) m0).1.readReg 5 = 0
#guard (execInstr (.alu .add 5 (.reg 6) (.reg 7)) (st [(6, 0xFFFFFFFF), (7, 1)]) m0).2
         = { pcTarget := 0x1004 }
-- x0 write dropped (writer-enforced)
#guard (execInstr (.alu .add 0 (.reg 1) (.imm 5)) (st [(1, 7)]) m0).1.readReg 0 = 0
-- AUIPC shape: pc as first operand
#guard (execInstr (.alu .add 6 .pc (.imm 0x12345000#32)) (st []) m0).1.readReg 6 = 0x12346000#32
-- .mulDiv through the step
#guard (execInstr (.mulDiv .div 17 18 19) (st [(18, 0xFFFFFFF9), (19, 2)]) m0).1.readReg 17
         = 0xFFFFFFFD#32
-- .branch: taken / not taken / signed vs. unsigned
#guard (execInstr (.branch .eq 1 2 16) (st [(1, 5), (2, 5)]) m0).1.pc = 0x1010#32
#guard (execInstr (.branch .ne 1 2 16) (st [(1, 5), (2, 5)]) m0).1.pc = 0x1004#32
#guard (execInstr (.branch .lt 1 2 0xFFFFFFF0#32) (st [(1, 0xFFFFFFFF), (2, 0)]) m0).1.pc = 0xFF0#32
#guard (execInstr (.branch .ltu 1 2 16) (st [(1, 0xFFFFFFFF), (2, 0)]) m0).1.pc = 0x1004#32
#guard (execInstr (.branch .eq 1 2 16) (st [(1, 5), (2, 5)]) m0).2.mem = none
-- .jump: JAL links and redirects; JALR with rd = rs1 uses the OLD rs1 and
-- clears the target's bit 0
#guard (execInstr (.jump 1 .pc 2048) (st []) m0).1.readReg 1 = 0x1004#32
#guard (execInstr (.jump 1 .pc 2048) (st []) m0).1.pc = 0x1800#32
#guard (execInstr (.jump 1 (.reg 1) 0xFFFFFFFC#32) (st [(1, 0x2001)]) m0).1.pc = 0x1FFC#32
#guard (execInstr (.jump 1 (.reg 1) 0xFFFFFFFC#32) (st [(1, 0x2001)]) m0).1.readReg 1 = 0x1004#32
-- .mem loads: word, signed/unsigned byte, misaligned half (mW has the word
-- 0xDEADBEEF at 0x100, so bytes EF BE AD DE at 0x100..0x103)
#guard (execInstr (.mem (.load true) .word 7 1 0) (st [(1, 0x100)]) mW).1.readReg 7 = 0xDEADBEEF#32
#guard (execInstr (.mem (.load true) .word 7 1 0) (st [(1, 0x100)]) mW).2
         = { pcTarget := 0x1004, mem := some (.read 0x100 .word) }
#guard (execInstr (.mem (.load true)  .byte 5 1 3) (st [(1, 0x100)]) mW).1.readReg 5 = 0xFFFFFFDE#32
#guard (execInstr (.mem (.load false) .byte 5 1 3) (st [(1, 0x100)]) mW).1.readReg 5 = 0xDE#32
#guard (execInstr (.mem (.load true)  .half 5 1 1) (st [(1, 0x100)]) mW).1.readReg 5 = 0xFFFFADBE#32
-- .mem stores: effect reported, not applied by execInstr; execStep applies it
#guard (execInstr (.mem .store .half 5 1 0xFFFFFFFE#32) (st [(1, 0x200), (5, 0x12345678)]) m0).2
         = { pcTarget := 0x1004, mem := some (.write 0x1FE .half 0x12345678) }
#guard (execInstr (.mem .store .half 5 1 0xFFFFFFFE#32) (st [(1, 0x200), (5, 0x12345678)]) m0).1.pc
         = 0x1004#32
#guard ((execStep (.mem .store .half 5 1 0xFFFFFFFE#32) (st [(1, 0x200), (5, 0x12345678)]) m0).2 0x1FE)
         = 0x78#8
#guard ((execStep (.mem .store .half 5 1 0xFFFFFFFE#32) (st [(1, 0x200), (5, 0x12345678)]) m0).2 0x1FF)
         = 0x56#8
#guard ((execStep (.mem .store .half 5 1 0xFFFFFFFE#32) (st [(1, 0x200), (5, 0x12345678)]) m0).2 0x200)
         = 0x00#8
-- store wraps mod 2^32 at the address-space edge
#guard (storeVal m0 .word 0xFFFFFFFE#32 0x11223344#32) 0xFFFFFFFE#32 = 0x44#8
#guard (storeVal m0 .word 0xFFFFFFFE#32 0x11223344#32) 0xFFFFFFFF#32 = 0x33#8
#guard (storeVal m0 .word 0xFFFFFFFE#32 0x11223344#32) 0x0#32 = 0x22#8
#guard (storeVal m0 .word 0xFFFFFFFE#32 0x11223344#32) 0x1#32 = 0x11#8
-- .system: fences and wfi retire at pc+4; ecall/mret/csr escape in place
#guard (execInstr (.system .fence) (st []) m0).2 = { pcTarget := 0x1004, sys := some .fence }
#guard (execInstr (.system .wfi) (st []) m0).1.pc = 0x1004#32
#guard (execInstr (.system .ecall) (st []) m0).2 = { pcTarget := 0x1000, sys := some .ecall }
#guard (execInstr (.system .mret) (st []) m0).1.pc = 0x1000#32
#guard (execInstr (.system (.csr .rw 5 (.reg 6) 0x340)) (st [(6, 1)]) m0).2.pcTarget = 0x1000#32

/-! ### decode → exec, end to end (incl. RVC through `decode16`) -/

-- lui x5, 0xdeadb (0xdeadb2b7)
#guard (decode 0xdeadb2b7#32).map (fun i => (execInstr i (st []) m0).1.readReg 5)
         = some 0xdeadb000#32
-- c.addi16sp -512 on sp = 0x800
#guard (decode16 0x7101#16).map (fun i => (execInstr i (st [(2, 0x800)]) m0).1.readReg 2)
         = some 0x600#32
-- c.beqz x8, -6 with x8 = 0: taken, pc 0x1000 → 0xFFA
#guard (decode16 0xdc6d#16).map (fun i => (execInstr i (st []) m0).1.pc) = some 0xFFA#32
-- c.ebreak escapes
#guard (decode16 0x9002#16).map (fun i => (execInstr i (st []) m0).2.sys) = some (some .ebreak)

end LeanModels.Rv
