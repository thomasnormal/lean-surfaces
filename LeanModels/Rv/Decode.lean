import LeanModels.Rv.Ast

/-!
# RV32IM(C) decode: the table, the decoder, and the RVC expander

Two artifacts, both designed to be *consumed as data* by the CV32E40P
projection (spec-surface entry 7, `cv32e40p_decoder`):

1. `decodeTable : List DecodeRow` — the RV32IM + Zicsr/Zifencei encoding table
   as mask/value wildcard rows (`w &&& mask = value`), exactly the `InstrPat`
   shape entry 7's `decoder_conforms` / `decoder_illegal` theorems need.
   `decode` is nothing but "find the matching row"; the rows are pairwise
   disjoint, so match order is irrelevant (a future `decodeTable_disjoint`
   obligation, mirroring the RTL's `unique case` claim).
2. `expandC : BitVec 16 → Option (BitVec 32)` — the C-extension expander in
   the exact style of `cv32e40p_compressed_decoder.sv` (read directly,
   `FPU = 0`): a compressed instruction *expands to its 32-bit encoding* and
   then decodes through the same table, so RVC lands in the same six semantic
   families with zero duplicated semantics.

Honesty rules, matching the RTL and the ISA text (unpriv spec 20191213):

* Anything outside the table decodes to `none` — including the branch funct3
  holes (`010`/`011`), RV64-only loads (LD/LWU), SRET/URET/DRET, and every
  encoding with bits `[1:0] ≠ 11` (a compressed halfword is not a 32-bit
  instruction).
* `FENCE`/`FENCE.I` are matched on opcode+funct3 only (fm/pred/succ/rd/rs1
  don't-care), which is both the RTL's behavior and the spec's "treat unknown
  fence modes as a normal fence".
* RVC reserved encodings are `none` per the RTL at `FPU = 0`: the all-zero
  halfword and `c.addi4spn` with `nzuimm = 0`; the FP rows (C.FLD/FLW/FSD/FSW
  and the SP forms); `c.lui`/`c.addi16sp` with `nzimm = 0`; RV32 shifts with
  `shamt[5] = 1`; `c.subw`/`c.addw`; `c.jr` with `rs1 = 0`; `c.lwsp` with
  `rd = 0`. HINTs (`c.nop` with imm, `c.mv`/`c.slli`/… targeting `x0`) expand
  normally — the `x0` write discipline makes them architectural no-ops.

Encodings were transliterated from the ISA manual's encoding listings,
cross-checked against sail-riscv (BSD-2-Clause, RISC-V International; used as
reference, not imported) and, in `#guard` batteries below, against llvm-mc's
RISC-V assembler output (57 32-bit + 27 compressed golden encodings).
-/

namespace LeanModels.Rv

/-! ## Encoding fields -/

/-- Bits `[6:0]`: the major opcode. -/
def opcodeOf (w : BitVec 32) : BitVec 7 := w.extractLsb' 0 7

/-- Bits `[11:7]` as a register index (rd). -/
def rdOf (w : BitVec 32) : Reg := (w.extractLsb' 7 5).toFin

/-- Bits `[19:15]` as a register index (rs1). -/
def rs1Of (w : BitVec 32) : Reg := (w.extractLsb' 15 5).toFin

/-- Bits `[24:20]` as a register index (rs2). -/
def rs2Of (w : BitVec 32) : Reg := (w.extractLsb' 20 5).toFin

/-- I-type immediate, sign-extended: bits `[31:20]`. -/
def immI (w : BitVec 32) : BitVec 32 := (w.extractLsb' 20 12).signExtend 32

/-- S-type immediate, sign-extended: bits `[31:25] ++ [11:7]`. -/
def immS (w : BitVec 32) : BitVec 32 :=
  (w.extractLsb' 25 7 ++ w.extractLsb' 7 5).signExtend 32

/-- B-type immediate, sign-extended, even:
`[31] ++ [7] ++ [30:25] ++ [11:8] ++ 0`. -/
def immB (w : BitVec 32) : BitVec 32 :=
  (w.extractLsb' 31 1 ++ w.extractLsb' 7 1 ++ w.extractLsb' 25 6 ++
    w.extractLsb' 8 4 ++ 0#1).signExtend 32

/-- U-type immediate: bits `[31:12]`, low 12 bits zero. -/
def immU (w : BitVec 32) : BitVec 32 := w &&& 0xFFFFF000#32

/-- J-type immediate, sign-extended, even:
`[31] ++ [19:12] ++ [20] ++ [30:21] ++ 0`. -/
def immJ (w : BitVec 32) : BitVec 32 :=
  (w.extractLsb' 31 1 ++ w.extractLsb' 12 8 ++ w.extractLsb' 20 1 ++
    w.extractLsb' 21 10 ++ 0#1).signExtend 32

/-- Shift amount of an immediate shift, zero-extended: bits `[24:20]`. The AST
carries the effective 5-bit amount, not the raw I-immediate (which for SRAI
also contains the `0x400` funct7 bit). -/
def shamtOf (w : BitVec 32) : BitVec 32 := (w.extractLsb' 20 5).setWidth 32

/-- CSR address: bits `[31:20]`. -/
def csrOf (w : BitVec 32) : BitVec 12 := w.extractLsb' 20 12

/-! ## Instruction-word builders (shared by table values and the RVC expander) -/

def opcLOAD    : BitVec 7 := 0b0000011
def opcMISCMEM : BitVec 7 := 0b0001111
def opcOPIMM   : BitVec 7 := 0b0010011
def opcAUIPC   : BitVec 7 := 0b0010111
def opcSTORE   : BitVec 7 := 0b0100011
def opcOP      : BitVec 7 := 0b0110011
def opcLUI     : BitVec 7 := 0b0110111
def opcBRANCH  : BitVec 7 := 0b1100011
def opcJALR    : BitVec 7 := 0b1100111
def opcJAL     : BitVec 7 := 0b1101111
def opcSYSTEM  : BitVec 7 := 0b1110011

/-- R-type word: `funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode`. -/
def encR (funct7 : BitVec 7) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opc : BitVec 7) : BitVec 32 :=
  funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opc

/-- I-type word: `imm[11:0] ++ rs1 ++ funct3 ++ rd ++ opcode`. -/
def encI (imm : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opc : BitVec 7) : BitVec 32 :=
  imm ++ rs1 ++ funct3 ++ rd ++ opc

/-- S-type word: the immediate split `[11:5]`/`[4:0]`. -/
def encS (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opc : BitVec 7) : BitVec 32 :=
  imm.extractLsb' 5 7 ++ rs2 ++ rs1 ++ funct3 ++ imm.extractLsb' 0 5 ++ opc

/-- B-type word from a 13-bit even offset. -/
def encB (imm : BitVec 13) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opc : BitVec 7) : BitVec 32 :=
  imm.extractLsb' 12 1 ++ imm.extractLsb' 5 6 ++ rs2 ++ rs1 ++ funct3 ++
    imm.extractLsb' 1 4 ++ imm.extractLsb' 11 1 ++ opc

/-- U-type word: `imm[31:12] ++ rd ++ opcode`. -/
def encU (imm20 : BitVec 20) (rd : BitVec 5) (opc : BitVec 7) : BitVec 32 :=
  imm20 ++ rd ++ opc

/-- J-type word from a 21-bit even offset. -/
def encJ (imm : BitVec 21) (rd : BitVec 5) (opc : BitVec 7) : BitVec 32 :=
  imm.extractLsb' 20 1 ++ imm.extractLsb' 1 10 ++ imm.extractLsb' 11 1 ++
    imm.extractLsb' 12 8 ++ rd ++ opc

/-! ## The decode table -/

/-- One row of the decode table: a wildcard pattern (`w &&& mask = value`) and
the AST builder for matching words. This is the `InstrPat`/`DecodeRow` shape of
spec-surface entry 7 — the decoder-conformance projection consumes these rows
as data. -/
structure DecodeRow where
  mnemonic : String
  mask     : BitVec 32
  value    : BitVec 32
  build    : BitVec 32 → Instr

/-- Does a row match a word? -/
def DecodeRow.matches (row : DecodeRow) (w : BitVec 32) : Bool :=
  w &&& row.mask == row.value

/-- Row constraint masks: opcode only / opcode+funct3 / opcode+funct3+funct7 /
every bit. -/
def mOPC : BitVec 32 := 0x0000007F
def mF3  : BitVec 32 := 0x0000707F
def mF7  : BitVec 32 := 0xFE00707F
def mALL : BitVec 32 := 0xFFFFFFFF

/-! Row builders, one per operand shape. -/

def rowAluR (m : String) (funct7 : BitVec 7) (funct3 : BitVec 3) (op : AluOp) :
    DecodeRow :=
  { mnemonic := m, mask := mF7, value := encR funct7 0 0 funct3 0 opcOP
    build := fun w => .alu op (rdOf w) (.reg (rs1Of w)) (.reg (rs2Of w)) }

def rowAluI (m : String) (funct3 : BitVec 3) (op : AluOp) : DecodeRow :=
  { mnemonic := m, mask := mF3, value := encI 0 0 funct3 0 opcOPIMM
    build := fun w => .alu op (rdOf w) (.reg (rs1Of w)) (.imm (immI w)) }

def rowShiftI (m : String) (funct7 : BitVec 7) (funct3 : BitVec 3)
    (op : AluOp) : DecodeRow :=
  { mnemonic := m, mask := mF7, value := encI (funct7 ++ 0#5) 0 funct3 0 opcOPIMM
    build := fun w => .alu op (rdOf w) (.reg (rs1Of w)) (.imm (shamtOf w)) }

def rowMulDiv (m : String) (funct3 : BitVec 3) (op : MulDivOp) : DecodeRow :=
  { mnemonic := m, mask := mF7, value := encR 0b0000001 0 0 funct3 0 opcOP
    build := fun w => .mulDiv op (rdOf w) (rs1Of w) (rs2Of w) }

def rowBranch (m : String) (funct3 : BitVec 3) (c : BranchCond) : DecodeRow :=
  { mnemonic := m, mask := mF3, value := encB 0 0 0 funct3 opcBRANCH
    build := fun w => .branch c (rs1Of w) (rs2Of w) (immB w) }

def rowLoad (m : String) (funct3 : BitVec 3) (width : MemW) (signed : Bool) :
    DecodeRow :=
  { mnemonic := m, mask := mF3, value := encI 0 0 funct3 0 opcLOAD
    build := fun w => .mem (.load signed) width (rdOf w) (rs1Of w) (immI w) }

def rowStore (m : String) (funct3 : BitVec 3) (width : MemW) : DecodeRow :=
  { mnemonic := m, mask := mF3, value := encS 0 0 0 funct3 opcSTORE
    build := fun w => .mem .store width (rs2Of w) (rs1Of w) (immS w) }

def rowCsr (m : String) (funct3 : BitVec 3) (op : CsrOp) : DecodeRow :=
  { mnemonic := m, mask := mF3, value := encI 0 0 funct3 0 opcSYSTEM
    build := fun w => .system (.csr op (rdOf w) (.reg (rs1Of w)) (csrOf w)) }

def rowCsrI (m : String) (funct3 : BitVec 3) (op : CsrOp) : DecodeRow :=
  { mnemonic := m, mask := mF3, value := encI 0 0 funct3 0 opcSYSTEM
    build := fun w =>
      .system (.csr op (rdOf w) (.imm (w.extractLsb' 15 5)) (csrOf w)) }

/-- The RV32IM + Zicsr + Zifencei encoding table: 57 pairwise-disjoint
wildcard rows. Everything not matched here is an illegal (or unimplemented)
encoding and decodes to `none`. -/
def decodeTable : List DecodeRow := [
  -- OP (R-type)
  rowAluR "add"  0b0000000 0b000 .add,
  rowAluR "sub"  0b0100000 0b000 .sub,
  rowAluR "sll"  0b0000000 0b001 .sll,
  rowAluR "slt"  0b0000000 0b010 .slt,
  rowAluR "sltu" 0b0000000 0b011 .sltu,
  rowAluR "xor"  0b0000000 0b100 .xor,
  rowAluR "srl"  0b0000000 0b101 .srl,
  rowAluR "sra"  0b0100000 0b101 .sra,
  rowAluR "or"   0b0000000 0b110 .or,
  rowAluR "and"  0b0000000 0b111 .and,
  -- OP, funct7 = 0000001 (RV32M)
  rowMulDiv "mul"    0b000 .mul,
  rowMulDiv "mulh"   0b001 .mulh,
  rowMulDiv "mulhsu" 0b010 .mulhsu,
  rowMulDiv "mulhu"  0b011 .mulhu,
  rowMulDiv "div"    0b100 .div,
  rowMulDiv "divu"   0b101 .divu,
  rowMulDiv "rem"    0b110 .rem,
  rowMulDiv "remu"   0b111 .remu,
  -- OP-IMM
  rowAluI "addi"  0b000 .add,
  rowAluI "slti"  0b010 .slt,
  rowAluI "sltiu" 0b011 .sltu,
  rowAluI "xori"  0b100 .xor,
  rowAluI "ori"   0b110 .or,
  rowAluI "andi"  0b111 .and,
  rowShiftI "slli" 0b0000000 0b001 .sll,
  rowShiftI "srli" 0b0000000 0b101 .srl,
  rowShiftI "srai" 0b0100000 0b101 .sra,
  -- LUI / AUIPC: the `.alu` family with x0 / pc as first operand
  { mnemonic := "lui", mask := mOPC, value := (opcLUI.setWidth 32 : BitVec 32)
    build := fun w => .alu .add (rdOf w) (.reg 0) (.imm (immU w)) },
  { mnemonic := "auipc", mask := mOPC, value := (opcAUIPC.setWidth 32 : BitVec 32)
    build := fun w => .alu .add (rdOf w) .pc (.imm (immU w)) },
  -- JAL / JALR
  { mnemonic := "jal", mask := mOPC, value := (opcJAL.setWidth 32 : BitVec 32)
    build := fun w => .jump (rdOf w) .pc (immJ w) },
  { mnemonic := "jalr", mask := mF3, value := encI 0 0 0b000 0 opcJALR
    build := fun w => .jump (rdOf w) (.reg (rs1Of w)) (immI w) },
  -- BRANCH (funct3 010/011 are holes: no row, hence `none`)
  rowBranch "beq"  0b000 .eq,
  rowBranch "bne"  0b001 .ne,
  rowBranch "blt"  0b100 .lt,
  rowBranch "bge"  0b101 .ge,
  rowBranch "bltu" 0b110 .ltu,
  rowBranch "bgeu" 0b111 .geu,
  -- LOAD / STORE (RV32: no ld/lwu; store funct3 > 010 is a hole)
  rowLoad "lb"  0b000 .byte true,
  rowLoad "lh"  0b001 .half true,
  rowLoad "lw"  0b010 .word true,
  rowLoad "lbu" 0b100 .byte false,
  rowLoad "lhu" 0b101 .half false,
  rowStore "sb" 0b000 .byte,
  rowStore "sh" 0b001 .half,
  rowStore "sw" 0b010 .word,
  -- MISC-MEM: fm/pred/succ/rd/rs1 are don't-care (normal-fence fallback)
  { mnemonic := "fence", mask := mF3, value := encI 0 0 0b000 0 opcMISCMEM
    build := fun _ => .system .fence },
  { mnemonic := "fence.i", mask := mF3, value := encI 0 0 0b001 0 opcMISCMEM
    build := fun _ => .system .fenceI },
  -- SYSTEM, funct3 = 000: exact-match words (SRET/URET/DRET have no row)
  { mnemonic := "ecall", mask := mALL, value := encI 0b000000000000 0 0b000 0 opcSYSTEM
    build := fun _ => .system .ecall },
  { mnemonic := "ebreak", mask := mALL, value := encI 0b000000000001 0 0b000 0 opcSYSTEM
    build := fun _ => .system .ebreak },
  { mnemonic := "mret", mask := mALL, value := encI 0b001100000010 0 0b000 0 opcSYSTEM
    build := fun _ => .system .mret },
  { mnemonic := "wfi", mask := mALL, value := encI 0b000100000101 0 0b000 0 opcSYSTEM
    build := fun _ => .system .wfi },
  -- SYSTEM, Zicsr
  rowCsr  "csrrw"  0b001 .rw,
  rowCsr  "csrrs"  0b010 .rs,
  rowCsr  "csrrc"  0b011 .rc,
  rowCsrI "csrrwi" 0b101 .rw,
  rowCsrI "csrrsi" 0b110 .rs,
  rowCsrI "csrrci" 0b111 .rc]

/-- Decode one 32-bit instruction word. `none` = illegal (nothing in the table
matches — including all compressed halfword patterns, bits `[1:0] ≠ 11`). -/
def decode (w : BitVec 32) : Option Instr :=
  (decodeTable.find? (·.matches w)).map (·.build w)

/-! ## The RVC expander

`expandC` maps a 16-bit halfword to the 32-bit encoding of its expansion —
the same contract as `cv32e40p_compressed_decoder.sv` (`FPU = 0`), with
`none` where the RTL raises `illegal_instr_o`. Immediate reassembly helpers
below name the scrambled fields once each. -/

/-- Compressed 3-bit register: `x8 + r`. -/
def cReg (r : BitVec 3) : BitVec 5 := 0b01#2 ++ r

/-- `c.addi4spn` zero-extended immediate: `[9:6]=h[10:7], [5:4]=h[12:11],
[3]=h[5], [2]=h[6]`. -/
def cImmAddi4spn (h : BitVec 16) : BitVec 12 :=
  0#2 ++ h.extractLsb' 7 4 ++ h.extractLsb' 11 2 ++ h.extractLsb' 5 1 ++
    h.extractLsb' 6 1 ++ 0#2

/-- `c.lw`/`c.sw` zero-extended immediate: `[6]=h[5], [5:3]=h[12:10],
[2]=h[6]`. -/
def cImmLw (h : BitVec 16) : BitVec 12 :=
  0#5 ++ h.extractLsb' 5 1 ++ h.extractLsb' 10 3 ++ h.extractLsb' 6 1 ++ 0#2

/-- `c.addi`/`c.li`/`c.andi` sign-extended immediate: `[5]=h[12],
[4:0]=h[6:2]`. -/
def cImm6 (h : BitVec 16) : BitVec 12 :=
  (h.extractLsb' 12 1 ++ h.extractLsb' 2 5).signExtend 12

/-- `c.lui` immediate as a U-type `imm[31:12]` field: `h[12]` sign-extended
over `[19:6]`, `[4:0]=h[6:2]`. -/
def cImmLui (h : BitVec 16) : BitVec 20 :=
  (h.extractLsb' 12 1 ++ h.extractLsb' 2 5).signExtend 20

/-- `c.addi16sp` sign-extended immediate: `[9]=h[12], [8:7]=h[4:3], [6]=h[5],
[5]=h[2], [4]=h[6]`, low four bits zero. -/
def cImmAddi16sp (h : BitVec 16) : BitVec 12 :=
  (h.extractLsb' 12 1 ++ h.extractLsb' 3 2 ++ h.extractLsb' 5 1 ++
    h.extractLsb' 2 1 ++ h.extractLsb' 6 1 ++ 0#4).signExtend 12

/-- `c.j`/`c.jal` sign-extended even offset: `[11]=h[12], [10]=h[8],
[9:8]=h[10:9], [7]=h[6], [6]=h[7], [5]=h[2], [4]=h[11], [3:1]=h[5:3]`. -/
def cImmJ (h : BitVec 16) : BitVec 21 :=
  (h.extractLsb' 12 1 ++ h.extractLsb' 8 1 ++ h.extractLsb' 9 2 ++
    h.extractLsb' 6 1 ++ h.extractLsb' 7 1 ++ h.extractLsb' 2 1 ++
    h.extractLsb' 11 1 ++ h.extractLsb' 3 3 ++ 0#1).signExtend 21

/-- `c.beqz`/`c.bnez` sign-extended even offset: `[8]=h[12], [7:6]=h[6:5],
[5]=h[2], [4:3]=h[11:10], [2:1]=h[4:3]`. -/
def cImmB (h : BitVec 16) : BitVec 13 :=
  (h.extractLsb' 12 1 ++ h.extractLsb' 5 2 ++ h.extractLsb' 2 1 ++
    h.extractLsb' 10 2 ++ h.extractLsb' 3 2 ++ 0#1).signExtend 13

/-- `c.lwsp` zero-extended immediate: `[7:6]=h[3:2], [5]=h[12],
[4:2]=h[6:4]`. -/
def cImmLwsp (h : BitVec 16) : BitVec 12 :=
  0#4 ++ h.extractLsb' 2 2 ++ h.extractLsb' 12 1 ++ h.extractLsb' 4 3 ++ 0#2

/-- `c.swsp` zero-extended immediate: `[7:6]=h[8:7], [5:2]=h[12:9]`. -/
def cImmSwsp (h : BitVec 16) : BitVec 12 :=
  0#4 ++ h.extractLsb' 7 2 ++ h.extractLsb' 9 4 ++ 0#2

/-- Expand a compressed halfword to its 32-bit encoding, or `none` if illegal.
Matches `cv32e40p_compressed_decoder.sv` at `FPU = 0` (see the module
docstring for the exact reserved/illegal set; HINTs expand normally). -/
def expandC (h : BitVec 16) : Option (BitVec 32) :=
  let r97 := cReg (h.extractLsb' 7 3)   -- rd'/rs1' (compressed register set)
  let r42 := cReg (h.extractLsb' 2 3)   -- rd'/rs2'
  let rd  := h.extractLsb' 7 5          -- full rd/rs1 field (quadrants 1/2)
  let rs2 := h.extractLsb' 2 5          -- full rs2 field (quadrant 2)
  match (h.extractLsb' 0 2).toNat, (h.extractLsb' 13 3).toNat with
  -- ── quadrant 0 ──
  | 0b00, 0b000 =>  -- c.addi4spn → addi rd', x2, nzuimm  (nzuimm = 0 reserved,
                    -- which also catches the canonical all-zero illegal word)
    if h.extractLsb' 5 8 = 0 then none
    else some (encI (cImmAddi4spn h) 2 0b000 r42 opcOPIMM)
  | 0b00, 0b010 =>  -- c.lw → lw rd', uimm(rs1')
    some (encI (cImmLw h) r97 0b010 r42 opcLOAD)
  | 0b00, 0b110 =>  -- c.sw → sw rs2', uimm(rs1')
    some (encS (cImmLw h) r42 r97 0b010 opcSTORE)
  -- ── quadrant 1 ──
  | 0b01, 0b000 =>  -- c.addi → addi rd, rd, imm  (c.nop and imm-HINTs included)
    some (encI (cImm6 h) rd 0b000 rd opcOPIMM)
  | 0b01, 0b001 =>  -- c.jal → jal x1, off  (RV32 encoding)
    some (encJ (cImmJ h) 1 opcJAL)
  | 0b01, 0b010 =>  -- c.li → addi rd, x0, imm
    some (encI (cImm6 h) 0 0b000 rd opcOPIMM)
  | 0b01, 0b011 =>  -- c.addi16sp / c.lui  (nzimm = 0 reserved)
    if h.extractLsb' 12 1 ++ h.extractLsb' 2 5 = (0 : BitVec 6) then none
    else if rd = 2 then some (encI (cImmAddi16sp h) 2 0b000 2 opcOPIMM)
    else some (encU (cImmLui h) rd opcLUI)
  | 0b01, 0b100 =>  -- shifts / andi / register-register ops on rd'
    match (h.extractLsb' 10 2).toNat with
    | 0b00 =>       -- c.srli → srli rd', rd', shamt  (RV32: shamt[5] = 1 reserved)
      if h[12] then none
      else some (encI (0b0000000#7 ++ h.extractLsb' 2 5) r97 0b101 r97 opcOPIMM)
    | 0b01 =>       -- c.srai → srai rd', rd', shamt
      if h[12] then none
      else some (encI (0b0100000#7 ++ h.extractLsb' 2 5) r97 0b101 r97 opcOPIMM)
    | 0b10 =>       -- c.andi → andi rd', rd', imm
      some (encI (cImm6 h) r97 0b111 r97 opcOPIMM)
    | _ =>          -- c.sub/c.xor/c.or/c.and  (h[12] = 1: c.subw/c.addw, RV64 only)
      if h[12] then none
      else match (h.extractLsb' 5 2).toNat with
        | 0b00 => some (encR 0b0100000 r42 r97 0b000 r97 opcOP)
        | 0b01 => some (encR 0b0000000 r42 r97 0b100 r97 opcOP)
        | 0b10 => some (encR 0b0000000 r42 r97 0b110 r97 opcOP)
        | _    => some (encR 0b0000000 r42 r97 0b111 r97 opcOP)
  | 0b01, 0b101 =>  -- c.j → jal x0, off
    some (encJ (cImmJ h) 0 opcJAL)
  | 0b01, 0b110 =>  -- c.beqz → beq rs1', x0, off
    some (encB (cImmB h) 0 r97 0b000 opcBRANCH)
  | 0b01, 0b111 =>  -- c.bnez → bne rs1', x0, off
    some (encB (cImmB h) 0 r97 0b001 opcBRANCH)
  -- ── quadrant 2 ──
  | 0b10, 0b000 =>  -- c.slli → slli rd, rd, shamt  (RV32: shamt[5] = 1 reserved)
    if h[12] then none
    else some (encI (0b0000000#7 ++ h.extractLsb' 2 5) rd 0b001 rd opcOPIMM)
  | 0b10, 0b010 =>  -- c.lwsp → lw rd, uimm(x2)  (rd = 0 reserved)
    if rd = 0 then none
    else some (encI (cImmLwsp h) 2 0b010 rd opcLOAD)
  | 0b10, 0b100 =>  -- c.jr / c.mv / c.ebreak / c.jalr / c.add
    if h[12] = false then
      if rs2 = 0 then
        if rd = 0 then none  -- c.jr with rs1 = 0 is reserved
        else some (encI 0 rd 0b000 0 opcJALR)          -- c.jr → jalr x0, rs1, 0
      else some (encR 0b0000000 rs2 0 0b000 rd opcOP)  -- c.mv → add rd, x0, rs2
    else
      if rs2 = 0 then
        if rd = 0 then some (encI 1 0 0b000 0 opcSYSTEM)  -- c.ebreak → ebreak
        else some (encI 0 rd 0b000 1 opcJALR)          -- c.jalr → jalr x1, rs1, 0
      else some (encR 0b0000000 rs2 rd 0b000 rd opcOP) -- c.add → add rd, rd, rs2
  | 0b10, 0b110 =>  -- c.swsp → sw rs2, uimm(x2)
    some (encS (cImmSwsp h) rs2 2 0b010 opcSTORE)
  -- everything else: FP rows at FPU = 0 (001/011/101/111 in quadrants 0 and
  -- 2), the reserved quadrant-0 100 row, and quadrant 3 (not compressed)
  | _, _ => none

/-- Decode a compressed halfword into the same six semantic families, by
expansion. `none` = illegal compressed encoding (or one whose expansion is
outside RV32IM — impossible by construction of `expandC`, a future lemma). -/
def decode16 (h : BitVec 16) : Option Instr :=
  (expandC h).bind decode

/-! ## `#guard` battery: 32-bit decode golden vectors

Encodings produced by llvm-mc (`-triple=riscv32 -mattr=+m,+zicsr,+zifencei`),
expectations hand-derived from the ISA text. One vector per table row family,
plus edge immediates. -/

-- OP
#guard decode 0x007302b3#32 = some (.alu .add  5 (.reg 6) (.reg 7))    -- add x5, x6, x7
#guard decode 0x40c58533#32 = some (.alu .sub  10 (.reg 11) (.reg 12)) -- sub x10, x11, x12
#guard decode 0x003110b3#32 = some (.alu .sll  1 (.reg 2) (.reg 3))    -- sll x1, x2, x3
#guard decode 0x0062a233#32 = some (.alu .slt  4 (.reg 5) (.reg 6))    -- slt x4, x5, x6
#guard decode 0x009433b3#32 = some (.alu .sltu 7 (.reg 8) (.reg 9))    -- sltu x7, x8, x9
#guard decode 0x00f746b3#32 = some (.alu .xor  13 (.reg 14) (.reg 15)) -- xor x13, x14, x15
#guard decode 0x0128d833#32 = some (.alu .srl  16 (.reg 17) (.reg 18)) -- srl x16, x17, x18
#guard decode 0x415a59b3#32 = some (.alu .sra  19 (.reg 20) (.reg 21)) -- sra x19, x20, x21
#guard decode 0x018beb33#32 = some (.alu .or   22 (.reg 23) (.reg 24)) -- or x22, x23, x24
#guard decode 0x01bd7cb3#32 = some (.alu .and  25 (.reg 26) (.reg 27)) -- and x25, x26, x27
-- OP-IMM (immediates arrive sign-extended; shifts carry the bare shamt)
#guard decode 0xffb10093#32 = some (.alu .add  1 (.reg 2) (.imm 0xFFFFFFFB#32)) -- addi x1, x2, -5
#guard decode 0x06422193#32 = some (.alu .slt  3 (.reg 4) (.imm 100))  -- slti x3, x4, 100
#guard decode 0x06433293#32 = some (.alu .sltu 5 (.reg 6) (.imm 100))  -- sltiu x5, x6, 100
#guard decode 0x7ff44393#32 = some (.alu .xor  7 (.reg 8) (.imm 2047)) -- xori x7, x8, 2047
#guard decode 0x80056493#32 = some (.alu .or   9 (.reg 10) (.imm 0xFFFFF800#32)) -- ori x9, x10, -2048
#guard decode 0x0ff67593#32 = some (.alu .and  11 (.reg 12) (.imm 255)) -- andi x11, x12, 255
#guard decode 0x01f71693#32 = some (.alu .sll  13 (.reg 14) (.imm 31)) -- slli x13, x14, 31
#guard decode 0x00185793#32 = some (.alu .srl  15 (.reg 16) (.imm 1))  -- srli x15, x16, 1
#guard decode 0x40795893#32 = some (.alu .sra  17 (.reg 18) (.imm 7))  -- srai x17, x18, 7
-- LUI / AUIPC as `.alu` with x0 / pc
#guard decode 0xdeadb2b7#32 = some (.alu .add 5 (.reg 0) (.imm 0xdeadb000#32)) -- lui x5, 0xdeadb
#guard decode 0x12345317#32 = some (.alu .add 6 .pc (.imm 0x12345000#32))      -- auipc x6, 0x12345
-- RV32M
#guard decode 0x027302b3#32 = some (.mulDiv .mul    5 6 7)    -- mul x5, x6, x7
#guard decode 0x02a49433#32 = some (.mulDiv .mulh   8 9 10)   -- mulh x8, x9, x10
#guard decode 0x02d625b3#32 = some (.mulDiv .mulhsu 11 12 13) -- mulhsu x11, x12, x13
#guard decode 0x0307b733#32 = some (.mulDiv .mulhu  14 15 16) -- mulhu x14, x15, x16
#guard decode 0x033948b3#32 = some (.mulDiv .div    17 18 19) -- div x17, x18, x19
#guard decode 0x036ada33#32 = some (.mulDiv .divu   20 21 22) -- divu x20, x21, x22
#guard decode 0x039c6bb3#32 = some (.mulDiv .rem    23 24 25) -- rem x23, x24, x25
#guard decode 0x03cdfd33#32 = some (.mulDiv .remu   26 27 28) -- remu x26, x27, x28
-- JAL / JALR
#guard decode 0x001000ef#32 = some (.jump 1 .pc 2048)                 -- jal x1, 2048
#guard decode 0xffc100e7#32 = some (.jump 1 (.reg 2) 0xFFFFFFFC#32)   -- jalr x1, x2, -4
-- BRANCH (offsets sign-extended and even; ±4 KiB extremes included)
#guard decode 0x00208863#32 = some (.branch .eq  1 2 16)              -- beq x1, x2, 16
#guard decode 0xfe4198e3#32 = some (.branch .ne  3 4 0xFFFFFFF0#32)   -- bne x3, x4, -16
#guard decode 0x7e62cfe3#32 = some (.branch .lt  5 6 4094)            -- blt x5, x6, 4094
#guard decode 0x8083d063#32 = some (.branch .ge  7 8 0xFFFFF000#32)   -- bge x7, x8, -4096
#guard decode 0x02a4e063#32 = some (.branch .ltu 9 10 32)             -- bltu x9, x10, 32
#guard decode 0xfcc5f0e3#32 = some (.branch .geu 11 12 0xFFFFFFC0#32) -- bgeu x11, x12, -64
-- LOAD / STORE
#guard decode 0xfff50283#32 = some (.mem (.load true)  .byte 5 10 0xFFFFFFFF#32) -- lb x5, -1(x10)
#guard decode 0x00259303#32 = some (.mem (.load true)  .half 6 11 2)             -- lh x6, 2(x11)
#guard decode 0x00462383#32 = some (.mem (.load true)  .word 7 12 4)             -- lw x7, 4(x12)
#guard decode 0x0ff6c403#32 = some (.mem (.load false) .byte 8 13 255)           -- lbu x8, 255(x13)
#guard decode 0x80075483#32 = some (.mem (.load false) .half 9 14 0xFFFFF800#32) -- lhu x9, -2048(x14)
#guard decode 0x005503a3#32 = some (.mem .store .byte 5 10 7)             -- sb x5, 7(x10)
#guard decode 0xfe659f23#32 = some (.mem .store .half 6 11 0xFFFFFFFE#32) -- sh x6, -2(x11)
#guard decode 0x7e762fa3#32 = some (.mem .store .word 7 12 2047)          -- sw x7, 2047(x12)
-- MISC-MEM / SYSTEM
#guard decode 0x0ff0000f#32 = some (.system .fence)   -- fence (iorw, iorw)
#guard decode 0x0000100f#32 = some (.system .fenceI)  -- fence.i
#guard decode 0x00000073#32 = some (.system .ecall)
#guard decode 0x00100073#32 = some (.system .ebreak)
#guard decode 0x30200073#32 = some (.system .mret)
#guard decode 0x10500073#32 = some (.system .wfi)
-- Zicsr (mscratch 0x340, mstatus 0x300, mepc 0x341, mie 0x304, mcause 0x342)
#guard decode 0x340312f3#32 = some (.system (.csr .rw 5 (.reg 6) 0x340)) -- csrrw x5, mscratch, x6
#guard decode 0x30002073#32 = some (.system (.csr .rs 0 (.reg 0) 0x300)) -- csrrs x0, mstatus, x0
#guard decode 0x341433f3#32 = some (.system (.csr .rc 7 (.reg 8) 0x341)) -- csrrc x7, mepc, x8
#guard decode 0x340ad2f3#32 = some (.system (.csr .rw 5 (.imm 21) 0x340)) -- csrrwi x5, mscratch, 21
#guard decode 0x304fe373#32 = some (.system (.csr .rs 6 (.imm 31) 0x304)) -- csrrsi x6, mie, 31
#guard decode 0x3420f3f3#32 = some (.system (.csr .rc 7 (.imm 1) 0x342))  -- csrrci x7, mcause, 1

/-! Illegal 32-bit encodings: holes stay holes. -/

#guard decode 0x00000000#32 = none  -- canonical illegal
#guard decode 0xFFFFFFFF#32 = none  -- canonical illegal
#guard decode 0x40001033#32 = none  -- OP funct3=001 with funct7=0100000
#guard decode 0x02001013#32 = none  -- slli with funct7=0000001
#guard decode 0x00003003#32 = none  -- LOAD funct3=011 (ld, RV64 only)
#guard decode 0x00006003#32 = none  -- LOAD funct3=110 (lwu is RV64 only)
#guard decode 0x00007023#32 = none  -- STORE funct3=111 (sd, RV64 only)
#guard decode 0x00002063#32 = none  -- BRANCH funct3=010 hole
#guard decode 0x0000200f#32 = none  -- MISC-MEM funct3=010 hole
#guard decode 0x10200073#32 = none  -- sret (S-mode not implemented)
#guard decode 0x00200073#32 = none  -- uret (priv 1.11 N-extension, not implemented)
#guard decode 0x7b200073#32 = none  -- dret (debug out of the model's scope)
#guard decode 0x00000001#32 = none  -- bits [1:0] ≠ 11: compressed, not a 32-bit word
#guard decode 0x00004067#32 = none  -- JALR funct3=100

/-! ## `#guard` battery: RVC expansion golden vectors

Pairs cross-checked with llvm-mc: left column assembled with `+c`, right
column the expansion assembled without `+c`. -/

#guard expandC 0x1020#16 = some 0x02810413#32  -- c.addi4spn x8, sp, 40 → addi x8, x2, 40
#guard expandC 0x4144#16 = some 0x00452483#32  -- c.lw x9, 4(x10)       → lw x9, 4(x10)
#guard expandC 0xdff8#16 = some 0x06e7ae23#32  -- c.sw x14, 124(x15)    → sw x14, 124(x15)
#guard expandC 0x0001#16 = some 0x00000013#32  -- c.nop                 → addi x0, x0, 0
#guard expandC 0x17fd#16 = some 0xfff78793#32  -- c.addi x15, -1        → addi x15, x15, -1
#guard expandC 0x2095#16 = some 0x064000ef#32  -- c.jal 100             → jal x1, 100
#guard expandC 0xbf71#16 = some 0xf9dff06f#32  -- c.j -100              → jal x0, -100
#guard expandC 0x5501#16 = some 0xfe000513#32  -- c.li x10, -32         → addi x10, x0, -32
#guard expandC 0x678d#16 = some 0x000037b7#32  -- c.lui x15, 3          → lui x15, 3
#guard expandC 0x7101#16 = some 0xe0010113#32  -- c.addi16sp -512       → addi x2, x2, -512
#guard expandC 0x800d#16 = some 0x00345413#32  -- c.srli x8, 3          → srli x8, x8, 3
#guard expandC 0x849d#16 = some 0x4074d493#32  -- c.srai x9, 7          → srai x9, x9, 7
#guard expandC 0x996d#16 = some 0xffb57513#32  -- c.andi x10, -5        → andi x10, x10, -5
#guard expandC 0x8c05#16 = some 0x40940433#32  -- c.sub x8, x9          → sub x8, x8, x9
#guard expandC 0x8ca9#16 = some 0x00a4c4b3#32  -- c.xor x9, x10         → xor x9, x9, x10
#guard expandC 0x8d4d#16 = some 0x00b56533#32  -- c.or x10, x11         → or x10, x10, x11
#guard expandC 0x8df1#16 = some 0x00c5f5b3#32  -- c.and x11, x12        → and x11, x11, x12
#guard expandC 0xdc6d#16 = some 0xfe040de3#32  -- c.beqz x8, -6         → beq x8, x0, -6
#guard expandC 0xe491#16 = some 0x00049663#32  -- c.bnez x9, 12         → bne x9, x0, 12
#guard expandC 0x02a6#16 = some 0x00929293#32  -- c.slli x5, 9          → slli x5, x5, 9
#guard expandC 0x53b2#16 = some 0x02c12383#32  -- c.lwsp x7, 44(sp)     → lw x7, 44(x2)
#guard expandC 0xd032#16 = some 0x02c12023#32  -- c.swsp x12, 32(sp)    → sw x12, 32(x2)
#guard expandC 0x8582#16 = some 0x00058067#32  -- c.jr x11              → jalr x0, x11, 0
#guard expandC 0x9582#16 = some 0x000580e7#32  -- c.jalr x11            → jalr x1, x11, 0
#guard expandC 0x829a#16 = some 0x006002b3#32  -- c.mv x5, x6           → add x5, x0, x6
#guard expandC 0x929a#16 = some 0x006282b3#32  -- c.add x5, x6          → add x5, x5, x6
#guard expandC 0x9002#16 = some 0x00100073#32  -- c.ebreak              → ebreak

/-! Illegal/reserved compressed encodings (cv32e40p behavior at `FPU = 0`). -/

#guard expandC 0x0000#16 = none  -- all-zero halfword (c.addi4spn nzuimm=0)
#guard expandC 0x2000#16 = none  -- c.fld  (FPU = 0)
#guard expandC 0x6000#16 = none  -- c.flw  (FPU = 0)
#guard expandC 0xa000#16 = none  -- c.fsd  (FPU = 0)
#guard expandC 0xe000#16 = none  -- c.fsw  (FPU = 0)
#guard expandC 0x8000#16 = none  -- quadrant-0 funct3=100 reserved row
#guard expandC 0x2002#16 = none  -- c.fldsp (FPU = 0)
#guard expandC 0x6781#16 = none  -- c.lui x15, 0 (nzimm = 0 reserved)
#guard expandC 0x9001#16 = none  -- c.srli64: shamt[5]=1 reserved in RV32
#guard expandC 0x1082#16 = none  -- c.slli x1 with shamt[5]=1
#guard expandC 0x9c01#16 = none  -- c.subw (RV64 only)
#guard expandC 0x8002#16 = none  -- c.jr x0 (reserved)
#guard expandC 0x400a#16 = none  -- c.lwsp x0 (reserved)

/-! RVC lands in the same families: `decode16` spot checks, plus a closure
check that every legal vector above decodes to a family. -/

#guard decode16 0x1020#16 = some (.alu .add 8 (.reg 2) (.imm 40))          -- c.addi4spn
#guard decode16 0x4144#16 = some (.mem (.load true) .word 9 10 4)          -- c.lw
#guard decode16 0x5501#16 = some (.alu .add 10 (.reg 0) (.imm 0xFFFFFFE0#32)) -- c.li
#guard decode16 0x7101#16 = some (.alu .add 2 (.reg 2) (.imm 0xFFFFFE00#32))  -- c.addi16sp
#guard decode16 0xbf71#16 = some (.jump 0 .pc 0xFFFFFF9C#32)               -- c.j -100
#guard decode16 0xdc6d#16 = some (.branch .eq 8 0 0xFFFFFFFA#32)           -- c.beqz -6
#guard decode16 0x9582#16 = some (.jump 1 (.reg 11) 0)                     -- c.jalr x11
#guard decode16 0x9002#16 = some (.system .ebreak)                         -- c.ebreak

#guard [0x1020#16, 0x4144, 0xdff8, 0x0001, 0x17fd, 0x2095, 0xbf71, 0x5501,
        0x678d, 0x7101, 0x800d, 0x849d, 0x996d, 0x8c05, 0x8ca9, 0x8d4d,
        0x8df1, 0xdc6d, 0xe491, 0x02a6, 0x53b2, 0xd032, 0x8582, 0x9582,
        0x829a, 0x929a, 0x9002].all fun hw => (decode16 hw).isSome

end LeanModels.Rv
