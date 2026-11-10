import LeanModels.Sv.ObserveE
import LeanModels.Sv.Obs
import LeanModels.Refine.Rvfi

/-!
# A partial RV32 RVFI port decoder

**Status: observation adapter for E, not an execution semantics.** This reads
one ordinary RVFI channel (`NRET = 1`, `ILEN = XLEN = 32`) from trusted port
samples. Names are the supplied `portPrefix` followed by the standard field name.
There is no source parsing, instruction decoding, or inferred trap cause.

Contract: YosysHQ/riscv-formal, c992aa61fdfe0846c5ed90324c596202a1c69b76,
`docs/source/rvfi.rst`, instruction metadata, integer registers, PC and memory.
Only known-invalid cycles ignore payloads. A valid cycle requires exact port
widths and fully known payloads, including unused payloads (a conservative
decode boundary). No x/z bit is converted to zero. Trap, halt and handler-entry
rows refuse: RVFI has no cause port, and `intr` marks handler entry rather than
encoding an interrupt cause. The existing RV32 canonical-mask/machine-mode
guard is reused. Aligned-memory, rollback and other RVFI extensions are outside
this adapter's contract.
-/

namespace LeanModels.Refine.RvfiPorts

open LeanModels.Rv LeanModels.Sv LeanModels.Sv.Observe

set_option autoImplicit false

/-- Exact-width, fully known port read. `cast` changes only the width proof;
it cannot narrow, extend, or otherwise alter the vector. -/
def readBits (width : Nat) (sample : PortSample) (name : String) : Option (BitVec width) := do
  let value ← sample.read name
  if h : value.width = width then
    return (← value.known?).cast h
  else none

/-- Successful reads retain the source width and its known-vector value. -/
theorem readBits_eq_some_iff (width : Nat) (sample : PortSample) (name : String)
    (bits : BitVec width) :
    readBits width sample name = some bits ↔
      ∃ (value : LVec) (h : value.width = width),
        sample.read name = some value ∧ value.allKnown = true ∧
        (BitVec.ofNat value.width value.toNat).cast h = bits := by
  unfold readBits
  cases hread : sample.read name with
  | none => simp
  | some value =>
      by_cases hw : value.width = width
      · cases hk : value.allKnown <;> simp [hw, LVec.known?, hk]
      · simp [hw]

/-- An arbitrary known vector reads back without truncation. -/
theorem readBits_ofBitVec {width : Nat} (sample : PortSample) (name : String)
    (bits : BitVec width) (hread : sample.read name = some (.ofBitVec bits)) :
    readBits width sample name = some bits := by
  rw [readBits_eq_some_iff]
  refine ⟨.ofBitVec bits, ?_, hread, ?_, ?_⟩
  · exact LVec.width_ofNat _ _
  · exact LVec.allKnown_ofNat _ _
  · apply BitVec.eq_of_toNat_eq
    simp [LVec.ofBitVec, LVec.toNat_ofNat, Nat.mod_eq_of_lt bits.isLt]

/-- The fixed-width payload of one active RV32 channel. Flags are retained
until the adapter explicitly checks its non-trapping contract. -/
structure Payload where
  order : BitVec 64
  insn : Word
  trap : BitVec 1
  halt : BitVec 1
  intr : BitVec 1
  mode : BitVec 2
  ixl : BitVec 2
  rs1Addr : BitVec 5
  rs2Addr : BitVec 5
  rs1Rdata : Word
  rs2Rdata : Word
  rdAddr : BitVec 5
  rdWdata : Word
  pcRdata : Word
  pcWdata : Word
  memAddr : Word
  memRmask : ByteMask
  memWmask : ByteMask
  memRdata : Word
  memWdata : Word
  deriving DecidableEq, Repr

/-- Read the standard fields as declared, without resizing or mask/address
conversion. `portPrefix = "rvfi_"` selects the usual signal names. -/
def readPayload (portPrefix : String) (sample : PortSample) : Option Payload := do
  let order ← readBits 64 sample (portPrefix ++ "order")
  let insn ← readBits 32 sample (portPrefix ++ "insn")
  let trap ← readBits 1 sample (portPrefix ++ "trap")
  let halt ← readBits 1 sample (portPrefix ++ "halt")
  let intr ← readBits 1 sample (portPrefix ++ "intr")
  let mode ← readBits 2 sample (portPrefix ++ "mode")
  let ixl ← readBits 2 sample (portPrefix ++ "ixl")
  let rs1Addr ← readBits 5 sample (portPrefix ++ "rs1_addr")
  let rs2Addr ← readBits 5 sample (portPrefix ++ "rs2_addr")
  let rs1Rdata ← readBits 32 sample (portPrefix ++ "rs1_rdata")
  let rs2Rdata ← readBits 32 sample (portPrefix ++ "rs2_rdata")
  let rdAddr ← readBits 5 sample (portPrefix ++ "rd_addr")
  let rdWdata ← readBits 32 sample (portPrefix ++ "rd_wdata")
  let pcRdata ← readBits 32 sample (portPrefix ++ "pc_rdata")
  let pcWdata ← readBits 32 sample (portPrefix ++ "pc_wdata")
  let memAddr ← readBits 32 sample (portPrefix ++ "mem_addr")
  let memRmask ← readBits 4 sample (portPrefix ++ "mem_rmask")
  let memWmask ← readBits 4 sample (portPrefix ++ "mem_wmask")
  let memRdata ← readBits 32 sample (portPrefix ++ "mem_rdata")
  let memWdata ← readBits 32 sample (portPrefix ++ "mem_wdata")
  return ⟨order, insn, trap, halt, intr, mode, ixl, rs1Addr, rs2Addr,
    rs1Rdata, rs2Rdata, rdAddr, rdWdata, pcRdata, pcWdata, memAddr,
    memRmask, memWmask, memRdata, memWdata⟩

private def Payload.row (p : Payload) : RvfiObservation :=
  { valid := true, order := p.order.toNat, insn := p.insn,
    pcRdata := p.pcRdata, pcWdata := p.pcWdata,
    mode := p.mode, ixl := p.ixl,
    rs1Addr := p.rs1Addr.toFin, rs2Addr := p.rs2Addr.toFin,
    rs1Rdata := p.rs1Rdata, rs2Rdata := p.rs2Rdata,
    rdAddr := p.rdAddr.toFin, rdWdata := p.rdWdata,
    rdWdataValid := p.rdAddr.toFin != 0,
    memAddr := p.memAddr, memRmask := p.memRmask, memWmask := p.memWmask,
    memRdata := p.memRdata, memWdata := p.memWdata }

/-- Standard RVFI has no separate write-enable: `rd_addr = 0` denotes no
architectural register write. Flags outside this no-trap slice refuse before
the existing observation guard is applied. -/
def Payload.toObservation? (p : Payload) : Option RvfiObservation :=
  if p.trap = 0 ∧ p.halt = 0 ∧ p.intr = 0 ∧ p.row.wellFormedB = true then
    some p.row
  else none

theorem Payload.toObservation?_sound (p : Payload) (row : RvfiObservation)
    (h : p.toObservation? = some row) :
    p.trap = 0 ∧ p.halt = 0 ∧ p.intr = 0 ∧
    row.valid = true ∧ row.wellFormed ∧ row.order = p.order.toNat ∧
    row.rdWdataValid = (row.rdAddr != 0) ∧
    row.trap = false ∧ row.intr = false ∧ row.cause = none := by
  unfold toObservation? at h
  split at h
  · rename_i hflags
    cases h
    exact ⟨hflags.1, hflags.2.1, hflags.2.2.1, rfl, hflags.2.2.2,
      rfl, rfl, rfl, rfl, rfl⟩
  · cases h

/-- Canonical representative of an invalid cycle. Its payload is not read
from hardware and has no retirement meaning. -/
def bubble : RvfiObservation :=
  { valid := false, insn := 0, pcRdata := 0, pcWdata := 0 }

/-- Decode one sample. A failed or unknown valid bit is not a bubble. -/
def decode (portPrefix : String) (sample : PortSample) : Option RvfiObservation := do
  let valid ← readBits 1 sample (portPrefix ++ "valid")
  if valid = 0 then return bubble
  else (← readPayload portPrefix sample).toObservation?

/-- A known-invalid cycle ignores even absent or unknown payload ports. -/
theorem decode_bubble (portPrefix : String) (sample : PortSample)
    (h : readBits 1 sample (portPrefix ++ "valid") = some 0) :
    decode portPrefix sample = some bubble := by
  simp [decode, h]

/-- Successful decoding preserves the actual valid bit; it cannot turn an
unknown or malformed active row into a bubble. -/
theorem decode_valid (portPrefix : String) (sample : PortSample) (row : RvfiObservation)
    (h : decode portPrefix sample = some row) :
    readBits 1 sample (portPrefix ++ "valid") = some (BitVec.ofBool row.valid) := by
  unfold decode at h
  cases hv : readBits 1 sample (portPrefix ++ "valid") with
  | none => simp [hv] at h
  | some valid =>
      rw [hv] at h
      change (if valid = 0 then some bubble else
        (readPayload portPrefix sample).bind Payload.toObservation?) = some row at h
      by_cases hz : valid = 0
      · simp [hz] at h
        subst row
        simp [hz, bubble, BitVec.ofBool]
      · rw [ite_eq_right hz] at h
        cases hp : readPayload portPrefix sample with
        | none => simp [hp] at h
        | some payload =>
            rw [hp] at h
            change payload.toObservation? = some row at h
            have hr := (payload.toObservation?_sound row h).2.2.2.1
            have hone : valid = 1 := by
              apply BitVec.eq_of_toNat_eq
              have hlt := valid.isLt
              have hne : valid.toNat ≠ 0 := by
                intro heq
                exact hz (BitVec.eq_of_toNat_eq heq)
              change valid.toNat = 1
              change valid.toNat < 2 at hlt
              omega
            simp [hr, hone, BitVec.ofBool]

/-- The post-cycle convention for registered RVFI outputs. This reads only
the trusted post sample; the core invariant must justify that convention. -/
def decodePost (portPrefix : String) (sample : CycleObs PortSample) : Option RvfiObservation :=
  decode portPrefix sample.post

end LeanModels.Refine.RvfiPorts

#print axioms LeanModels.Refine.RvfiPorts.readBits_eq_some_iff
#print axioms LeanModels.Refine.RvfiPorts.readBits_ofBitVec
#print axioms LeanModels.Refine.RvfiPorts.Payload.toObservation?_sound
#print axioms LeanModels.Refine.RvfiPorts.decode_valid
