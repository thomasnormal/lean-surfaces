import LeanModels.Sv.Known2

/-!
# E-core memory state

**Status: trusted statement primitive, derived from E's value discipline.**

An unpacked fixed array is an array-valued store, not a collection of cells
from slang's default parameter point.  This file gives the canonical E memory
component for the first one-rank boundary.  A memory keeps its structured
declaration identity, packed element type, and inclusive unpacked bounds; its
cells are indexed by the source labels (`Int`).  The function has values
outside the declared range as an implementation detail; reads never observe
them and out-of-range writes are no-ops.  There is no fuel and no finite
expansion.

The process evaluator will use these operations when `PDecl.unpackedDims` and
`PLhs.arrayElem` are wired into E.  Unknown memory names are an explicit
`none`, so a loader cannot turn a missing declaration into a scalar signal.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Declaration identity and typed shape -/

/-- A declaration identity is a source scope path plus the declaration's
ordinal in that scope.  The spelling is retained separately for diagnostics;
two scopes may therefore contain declarations with the same spelling without
sharing a memory object. -/
structure MemId where
  scope : List String := []
  decl : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-! ## Source-shaped memory blocks -/

structure MemShape where
  name : String
  elemWidth : Nat
  msb : Int
  lsb : Int
  /-- Structured source identity; old root shapes use the default identity. -/
  id : MemId := {}
  /-- Element signedness, retained at the memory boundary for typed writes. -/
  signed : Bool := false
  /-- IEEE two-state destination conversion (§6.11). -/
  twoState : Bool := false
  /-- An undriven net starts at z rather than x (§6.6). -/
  isNet : Bool := false
deriving Repr, DecidableEq, Inhabited

/-- A label belongs to `[msb:lsb]`, in either ascending or descending order. -/
def MemShape.inRange (m : MemShape) (k : Int) : Prop :=
  (m.lsb ≤ m.msb ∧ m.lsb ≤ k ∧ k ≤ m.msb) ∨
    (m.msb < m.lsb ∧ m.msb ≤ k ∧ k ≤ m.lsb)

instance (m : MemShape) (k : Int) : Decidable (m.inRange k) := by
  unfold MemShape.inRange
  infer_instance

/-- Convert a source value at a memory element boundary.  Width conversion is
bitwise; a two-state destination then maps x/z to zero (IEEE 1800-2023
§6.11). -/
def MemShape.convert (m : MemShape) (v : LVec) : LVec :=
  let resized := v.resizeU m.elemWidth
  if m.twoState then resized.toTwoState else resized

@[simp] theorem width_resizeU_mem (v : LVec) (w : Nat) :
    (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

@[simp] theorem width_toTwoState_mem (v : LVec) :
    v.toTwoState.width = v.width := by
  simp [LVec.toTwoState, LVec.width]

@[simp] theorem bits_size_resizeU_mem (v : LVec) (w : Nat) :
    (v.resizeU w).bits.size = w := by
  simp [LVec.resizeU]

@[simp] theorem bits_size_toTwoState_mem (v : LVec) :
    v.toTwoState.bits.size = v.bits.size := by
  simp [LVec.toTwoState]

/-- The value of an uninitialized element.  Four-state variables start x;
undriven nets have their independent z startup; two-state elements apply the
same deterministic conversion as every later assignment. -/
def MemShape.startCell (m : MemShape) : LVec :=
  m.convert (if m.isNet then LVec.replicate m.elemWidth .lz else LVec.xVec m.elemWidth)

/-- A native array value.  Every cell has the declared packed element width. -/
structure MemBlock where
  shape : MemShape
  cell : Int → LVec
  cell_width : ∀ k, (cell k).width = shape.elemWidth

/-- An uninitialized memory block.  `startCell` supplies the declaration's
typed x/z startup value without expanding the memory into scalar cells. -/
def MemBlock.xBlock (shape : MemShape) : MemBlock :=
  { shape := shape, cell := fun _ => shape.startCell,
    cell_width := fun _ => by
      by_cases h : shape.twoState
      · simp [MemShape.startCell, MemShape.convert, h, bits_size_resizeU_mem,
          bits_size_toTwoState_mem, LVec.toTwoState, LVec.width]
      · simp [MemShape.startCell, MemShape.convert, h, bits_size_resizeU_mem,
          bits_size_toTwoState_mem, LVec.toTwoState, LVec.width] }

instance : Inhabited MemBlock where
  default :=
    let shape : MemShape := { name := "", elemWidth := 0, msb := 0, lsb := 0 }
    { shape := shape, cell := fun _ => LVec.xVec 0,
      cell_width := fun _ => by simp [shape, LVec.xVec, LVec.replicate, LVec.width] }

/-- Read a source label.  Out-of-range labels read all-x at the element width. -/
def MemBlock.read (m : MemBlock) (k : Int) : LVec :=
  if m.shape.inRange k then m.cell k else LVec.xVec m.shape.elemWidth

/-- Write one source label.  The caller supplies the typed element-width fact. -/
def MemBlock.write (m : MemBlock) (k : Int) (v : LVec)
    : MemBlock :=
  if m.shape.inRange k then
    let c : Int → LVec := fun j => if j = k then m.shape.convert v else m.cell j
    let hc : ∀ j, (c j).width = m.shape.elemWidth := by
      intro j
      by_cases hj : j = k
      · by_cases h : m.shape.twoState
        · simp [c, hj, MemShape.convert, h, bits_size_resizeU_mem,
            bits_size_toTwoState_mem, LVec.toTwoState, LVec.width]
        · simp [c, hj, MemShape.convert, h, bits_size_resizeU_mem,
            bits_size_toTwoState_mem, LVec.toTwoState, LVec.width]
      · simp [c, hj, m.cell_width]
    { shape := m.shape, cell := c, cell_width := hc }
  else m

theorem resizeU_of_width {v : LVec} {w : Nat} (h : v.width = w) :
    v.resizeU w = v := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.resizeU, Array.getElem?_ofFn, LVec.width]
  change v.bits.size = w at h
  by_cases hi : i < v.bits.size
  · have hiw : i < w := by omega
    simp [hi, hiw]
  · have hiw : w ≤ i := by omega
    simp [hi, hiw]

theorem MemBlock.read_write_same {m : MemBlock} {k : Int} {v : LVec}
    (hin : m.shape.inRange k) (hv : v.width = m.shape.elemWidth) :
    (m.write k v).read k = m.shape.convert v := by
  rw [MemBlock.write, if_pos hin]
  simp [MemBlock.read, hin]

theorem MemBlock.read_write_other {m : MemBlock} {k j : Int} {v : LVec}
    (hkj : j ≠ k) (hv : v.width = m.shape.elemWidth) :
    (m.write k v).read j = m.read j := by
  by_cases hj : m.shape.inRange k
  · simp [MemBlock.write, MemBlock.read, hj, hkj]
  · simp [MemBlock.write, hj]

theorem MemBlock.read_oob {m : MemBlock} {k : Int}
    (hout : ¬m.shape.inRange k) :
    m.read k = LVec.xVec m.shape.elemWidth := by
  simp [MemBlock.read, hout]

theorem MemBlock.write_oob {m : MemBlock} {k : Int} {v : LVec}
    (hout : ¬m.shape.inRange k) :
    m.write k v = m := by
  unfold MemBlock.write
  rw [if_neg hout]

/-! ## Run-time index resolution -/

/-- Resolve a run-time index using the source declaration's signedness.  An
unknown bit makes the index unknown; the caller turns that into the LRM's
all-x read or no-op write. -/
def MemShape.index? (m : MemShape) (signedIndex : Bool) (idx : LVec) : Option Int :=
  let raw := if signedIndex then idx.toInt? else idx.toNat?.map Int.ofNat
  match raw with
  | some k => if m.inRange k then some k else none
  | none => none

/-- Read a run-time selected cell.  Unknown and out-of-range indices return
all x at the element width (§11.5.1). -/
def MemBlock.readIndex (m : MemBlock) (signedIndex : Bool) (idx : LVec) : LVec :=
  match m.shape.index? signedIndex idx with
  | some k => m.read k
  | none => LVec.xVec m.shape.elemWidth

/-- Write a run-time selected cell.  The RHS has already been evaluated by the
caller; an unknown or out-of-range index is a no-op (§11.5.1). -/
def MemBlock.writeIndex (m : MemBlock) (signedIndex : Bool) (idx value : LVec) : MemBlock :=
  match m.shape.index? signedIndex idx with
  | some k => m.write k value
  | none => m

theorem MemBlock.readIndex_unknown {m : MemBlock} {signedIndex : Bool} {idx : LVec}
    (h : m.shape.index? signedIndex idx = none) :
    m.readIndex signedIndex idx = LVec.xVec m.shape.elemWidth := by
  simp [MemBlock.readIndex, h]

theorem MemBlock.writeIndex_unknown {m : MemBlock} {signedIndex : Bool} {idx value : LVec}
    (h : m.shape.index? signedIndex idx = none) :
    m.writeIndex signedIndex idx value = m := by
  simp [MemBlock.writeIndex, h]

theorem MemBlock.readIndex_writeIndex_same {m : MemBlock} {signedIndex : Bool}
    {idx value : LVec} {k : Int}
    (hi : m.shape.index? signedIndex idx = some k)
    (hv : value.width = m.shape.elemWidth) :
    (m.writeIndex signedIndex idx value).readIndex signedIndex idx =
      m.shape.convert value := by
  have hkin : m.shape.inRange k := by
    unfold MemShape.index? at hi
    split at hi
    · cases hidx : idx.toInt? with
      | none => simp [hidx] at hi
      | some n =>
          simp [hidx] at hi
          have hnk := hi.2
          simpa [hnk] using hi.1
    · cases hidx : idx.toNat? with
      | none => simp [hidx] at hi
      | some n =>
          simp [hidx] at hi
          have hnk := hi.2
          simpa [hnk] using hi.1
  unfold MemBlock.writeIndex
  rw [hi]
  unfold MemBlock.readIndex
  have hi' : (m.write k value).shape.index? signedIndex idx = some k := by
    simp [MemBlock.write, hkin, hi]
  rw [hi']
  apply MemBlock.read_write_same
  · exact hkin
  · exact hv

/-! ## Named memory state -/

/-- The E memory component.  A missing name is a loud lookup failure. -/
structure MemState where
  lookup : String → Option MemBlock
  /-- Canonical lookup by structured declaration identity.  The name lookup is
      retained as a compatibility view for the source-shaped adapter. -/
  byId : MemId → Option MemBlock := fun _ => none

instance : Inhabited MemState :=
  ⟨{ lookup := fun _ => none, byId := fun _ => none }⟩

def MemState.empty : MemState := default

def MemState.set (s : MemState) (name : String) (m : MemBlock) : MemState :=
  { lookup := fun n => if n == name then some m else s.lookup n
    byId := fun id => if id == m.shape.id then some m else s.byId id }

/-- Canonical identity lookup. -/
def MemState.lookupId (s : MemState) (id : MemId) : Option MemBlock := s.byId id

/-- Replace a block through its structured identity while retaining the
source-spelling compatibility view. -/
def MemState.setId (s : MemState) (id : MemId) (m : MemBlock) : MemState :=
  { lookup := fun n => if n == m.shape.name then some m else s.lookup n
    byId := fun i => if i == id then some m else s.byId i }

def MemState.ofShapes : List MemShape → MemState
  | [] => MemState.empty
  | shape :: rest =>
      MemState.set (MemState.ofShapes rest) shape.name (MemBlock.xBlock shape)

def MemState.read (s : MemState) (name : String) (k : Int) : Option LVec :=
  (s.lookup name).map fun m => m.read k

def MemState.write (s : MemState) (name : String) (k : Int) (v : LVec)
    : Option MemState :=
  (s.lookup name).map fun m => s.set name (m.write k v)

def MemState.readId (s : MemState) (id : MemId) (k : Int) : Option LVec :=
  (s.lookupId id).map fun m => m.read k

def MemState.writeId (s : MemState) (id : MemId) (k : Int) (v : LVec)
    : Option MemState :=
  (s.lookupId id).map fun m => s.setId id (m.write k v)

def MemState.readIndex (s : MemState) (name : String) (signedIndex : Bool)
    (idx : LVec) : Option LVec :=
  (s.lookup name).map fun m => m.readIndex signedIndex idx

def MemState.readIndexId (s : MemState) (id : MemId) (signedIndex : Bool)
    (idx : LVec) : Option LVec :=
  (s.lookupId id).map fun m => m.readIndex signedIndex idx

def MemState.writeIndex (s : MemState) (name : String) (signedIndex : Bool)
    (idx value : LVec) : Option MemState :=
  (s.lookup name).map fun m => s.set name (m.writeIndex signedIndex idx value)

def MemState.writeIndexId (s : MemState) (id : MemId) (signedIndex : Bool)
    (idx value : LVec) : Option MemState :=
  (s.lookupId id).map fun m => s.setId id (m.writeIndex signedIndex idx value)

theorem MemState.read_write_same {s : MemState} {name : String} {k : Int}
    {v : LVec} {m : MemBlock} (hm : s.lookup name = some m)
    (hin : m.shape.inRange k) (hv : v.width = m.shape.elemWidth) :
    (s.write name k v).bind
        (fun s' => s'.read name k) = some (m.shape.convert v) := by
  simp [MemState.write, hm, MemState.read, MemState.set]
  exact MemBlock.read_write_same hin hv

theorem MemState.read_write_other {s : MemState} {name : String} {k j : Int}
    {v : LVec} {m : MemBlock} (hm : s.lookup name = some m)
    (hjk : j ≠ k) (hv : v.width = m.shape.elemWidth) :
    (s.write name k v).bind
        (fun s' => s'.read name j) = s.read name j := by
  simp [MemState.write, hm, MemState.read, MemState.set]
  exact MemBlock.read_write_other hjk hv

theorem MemState.read_unknown {s : MemState} {name : String} {k : Int}
    (hm : s.lookup name = none) : s.read name k = none := by
  simp [MemState.read, hm]

/-! ## Issue-time NBA memory records -/

/-- A memory NBA record stores the declaration identity, the resolved source
label, and the already converted element value.  Neither the index nor the
RHS is re-evaluated at commit (§10.4.2). -/
structure MemNbaRecord where
  id : MemId
  label : Int
  value : LVec
deriving Repr, DecidableEq, Inhabited

abbrev MemNbaQueue := List MemNbaRecord

inductive MemIssue where
  | missing
  | noOp
  | queued (u : MemNbaRecord)
deriving Repr, DecidableEq, Inhabited

/-- Resolve and capture one NBA.  `noOp` is the faithful x/z or out-of-range
index result; `missing` is a loud identity lookup failure. -/
def MemState.issueNba (s : MemState) (id : MemId) (signedIndex : Bool)
    (idx value : LVec) : MemIssue :=
  match s.lookupId id with
  | none => .missing
  | some m =>
      match m.shape.index? signedIndex idx with
      | none => .noOp
      | some label => .queued
          { id := id, label := label, value := m.shape.convert value }

/-- Commit records in issue order.  A later record to the same cell therefore
wins, while records for different cells remain independent. -/
def MemState.commitNba (s : MemState) : MemNbaQueue → Option MemState
  | [] => some s
  | u :: us => do
      let s' ← s.writeId u.id u.label u.value
      s'.commitNba us

theorem MemState.commitNba_nil (s : MemState) : s.commitNba [] = some s := rfl

theorem MemState.commitNba_cons (s : MemState) (u : MemNbaRecord) (us : MemNbaQueue) :
    s.commitNba (u :: us) = (s.writeId u.id u.label u.value).bind
      (fun s' => s'.commitNba us) := by rfl

/-! ## Selected-cell sensitivity -/

/-- A source-shaped memory read site.  The index-expression signal names are
kept as metadata by elaboration; the selected-cell comparison below is the
memory part of §9.4.2.2.2's implicit sensitivity rule. -/
structure MemReadSite where
  id : MemId
  signedIndex : Bool
  index : LVec
  indexSignals : List String := []
deriving Repr, DecidableEq, Inhabited

def MemReadSite.value (site : MemReadSite) (s : MemState) : Option LVec :=
  s.readIndexId site.id site.signedIndex site.index

def MemReadSite.cellChanged (site : MemReadSite) (before after : MemState) : Bool :=
  site.value before != site.value after

/-! ## Kernel guards -/

/-! ## Kernel guards -/

private def fifoShape : MemShape :=
  { name := "mem_q", elemWidth := 8, msb := 0, lsb := 3,
    id := { scope := ["fifo"], decl := 2 } }

private def fifoBlock : MemBlock :=
  { shape := fifoShape,
    cell := fun k => LVec.ofNat 8 (k.toNat + 1),
    cell_width := fun _ => by simp [fifoShape, LVec.ofNat, LVec.width] }

private def fifoState : MemState := MemState.set MemState.empty "mem_q" fifoBlock

#guard (MemState.read fifoState "mem_q" 2).getD (LVec.xVec 8) == LVec.ofNat 8 3
#guard (MemState.read fifoState "mem_q" 8).getD (LVec.ofNat 8 99) == LVec.xVec 8
#guard (MemState.read fifoState "missing" 0).isNone

private def cpuregsShape : MemShape :=
  { name := "cpuregs", elemWidth := 32, msb := 0, lsb := 31,
    id := { scope := ["unpacked_cpuregs_e"], decl := 0 } }

private def cpuregsState : MemState := MemState.ofShapes [cpuregsShape]

-- Runtime unsigned indices: known reads select one cell, x/z and OOB read x.
#guard (MemState.readIndexId cpuregsState cpuregsShape.id false (LVec.ofNat 5 3)).getD
    (LVec.xVec 32) == LVec.xVec 32
#guard (MemState.readIndexId cpuregsState cpuregsShape.id false (LVec.lit "xxxxx")).getD
    (LVec.ofNat 32 7) == LVec.xVec 32
#guard (MemState.readIndexId cpuregsState cpuregsShape.id false (LVec.ofNat 5 32)).getD
    (LVec.ofNat 32 7) == LVec.xVec 32

-- NBA issue captures the known label and converted RHS before commit.
#guard match MemState.issueNba cpuregsState cpuregsShape.id false
    (LVec.ofNat 5 3) (LVec.ofNat 32 0xa5) with
  | .queued u => u.id == cpuregsShape.id && u.label == 3 && u.value == LVec.ofNat 32 0xa5
  | _ => false
#guard match MemState.issueNba cpuregsState cpuregsShape.id false
    (LVec.lit "xxxxx") (LVec.ofNat 32 0x5a) with
  | .noOp => true
  | _ => false

private def cpuregsWrite : MemNbaRecord :=
  { id := cpuregsShape.id, label := 3, value := LVec.ofNat 32 0xa5 }

#guard match cpuregsState.commitNba [cpuregsWrite] with
  | some s => (s.readId cpuregsShape.id 3).getD (LVec.xVec 32) == LVec.ofNat 32 0xa5
  | none => false

#guard match cpuregsState.commitNba
    [{ id := cpuregsShape.id, label := 3, value := LVec.ofNat 32 1 },
     { id := cpuregsShape.id, label := 3, value := LVec.ofNat 32 2 }] with
  | some s => (s.readId cpuregsShape.id 3).getD (LVec.xVec 32) == LVec.ofNat 32 2
  | none => false

private def cpuregsSite3 : MemReadSite :=
  { id := cpuregsShape.id, signedIndex := false, index := LVec.ofNat 5 3 }
private def cpuregsSite2 : MemReadSite :=
  { id := cpuregsShape.id, signedIndex := false, index := LVec.ofNat 5 2 }

#guard match cpuregsState.commitNba [cpuregsWrite] with
  | some s => cpuregsSite3.cellChanged cpuregsState s &&
      !(cpuregsSite2.cellChanged cpuregsState s)
  | none => false

private def twoStateShape : MemShape :=
  { name := "two", elemWidth := 4, msb := 0, lsb := 1, twoState := true,
    id := { scope := ["typed"], decl := 0 } }
private def netShape : MemShape :=
  { name := "wire", elemWidth := 1, msb := 0, lsb := 0, isNet := true,
    id := { scope := ["typed"], decl := 1 } }

#guard (MemState.readId (MemState.ofShapes [twoStateShape]) twoStateShape.id 0).getD
    (LVec.ofNat 4 1) == LVec.ofNat 4 0
#guard (MemState.readId (MemState.ofShapes [netShape]) netShape.id 0).getD
    (LVec.ofNat 1 0) == LVec.lit "z"
#guard match MemState.issueNba (MemState.ofShapes [twoStateShape]) twoStateShape.id
    false (LVec.ofNat 1 0) (LVec.lit "1x01") with
  | .queued u => u.value == LVec.ofNat 4 9
  | _ => false

end LeanModels.Sv.Kernel

#print axioms LeanModels.Sv.Kernel.MemBlock.read_write_same
#print axioms LeanModels.Sv.Kernel.MemBlock.read_write_other
#print axioms LeanModels.Sv.Kernel.MemState.read_unknown
#print axioms LeanModels.Sv.Kernel.MemState.commitNba_cons
