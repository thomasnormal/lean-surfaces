import LeanModels.Sv.Known2

/-!
# E-core memory state

**Status: trusted statement primitive, derived from E's value discipline.**

An unpacked fixed array is an array-valued store, not a collection of cells
from slang's default parameter point.  This file gives the source-shaped
memory state used by the next E elaboration rung.  A memory keeps its declared
packed element width and unpacked bounds, and its cells are indexed by the
source labels (`Int`).  The function has values outside the declared range as
an implementation detail; reads never observe them and out-of-range writes
are no-ops.  There is no fuel and no finite expansion.

The process evaluator will use these operations when `PDecl.unpackedDims` and
`PLhs.arrayElem` are wired into E.  Unknown memory names are an explicit
`none`, so a loader cannot turn a missing declaration into a scalar signal.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Source-shaped memory blocks -/

structure MemShape where
  name : String
  elemWidth : Nat
  msb : Int
  lsb : Int
deriving Repr, DecidableEq, Inhabited

/-- A label belongs to `[msb:lsb]`, in either ascending or descending order. -/
def MemShape.inRange (m : MemShape) (k : Int) : Prop :=
  (m.lsb ≤ m.msb ∧ m.lsb ≤ k ∧ k ≤ m.msb) ∨
    (m.msb < m.lsb ∧ m.msb ≤ k ∧ k ≤ m.lsb)

instance (m : MemShape) (k : Int) : Decidable (m.inRange k) := by
  unfold MemShape.inRange
  infer_instance

/-- A native array value.  Every cell has the declared packed element width. -/
structure MemBlock where
  shape : MemShape
  cell : Int → LVec
  cell_width : ∀ k, (cell k).width = shape.elemWidth

/-- An uninitialized memory block: every declared element starts all-x. -/
def MemBlock.xBlock (shape : MemShape) : MemBlock :=
  { shape := shape, cell := fun _ => LVec.xVec shape.elemWidth,
    cell_width := fun _ => by simp [LVec.xVec, LVec.replicate, LVec.width] }

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
    let c : Int → LVec := fun j => if j = k then v.resizeU m.shape.elemWidth else m.cell j
    let hc : ∀ j, (c j).width = m.shape.elemWidth := by
      intro j
      by_cases hj : j = k
      · simp [c, hj, LVec.resizeU, LVec.width]
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
    (m.write k v).read k = v := by
  rw [MemBlock.write, if_pos hin]
  simp [MemBlock.read, hin, resizeU_of_width hv]

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

/-! ## Named memory state -/

/-- The E memory component.  A missing name is a loud lookup failure. -/
structure MemState where
  lookup : String → Option MemBlock

instance : Inhabited MemState := ⟨{ lookup := fun _ => none }⟩

def MemState.empty : MemState := default

def MemState.set (s : MemState) (name : String) (m : MemBlock) : MemState :=
  { lookup := fun n => if n == name then some m else s.lookup n }

def MemState.ofShapes : List MemShape → MemState
  | [] => MemState.empty
  | shape :: rest =>
      MemState.set (MemState.ofShapes rest) shape.name (MemBlock.xBlock shape)

def MemState.read (s : MemState) (name : String) (k : Int) : Option LVec :=
  (s.lookup name).map fun m => m.read k

def MemState.write (s : MemState) (name : String) (k : Int) (v : LVec)
    : Option MemState :=
  (s.lookup name).map fun m => s.set name (m.write k v)

theorem MemState.read_write_same {s : MemState} {name : String} {k : Int}
    {v : LVec} {m : MemBlock} (hm : s.lookup name = some m)
    (hin : m.shape.inRange k) (hv : v.width = m.shape.elemWidth) :
    (s.write name k v).bind
        (fun s' => s'.read name k) = some v := by
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

/-! ## Kernel guards -/

private def fifoShape : MemShape :=
  { name := "mem_q", elemWidth := 8, msb := 0, lsb := 3 }

private def fifoBlock : MemBlock :=
  { shape := fifoShape,
    cell := fun k => LVec.ofNat 8 (k.toNat + 1),
    cell_width := fun _ => by simp [fifoShape, LVec.ofNat, LVec.width] }

private def fifoState : MemState := MemState.set MemState.empty "mem_q" fifoBlock

#guard (MemState.read fifoState "mem_q" 2).getD (LVec.xVec 8) == LVec.ofNat 8 3
#guard (MemState.read fifoState "mem_q" 8).getD (LVec.ofNat 8 99) == LVec.xVec 8
#guard (MemState.read fifoState "missing" 0).isNone

end LeanModels.Sv.Kernel

#print axioms LeanModels.Sv.Kernel.MemBlock.read_write_same
#print axioms LeanModels.Sv.Kernel.MemBlock.read_write_other
#print axioms LeanModels.Sv.Kernel.MemState.read_unknown
