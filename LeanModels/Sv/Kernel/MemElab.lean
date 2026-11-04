import LeanModels.Sv.Param2
import LeanModels.Sv.Kernel.CoreMem

/-!
# Retained declaration to E-memory bridge

**Status: derived elaboration bridge.**  `UnpackedDecl` keeps the source
declaration and symbolic bounds in the envelope.  This module evaluates one
unpacked dimension at a concrete parameter point and creates the corresponding
native E memory shape/state.  It deliberately admits only one unpacked rank,
which is the shape used by FIFO storage; nested memories remain a named loud
boundary until their row-major state is specified.
-/

namespace LeanModels.Sv

open Kernel

def evalMemDim (env : IEnv) (d : PDim) : Except String (Int × Int) := do
  return (← evalInt env d.msb, ← evalInt env d.lsb)

def PDecl.memShape? (env : IEnv) (pd : PDecl) : Except String (Option MemShape) :=
  match pd.unpackedDims with
  | [] => .ok none
  | [d] => do
      let w ← pd.type.width env
      let (msb, lsb) ← evalMemDim env d
      if w == 0 then
        .error s!"decl '{pd.name}': zero-width unpacked element"
      else
        .ok (some { name := pd.name, elemWidth := w, msb, lsb })
  | _ :: _ :: _ =>
      .error s!"decl '{pd.name}': nested unpacked memory rank outside E (UnpackedDecl:rank)"

def PDesign.memShapesAt (env : IEnv) : PDesign → Except String (List MemShape)
  | d => go d.decls
where
  go : List PDecl → Except String (List MemShape)
    | [] => .ok []
    | pd :: rest => do
        let tail ← go rest
        match ← pd.memShape? env with
        | none => .ok tail
        | some shape => .ok (shape :: tail)

def PDesign.memStateAt (env : IEnv) (d : PDesign) : Except String MemState := do
  return MemState.ofShapes (← d.memShapesAt env)

/-! ## Source-shaped array targets

The flat `Lhs2` path cannot represent an unpacked cell: its slices address one
packed vector.  Keep that distinction explicit here.  A one-rank
`PLhs.arrayElem` is resolved against the declaration's source label range and
then uses the native `MemState` cell operation.  Out-of-range labels are the
LRM no-op/read-x behavior supplied by `MemBlock`; dynamic labels and partial
array selects remain loud. -/

def PDecl.memTarget? (env : IEnv) (pd : PDecl) (target : PLhs) :
    Except String (Option (MemShape × Int)) := do
  let some shape ← pd.memShape? env
    | .error s!"decl '{pd.name}': target is not an unpacked memory"
  match target with
  | .arrayElem n [index] =>
      if n != pd.name then
        .error s!"array target '{n}' does not name declaration '{pd.name}'"
      else
        match evalInt env index with
        | .ok i => .ok (some (shape, i))
        | .error e => .error s!"array target '{n}' index: {e}"
  | .arrayElem n _ =>
      .error s!"array target '{n}' has rank outside E (UnpackedDecl:rank)"
  | .arrayPart n _ _ _ _ =>
      .error s!"array part target '{n}' is outside the one-cell E memory fragment"
  | _ => .error s!"target '{pd.name}' is not an unpacked array element"

def MemState.readTarget (env : IEnv) (pd : PDecl) (target : PLhs) (s : MemState) :
    Except String (Option LVec) := do
  match ← pd.memTarget? env target with
  | none => .ok none
  | some (shape, index) =>
      match s.lookup shape.name with
      | none => .error s!"memory '{shape.name}' is not present in E state"
      | some _ => .ok (s.read shape.name index)

def MemState.writeTarget (env : IEnv) (pd : PDecl) (target : PLhs)
    (value : LVec) (s : MemState) : Except String (Option MemState) := do
  match ← pd.memTarget? env target with
  | none => .ok none
  | some (shape, index) =>
      match s.write shape.name index value with
      | none => .error s!"memory '{shape.name}' is not present in E state"
      | some s' => .ok (some s')

private def memEnv : IEnv := { vals := [("S", 4)] }

private def memDecl : PDecl :=
  { name := "mem", type := .packed [⟨.int 7, .int 0⟩] (some 8),
    unpackedDims := [⟨.int 0, .binary (.m0 .sub) (.paramRef "S" none) (.int 1)⟩] }

#guard (memDecl.memShape? memEnv).toOption ==
  some ({ name := "mem", elemWidth := 8, msb := 0, lsb := 3 } : MemShape)
#guard (MemState.read (MemState.ofShapes
  [{ name := "mem", elemWidth := 8, msb := 0, lsb := 3 }]) "mem" 4).getD (LVec.ofNat 1 1) == LVec.xVec 8

private def memTarget : PLhs := .arrayElem "mem" [.int 2]

#guard match MemState.writeTarget memEnv memDecl memTarget (LVec.ofNat 8 165)
    (MemState.ofShapes [{ name := "mem", elemWidth := 8, msb := 0, lsb := 3 }]) with
  | .ok (some s) => (MemState.readTarget memEnv memDecl memTarget s).toOption ==
      some (some (LVec.ofNat 8 165))
  | _ => false
#guard match MemState.readTarget memEnv memDecl (.arrayElem "mem" [.int 9])
    (MemState.ofShapes [{ name := "mem", elemWidth := 8, msb := 0, lsb := 3 }]) with
  | .ok (some v) => v == LVec.xVec 8
  | _ => false
#guard match MemState.writeTarget memEnv memDecl (.arrayPart "mem" [.int 1]
    .range (.int 3) (.int 2)) (LVec.ofNat 2 3)
    (MemState.ofShapes [{ name := "mem", elemWidth := 8, msb := 0, lsb := 3 }]) with
  | .error _ => true
  | _ => false

end LeanModels.Sv

#print axioms LeanModels.Sv.PDecl.memShape?
#print axioms LeanModels.Sv.PDesign.memStateAt
