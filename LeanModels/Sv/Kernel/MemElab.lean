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

private def memEnv : IEnv := { vals := [("S", 4)] }

private def memDecl : PDecl :=
  { name := "mem", type := .packed [⟨.int 7, .int 0⟩] (some 8),
    unpackedDims := [⟨.int 0, .binary (.m0 .sub) (.paramRef "S" none) (.int 1)⟩] }

#guard (memDecl.memShape? memEnv).toOption ==
  some ({ name := "mem", elemWidth := 8, msb := 0, lsb := 3 } : MemShape)
#guard (MemState.read (MemState.ofShapes
  [{ name := "mem", elemWidth := 8, msb := 0, lsb := 3 }]) "mem" 4).getD (LVec.ofNat 1 1) == LVec.xVec 8

end LeanModels.Sv

#print axioms LeanModels.Sv.PDecl.memShape?
#print axioms LeanModels.Sv.PDesign.memStateAt
