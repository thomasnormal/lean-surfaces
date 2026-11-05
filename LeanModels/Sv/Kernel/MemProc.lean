import LeanModels.Sv.Kernel.MemElab

/-!
# Procedural updates for source-shaped E memories

This is the first process adapter for the native memory component.  It keeps
unpacked cells as cells: an NBA target carries its declaration and source
`PLhs.arrayElem`, and the queue commits through `MemState.writeTarget`.  Scalar
right-hand sides use the existing `Expr2` evaluator over the scalar view; a
direct memory-cell read is available as an explicit RHS form.  Compound source
expressions containing memory reads remain loud until their source-shaped
expression evaluator is specified.

No `Stmt2` constructor or finite-array expansion is introduced here.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Source-shaped memory NBA entries -/

structure MemUpdate where
  decl : PDecl
  target : PLhs
  value : LVec

abbrev MemNba := List MemUpdate

structure MemProcState where
  scalar : SvState
  memory : MemState

def MemProcState.empty (scalar : SvState) : MemProcState :=
  { scalar, memory := .empty }

def enqueueMemNba (env : IEnv) (decl : PDecl) (target : PLhs) (value : LVec)
    (q : MemNba) : Except String MemNba := do
  match ← decl.memTarget? env target with
  | none => .error s!"memory target '{decl.name}' did not resolve to a cell"
  | some _ => .ok (q ++ [{ decl, target, value }])

def commitMemNba (env : IEnv) (s : MemState) : MemNba → Res MemState
  | [] => .ok s
  | u :: rest =>
      match u.decl.memTarget? env u.target with
      | .error e => .unsupported s!"memory NBA target: {e}"
      | .ok none => .unsupported s!"memory NBA target '{u.decl.name}' did not resolve to a cell"
      | .ok (some _) =>
          match LeanModels.Sv.MemState.writeTarget env u.decl u.target u.value s with
          | .error e => .unsupported s!"memory NBA write: {e}"
          | .ok none => .unsupported s!"memory NBA write '{u.decl.name}' did not find its state"
          | .ok (some s') => commitMemNba env s' rest

theorem commitMemNba_nil (env : IEnv) (s : MemState) :
    commitMemNba env s [] = .ok s := rfl

/-! ## A process step -/

inductive MemRhs where
  | scalar (value : Expr2)
  | cell (decl : PDecl) (target : PLhs)

def evalMemRhs (env : IEnv) (fuel : Nat) (st : MemProcState) : MemRhs → Res LVec
  | .scalar value => evalExpr2 fuel st.scalar value
  | .cell decl target =>
      match LeanModels.Sv.MemState.readTarget env decl target st.memory with
      | .error e => .unsupported s!"memory RHS read: {e}"
      | .ok none => .unsupported s!"memory RHS '{decl.name}' is not a cell"
      | .ok (some value) => .ok value

def execMemNba (env : IEnv) (fuel : Nat) (st : MemProcState) (q : MemNba)
    (decl : PDecl) (target : PLhs) (rhs : MemRhs) : Res MemNba := do
  let value ← evalMemRhs env fuel st rhs
  match enqueueMemNba env decl target value q with
  | .error e => .unsupported s!"memory NBA enqueue: {e}"
  | .ok q' => .ok q'

def stepMemNba (env : IEnv) (fuel : Nat) (st : MemProcState) (q : MemNba)
    (decl : PDecl) (target : PLhs) (rhs : MemRhs) : Res MemProcState := do
  let q' ← execMemNba env fuel st q decl target rhs
  let memory ← commitMemNba env st.memory q'
  return { st with memory }

/-! ## Kernel guards -/

private def procEnv : IEnv := { vals := [("S", 4)] }

private def procDecl : PDecl :=
  { name := "mem", type := .packed [⟨.int 7, .int 0⟩] (some 8),
    unpackedDims := [⟨.int 0, .binary (.m0 .sub) (.paramRef "S" none) (.int 1)⟩] }

private def procTarget : PLhs := .arrayElem "mem" [.int 2]

private def procMemory : MemState :=
  MemState.ofShapes [{ name := "mem", elemWidth := 8, msb := 0, lsb := 3 }]

#guard match execMemNba procEnv 4
    { scalar := [], memory := procMemory } [] procDecl procTarget
    (.scalar (.lit (LVec.ofNat 8 165))) with
  | .ok [u] => u.value == LVec.ofNat 8 165
  | _ => false

#guard match stepMemNba procEnv 4
    { scalar := [], memory := procMemory } [] procDecl procTarget
    (.scalar (.lit (LVec.ofNat 8 165))) with
  | .ok st => (st.memory.read "mem" 2).getD (LVec.xVec 8) == LVec.ofNat 8 165
  | _ => false

#guard match stepMemNba procEnv 4
    { scalar := [], memory := procMemory } [] procDecl procTarget
    (.cell procDecl procTarget) with
  | .ok st => (st.memory.read "mem" 2).getD (LVec.xVec 8) == LVec.xVec 8
  | _ => false

#guard match execMemNba procEnv 4
    { scalar := [], memory := procMemory } [] procDecl (.arrayPart "mem" [.int 2]
      .range (.int 1) (.int 0)) (.scalar (.lit (LVec.ofNat 2 3))) with
  | .unsupported m => m.startsWith "memory NBA enqueue"
  | _ => false

end LeanModels.Sv.Kernel

#print axioms LeanModels.Sv.Kernel.commitMemNba_nil
