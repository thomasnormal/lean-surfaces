import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.ArrayFast

/-!
# Scalar-array instrument for canonical memory E

This is an executor view over `CoreMemState`: native `MemState` remains the
only memory representation, while scalar declarations use the existing
`ArrayFast` snapshot.  The first bridge below proves one whole scalar write
back to the authoritative `Store.set`; no canonical step is changed yet.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

structure CoreMemFastState where
  scalar : FastConfig
  memory : MemState

def CoreMemFastState.toState (s : CoreMemFastState) : CoreMemState :=
  { scalar := s.scalar.store, memory := s.memory }

def CoreMemFastState.ofState (E : CoreMemDesign) (s : CoreMemState) : CoreMemFastState :=
  { scalar := FastConfig.ofConfig E.scalar
      { store := s.scalar, active := [], k := 0 }
    memory := s.memory }

theorem CoreMemFastState.ofState_toState (E : CoreMemDesign) (s : CoreMemState) :
    (CoreMemFastState.ofState E s).toState = s := by
  cases s
  simp [CoreMemFastState.ofState, CoreMemFastState.toState,
    FastConfig.ofConfig_store]

def CoreMemDesign.fastScalarWrite (E : CoreMemDesign) (s : CoreMemFastState)
    (name : String) (v : LVec) : Res CoreMemFastState :=
  match E.scalar.resolve name with
  | none => .unsupported s!"10.3: continuous target '{name}' is undeclared"
  | some x =>
      match x.path with
      | [] =>
          let old := s.scalar.cells.getD x.decl (s.scalar.fallback x)
          let converted := Val.ofLVec old.ty v
          .ok { s with scalar := { s.scalar with
            cells := s.scalar.cells.setIfInBounds x.decl converted } }
      | _ => .unsupported "10.3.2: non-flat scalar target"

def CoreMemDesign.fastScalarAssignAt (E : CoreMemDesign) (s : CoreMemFastState)
    (view : SvState) (index : Nat) (name : String) (value : PExpr) : Res CoreMemFastState := do
  let width ← match E.scalarWidth? name with
    | some w => .ok w
    | none => .unsupported s!"10.3: continuous target '{name}' is undeclared"
  let v ← E.evalScalarAssignAtView E.env E.elems s.toState view (some width) index value
  E.fastScalarWrite s name v

def CoreMemDesign.fastSettleAssignAt (E : CoreMemDesign)
    (env : IEnv) (elems : List (String × Nat)) (s : CoreMemFastState)
    (view : SvState) (index : Nat) : List CoreMemProc →
    Res (CoreMemFastState × SvState)
  | [] => .ok (s, view)
  | .assign (.ident name) value :: rest => do
      let s' ← E.fastScalarAssignAt s view index name value
      let v ← E.evalScalarAssignAtView env elems s.toState view
        (E.scalarWidth? name |>.map some |>.getD none) index value
      E.fastSettleAssignAt env elems s' (SvState.set view name v) (index + 1) rest
  | .assign (.arrayElem name [indexExpr]) value :: rest => do
      let st := s.toState
      let md ← E.memDecl? name |>.map Res.ok |>.getD
        (.unsupported s!"10.3: continuous memory target '{name}' is undeclared")
      let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
      let st' ← E.writeMemoryAssign env elems st (.arrayElem name [indexExpr]) md v
      E.fastSettleAssignAt env elems (CoreMemFastState.ofState E st') view (index + 1) rest
  | _ :: rest => E.fastSettleAssignAt env elems s view (index + 1) rest

theorem CoreMemDesign.fastScalarWrite_toState
    (E : CoreMemDesign) (s s' : CoreMemFastState) (name : String) (v : LVec)
    (x : VarId)
    (hresolve : E.scalar.resolve name = some x)
    (hpath : x.path = [])
    (hbound : x.decl < s.scalar.cells.size)
    (h : E.fastScalarWrite s name v = .ok s') :
    s'.toState = { s.toState with
      scalar := E.scalar.setName s.toState.scalar name v } := by
  unfold CoreMemDesign.fastScalarWrite at h
  rw [hresolve] at h
  cases x with
  | mk path decl =>
    cases path with
    | nil =>
      simp only [Res.ok.injEq] at h
      cases h
      unfold CoreMemFastState.toState
      simp only [FastConfig.store]
      rw [arrayStore_set_flat_store s.scalar.cells s.scalar.fallback
        { path := [], decl } (Val.ofLVec
          ((s.scalar.cells.getD decl (s.scalar.fallback { path := [], decl })).ty) v)
        rfl hbound]
      simp [Elab.setName, hresolve, arrayStore, hbound]
    | cons head tail =>
      simp_all

theorem CoreMemDesign.fastScalarAssignAt_toState
    (E : CoreMemDesign) (s s' : CoreMemFastState) (view : SvState)
    (index : Nat) (name : String) (value : PExpr) (width : Nat) (v : LVec)
    (x : VarId)
    (hwidth : E.scalarWidth? name = some width)
    (hresolve : E.scalar.resolve name = some x)
    (hpath : x.path = [])
    (hbound : x.decl < s.scalar.cells.size)
    (hv : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width) index value = .ok v)
    (h : E.fastScalarAssignAt s view index name value = .ok s') :
    s'.toState = { s.toState with
      scalar := E.scalar.setName s.toState.scalar name v } := by
  unfold CoreMemDesign.fastScalarAssignAt at h
  simp [hwidth] at h
  rw [hv] at h
  obtain ⟨a, ha, hwrite⟩ := h
  have hav : a = v := (Res.ok.inj ha).symm
  subst a
  exact E.fastScalarWrite_toState s s' name v x hresolve hpath hbound hwrite

theorem CoreMemDesign.fastSettleAssignAt_single_ident_toState
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s s' : CoreMemFastState) (view view' : SvState) (index : Nat)
    (name : String) (value : PExpr) (width : Nat) (v : LVec) (x : VarId)
    (hwidth : E.scalarWidth? name = some width)
    (hresolve : E.scalar.resolve name = some x)
    (hpath : x.path = []) (hbound : x.decl < s.scalar.cells.size)
    (henv : env = E.env) (helems : elems = E.elems)
    (hv : E.evalScalarAssignAtView env elems s.toState view
      (some width) index value = .ok v)
    (h : E.fastSettleAssignAt env elems s view index
      [.assign (.ident name) value] = .ok (s', view')) :
    s'.toState = { s.toState with
      scalar := E.scalar.setName s.toState.scalar name v } ∧
      view' = SvState.set view name v := by
  simp [CoreMemDesign.fastSettleAssignAt, hwidth, hv] at h
  obtain ⟨a, ha, hs⟩ := h
  rcases hs with ⟨rfl, rfl⟩
  have hv' : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width) index value = .ok v := by simpa [henv, helems] using hv
  have hstate := E.fastScalarAssignAt_toState s a view index name value
    width v x hwidth hresolve hpath hbound hv' ha
  exact ⟨hstate, rfl⟩

theorem CoreMemDesign.fastSettleAssignAt_skip_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (e : CoreMemEdge)
    (hfast : E.fastSettleAssignAt env elems s view index (.edge e :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.edge e :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_initial_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (body : PStmt) (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (hfast : E.fastSettleAssignAt env elems s view index (.initial body :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.initial body :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_comb_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (body : PStmt) (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (hfast : E.fastSettleAssignAt env elems s view index (.comb body :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.comb body :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

theorem CoreMemDesign.fastSettleAssignAt_implicit_cons_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (body : PStmt) (rest : List CoreMemProc) (s' : CoreMemFastState) (view' : SvState)
    (hfast : E.fastSettleAssignAt env elems s view index (.implicit body :: rest) =
      .ok (s', view'))
    (htail : E.settleAssignAt env elems s.toState view (index + 1) rest =
      .ok (s'.toState, view')) :
    E.settleAssignAt env elems s.toState view index (.implicit body :: rest) =
      .ok (s'.toState, view') := by
  simpa [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt] using htail

end LeanModels.Sv.Kernel
