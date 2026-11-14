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

theorem CoreMemDesign.fastSettleAssignAt_single_array_refines
    (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (s : CoreMemFastState) (view : SvState) (index : Nat)
    (name : String) (indexExpr : PExpr) (value : PExpr)
    (md : CoreMemDecl) (v : LVec) (s' : CoreMemFastState) (view' : SvState)
    (hmem : E.memDecl? name = some md)
    (hv : E.evalExpr env elems s.toState (some md.shape.elemWidth) value = .ok v)
    (h : E.fastSettleAssignAt env elems s view index
      [.assign (.arrayElem name [indexExpr]) value] = .ok (s', view')) :
    E.settleAssignAt env elems s.toState view index
      [.assign (.arrayElem name [indexExpr]) value] =
      .ok (s'.toState, view') := by
  simp [CoreMemDesign.fastSettleAssignAt, hmem, hv] at h
  simp [CoreMemDesign.settleAssignAt, hmem, hv]
  rcases h with ⟨a, ha, hof, hview⟩
  have hstate : a = s'.toState := by
    calc
      a = (CoreMemFastState.ofState E a).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = s'.toState := congrArg CoreMemFastState.toState hof
  exact ⟨a, ha, hstate, hview⟩

theorem CoreMemDesign.fastSettleAssignAt_two_array_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (indexExpr₁ indexExpr₂ value₁ value₂ : PExpr)
    (md₁ md₂ : CoreMemDecl) (v₁ v₂ : LVec)
    (hmem₁ : E.memDecl? name₁ = some md₁)
    (hmem₂ : E.memDecl? name₂ = some md₂)
    (hv₁ : E.evalExpr E.env E.elems s.toState (some md₁.shape.elemWidth) value₁ = .ok v₁)
    (hv₂ : E.evalExpr E.env E.elems a₁.toState (some md₂.shape.elemWidth) value₂ = .ok v₂)
    (h₁ : E.fastSettleAssignAt E.env E.elems s view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁] = .ok (a₁, view))
    (h₂ : E.fastSettleAssignAt E.env E.elems a₁ view (index + 1)
      [.assign (.arrayElem name₂ [indexExpr₂]) value₂] = .ok (a₂, view)) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁,
       .assign (.arrayElem name₂ [indexExpr₂]) value₂] =
      .ok (a₂.toState, view) := by
  simp [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt,
    hmem₁, hmem₂, hv₁, hv₂] at h₁ h₂ ⊢
  rcases h₁ with ⟨a, ha, ha₁⟩
  rcases h₂ with ⟨b, hb, hb₂⟩
  have ha_to : a = a₁.toState := by
    calc
      a = (CoreMemFastState.ofState E a).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₁.toState := congrArg CoreMemFastState.toState ha₁
  have hb_to : b = a₂.toState := by
    calc
      b = (CoreMemFastState.ofState E b).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₂.toState := congrArg CoreMemFastState.toState hb₂
  refine ⟨a, ha, v₂, ?_, ?_⟩
  · simpa [ha_to] using hv₂
  · simpa [ha_to, hb_to] using hb

theorem CoreMemDesign.fastSettleAssignAt_scalar_array_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (value₁ value₂ indexExpr₂ : PExpr)
    (width₁ : Nat) (v₁ v₂ : LVec) (x₁ : VarId) (md₂ : CoreMemDecl)
    (hwidth₁ : E.scalarWidth? name₁ = some width₁)
    (hresolve₁ : E.scalar.resolve name₁ = some x₁)
    (hpath₁ : x₁.path = [])
    (hbound₁ : x₁.decl < s.scalar.cells.size)
    (hmem₂ : E.memDecl? name₂ = some md₂)
    (hv₁ : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width₁) index value₁ = .ok v₁)
    (hv₂ : E.evalExpr E.env E.elems a₁.toState
      (some md₂.shape.elemWidth) value₂ = .ok v₂)
    (h₁ : E.fastScalarAssignAt s view index name₁ value₁ = .ok a₁)
    (h₂ : E.fastSettleAssignAt E.env E.elems a₁
      (SvState.set view name₁ v₁) (index + 1)
      [.assign (.arrayElem name₂ [indexExpr₂]) value₂] =
      .ok (a₂, SvState.set view name₁ v₁)) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.ident name₁) value₁,
       .assign (.arrayElem name₂ [indexExpr₂]) value₂] =
      .ok (a₂.toState, SvState.set view name₁ v₁) := by
  have hs₁ := E.fastScalarAssignAt_toState s a₁ view index name₁ value₁
    width₁ v₁ x₁ hwidth₁ hresolve₁ hpath₁ hbound₁ hv₁ h₁
  have hv₂' := hv₂
  rw [hs₁] at hv₂'
  simp [CoreMemDesign.fastSettleAssignAt, hmem₂, hv₂'] at h₂
  rcases h₂ with ⟨b, hb, hb₂⟩
  rcases hb₂ with ⟨c, hbc, hc₂⟩
  have hbv : b = v₂ := Res.ok.inj (hb.symm.trans hv₂)
  have hc_to : c = a₂.toState := by
    calc
      c = (CoreMemFastState.ofState E c).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₂.toState := congrArg CoreMemFastState.toState hc₂
  have hbc' := hbc
  rw [hs₁, hbv, hc_to] at hbc'
  simp [CoreMemDesign.settleAssignAt, hwidth₁, hmem₂, hv₁, hv₂', hs₁]
  exact hbc'

theorem CoreMemDesign.fastSettleAssignAt_array_scalar_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (indexExpr₁ value₁ value₂ : PExpr)
    (md₁ : CoreMemDecl) (v₁ v₂ : LVec) (width₂ : Nat) (x₂ : VarId)
    (hmem₁ : E.memDecl? name₁ = some md₁)
    (hwidth₂ : E.scalarWidth? name₂ = some width₂)
    (hresolve₂ : E.scalar.resolve name₂ = some x₂)
    (hpath₂ : x₂.path = [])
    (hbound₂ : x₂.decl < a₁.scalar.cells.size)
    (hv₁ : E.evalExpr E.env E.elems s.toState
      (some md₁.shape.elemWidth) value₁ = .ok v₁)
    (hv₂ : E.evalScalarAssignAtView E.env E.elems a₁.toState view
      (some width₂) (index + 1) value₂ = .ok v₂)
    (h₁ : E.fastSettleAssignAt E.env E.elems s view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁] = .ok (a₁, view))
    (h₂ : E.fastScalarAssignAt a₁ view (index + 1) name₂ value₂ = .ok a₂) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.arrayElem name₁ [indexExpr₁]) value₁,
       .assign (.ident name₂) value₂] =
      .ok (a₂.toState, SvState.set view name₂ v₂) := by
  have hs₂ := E.fastScalarAssignAt_toState a₁ a₂ view (index + 1) name₂ value₂
    width₂ v₂ x₂ hwidth₂ hresolve₂ hpath₂ hbound₂ hv₂ h₂
  simp [CoreMemDesign.fastSettleAssignAt, CoreMemDesign.settleAssignAt,
    hmem₁, hv₁] at h₁
  rcases h₁ with ⟨c, hc, hc₁⟩
  have hc_to : c = a₁.toState := by
    calc
      c = (CoreMemFastState.ofState E c).toState := by
        simp [CoreMemFastState.ofState_toState]
      _ = a₁.toState := congrArg CoreMemFastState.toState hc₁
  have hc' := hc
  rw [hc_to] at hc'
  simp [CoreMemDesign.settleAssignAt, hmem₁, hwidth₂, hv₁, hs₂, hc']
  exact ⟨v₂, hv₂, rfl, rfl⟩

theorem CoreMemDesign.settleAssignAt_two_ident_fast_refines
    (E : CoreMemDesign) (s a₁ a₂ : CoreMemFastState) (view : SvState)
    (index : Nat) (name₁ name₂ : String) (value₁ value₂ : PExpr)
    (width₁ width₂ : Nat) (v₁ v₂ : LVec) (x₁ x₂ : VarId)
    (hwidth₁ : E.scalarWidth? name₁ = some width₁)
    (hwidth₂ : E.scalarWidth? name₂ = some width₂)
    (hresolve₁ : E.scalar.resolve name₁ = some x₁)
    (hresolve₂ : E.scalar.resolve name₂ = some x₂)
    (hpath₁ : x₁.path = []) (hpath₂ : x₂.path = [])
    (hbound₁ : x₁.decl < s.scalar.cells.size)
    (hbound₂ : x₂.decl < a₁.scalar.cells.size)
    (hv₁ : E.evalScalarAssignAtView E.env E.elems s.toState view
      (some width₁) index value₁ = .ok v₁)
    (hv₂ : E.evalScalarAssignAtView E.env E.elems a₁.toState
      (SvState.set view name₁ v₁) (some width₂) (index + 1) value₂ = .ok v₂)
    (h₁ : E.fastScalarAssignAt s view index name₁ value₁ = .ok a₁)
    (h₂ : E.fastScalarAssignAt a₁ (SvState.set view name₁ v₁)
      (index + 1) name₂ value₂ = .ok a₂) :
    E.settleAssignAt E.env E.elems s.toState view index
      [.assign (.ident name₁) value₁, .assign (.ident name₂) value₂] =
      .ok (a₂.toState, SvState.set (SvState.set view name₁ v₁) name₂ v₂) := by
  have hs₁ := E.fastScalarAssignAt_toState s a₁ view index name₁ value₁
    width₁ v₁ x₁ hwidth₁ hresolve₁ hpath₁ hbound₁ hv₁ h₁
  have hs₂ := E.fastScalarAssignAt_toState a₁ a₂ (SvState.set view name₁ v₁)
    (index + 1) name₂ value₂ width₂ v₂ x₂ hwidth₂ hresolve₂ hpath₂ hbound₂ hv₂ h₂
  have hv₂' := hv₂
  rw [hs₁] at hv₂'
  simp [CoreMemDesign.settleAssignAt, hwidth₁, hwidth₂, hv₁, hv₂', hs₁, hs₂]

end LeanModels.Sv.Kernel
