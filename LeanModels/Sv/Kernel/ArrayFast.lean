import LeanModels.Sv.Kernel.ArrayE

/-!
# Direct flat-array E executor

The original array executor snapshots a function-valued `Store` after every
micro-step.  This companion route keeps flat continuous-assignment writes in
the array directly; non-flat and procedural processes fall back to the
authoritative executor.  The source AST and E evaluator are unchanged.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

structure FastConfig where
  cells : Array Val
  fallback : Store
  active : List ProcId
  k : Nat := 0

def FastConfig.store (c : FastConfig) : Store := arrayStore c.cells c.fallback

def FastConfig.ofConfig (E : Elab) (c : Config) : FastConfig :=
  { cells := arrayCells c.store E.decls.size, fallback := c.store,
    active := c.active, k := c.k }

def FastConfig.toConfig (c : FastConfig) : Config :=
  { store := c.store, active := c.active, k := c.k }

/-! The array view starts extensionally equal to the authoritative function
store.  This is the first refinement lemma for the direct route; subsequent
write lemmas can use it to relate a flat array update to `Store.set`. -/
theorem FastConfig.ofConfig_store (E : Elab) (c : Config) :
    (FastConfig.ofConfig E c).store = c.store := by
  unfold FastConfig.ofConfig FastConfig.store
  exact arrayStore_cells c.store E.decls.size

theorem arrayStore_set_flat (a : Array Val) (fallback : Store) (x : VarId) (v : Val)
    (hp : x.path = []) (hb : x.decl < a.size) :
    arrayStore (a.setIfInBounds x.decl v) fallback x = v := by
  cases x with
  | mk path decl =>
      cases path with
      | nil => simp [arrayStore, Array.getD, hb]
      | cons head tail => simp_all

theorem arrayStore_set_flat_frame (a : Array Val) (fallback : Store)
    (x y : VarId) (v : Val) (hp : x.path = []) (hb : x.decl < a.size)
    (hne : y ≠ x) :
    arrayStore (a.setIfInBounds x.decl v) fallback y = arrayStore a fallback y := by
  cases x with
  | mk xp xd =>
    cases y with
    | mk yp yd =>
      cases xp with
      | nil =>
        cases yp with
        | nil =>
            simp only [arrayStore, Array.getD]
            by_cases hy : yd < a.size
            · have hxy : xd ≠ yd := by
                intro he
                apply hne
                cases he
                rfl
              have hs := Array.getElem?_setIfInBounds
                (xs := a) (i := xd) (j := yd) (a := v)
              rw [Array.getElem?_eq_getElem hy] at hs
              simp [hy, hxy] at hs ⊢
            · simp [hy]
        | cons yh yt => rfl
      | cons xh xt => simp_all

theorem arrayStore_set_flat_store (a : Array Val) (fallback : Store)
    (x : VarId) (v : Val) (hp : x.path = []) (hb : x.decl < a.size) :
    arrayStore (a.setIfInBounds x.decl v) fallback =
      Store.set (arrayStore a fallback) x v := by
  funext y
  by_cases hxy : y = x
  · subst y
    simp [Store.set, arrayStore_set_flat a fallback x v hp hb]
  · rw [arrayStore_set_flat_frame a fallback x y v hp hb hxy]
    simp [Store.set, hxy]

theorem fastWriteWin_ok_of_flat (E : Elab) (fallback : Store) (a : Array Val)
    (name : String) (x : VarId) (lo : Nat) (part : LVec)
    (hx : E.resolve name = some x) (hp : x.path = []) (hb : x.decl < a.size) :
    arrayStore (a.setIfInBounds x.decl
      ((a.getD x.decl (fallback x)).write lo part)) fallback =
      E.writeWin (arrayStore a fallback) name lo part := by
  rw [show E.writeWin (arrayStore a fallback) name lo part =
      Store.set (arrayStore a fallback) x
        ((arrayStore a fallback x).write lo part) by
    unfold Elab.writeWin
    rw [hx]]
  rw [arrayStore_set_flat_store a fallback x
    ((a.getD x.decl (fallback x)).write lo part) hp hb]
  simp [arrayStore, Array.getD, hp, hb]

def fastWriteWins (E : Elab) (fallback : Store) (a : Array Val)
    (value : LVec) : List (Win × Nat) → Res (Array Val)
  | [] => .ok a
  | ((name, lo, width), off) :: rest =>
      match E.resolve name with
      | none => .unsupported s!"10.3.2: continuous assignment target '{name}' is undeclared"
      | some x =>
          match x.path with
          | _ :: _ => .unsupported "10.3.2: non-flat continuous assignment target"
          | [] =>
              let old := a.getD x.decl (fallback x)
              fastWriteWins E fallback
                (a.setIfInBounds x.decl (old.write lo (value.extract off width))) value rest


theorem fastWriteWins_ok_of_flat (E : Elab) (fallback : Store) (a : Array Val)
    (value : LVec) : ∀ (xs : List (Win × Nat)) (a' : Array Val),
    fastWriteWins E fallback a value xs = .ok a' →
    (∀ wn off, (wn, off) ∈ xs →
      ∃ x, E.resolve wn.1 = some x ∧ x.path = [] ∧ x.decl < a.size) →
    arrayStore a' fallback = E.writeWins (arrayStore a fallback) value xs := by
  intro xs
  induction xs generalizing a with
  | nil =>
      intro a' h _
      simp only [fastWriteWins, Res.ok.injEq] at h
      cases h
      rfl
  | cons head rest ih =>
      intro a' h hflat
      obtain ⟨x, hx, hp, hb⟩ := hflat head.1 head.2 (by simp)
      cases x with
      | mk path decl =>
        cases path with
        | nil =>
          simp only [fastWriteWins] at h
          rw [hx] at h
          let old := a.getD decl (fallback {path := [], decl})
          let a1 := a.setIfInBounds decl
            (old.write head.1.2.1 (value.extract head.2 head.1.2.2))
          have htail : fastWriteWins E fallback a1 value rest = .ok a' := by
            simpa [a1, old] using h
          have hflat' : ∀ wn off, (wn, off) ∈ rest →
              ∃ y, E.resolve wn.1 = some y ∧ y.path = [] ∧ y.decl < a1.size := by
            intro wn off hm
            obtain ⟨y, hy, hpy, hby⟩ := hflat wn off (by simp [hm])
            exact ⟨y, hy, hpy, by simpa [a1, hb] using hby⟩
          have ih' := ih a1 a' htail hflat'
          rw [ih']
          rw [arrayStore_set_flat_store a fallback {path := [], decl}
            ((a.getD decl (fallback {path := [], decl})).write
              head.1.2.1 (value.extract head.2 head.1.2.2)) hp hb]
          simp only [Elab.writeWins]
          simp [Elab.writeWin, hx, hb, old, a1, arrayStore, Array.getD]
        | cons hd tl => simp_all

def fastActivateAssign (E : Elab) (c : FastConfig) (t : Lhs2) (e : Expr2) : Res (Array Val) := do
  let some ws := t.windows? E.toDesign2
    | .unsupported "10.3.2: continuous assignment target has no static window"
  let v ← evalPure2 (E.view c.store) e
  fastWriteWins E c.fallback c.cells (v.resizeU (Win.sumWidth ws)) (Win.placed ws)

theorem fastActivateAssign_store_eq (E : Elab) (c : FastConfig)
    (t : Lhs2) (e : Expr2) (ws : List Win) (v : LVec) (a' : Array Val)
    (hws : t.windows? E.toDesign2 = some ws)
    (hv : evalPure2 (E.view c.store) e = .ok v)
    (h : fastWriteWins E c.fallback c.cells
      (v.resizeU (Win.sumWidth ws)) (Win.placed ws) = .ok a')
    (hflat : ∀ wn off, (wn, off) ∈ Win.placed ws →
      ∃ x, E.resolve wn.1 = some x ∧ x.path = [] ∧ x.decl < c.cells.size) :
    arrayStore a' c.fallback =
      E.writeWins c.store (v.resizeU (Win.sumWidth ws)) (Win.placed ws) := by
  exact fastWriteWins_ok_of_flat E c.fallback c.cells
    (v.resizeU (Win.sumWidth ws)) (Win.placed ws) a' h hflat

def fastTriggered (E : Elab) (before after : FastConfig) : List ProcId :=
  E.triggered (E.view before.store) (E.view after.store)

def fastStep (E : Elab) (ch : Choice) (c : FastConfig) : Res (Option FastConfig) :=
  match ch.choose c.k c.active with
  | [] => .ok none
  | p :: rest =>
      match E.procs[p]? with
      | some (.assign t e) => do
          let cells ← fastActivateAssign E c t e
          let after : FastConfig := { c with cells, active := [], k := c.k + 1 }
          return some { after with
            active := rest ++ (fastTriggered E c after).filter (fun q => decide (q ∉ rest)) }
      | _ =>
          match step E ch c.toConfig with
          | .next c' => return some (FastConfig.ofConfig E c')
          | .slotClosed _ => return none
          | .refused r => .unsupported r.observable.2

def fastExec (E : Elab) (ch : Choice) : Nat → FastConfig → Res FastConfig
  | 0, _ => .timeout
  | n + 1, c =>
      match fastStep E ch c with
      | .ok none => .ok c
      | .ok (some c') => fastExec E ch n c'
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

def fastRun (E : Elab) (ch : Choice) (fuel : Nat) (env : List SvState) :
    Res (List FastConfig) :=
  match env with
  | [] => .ok []
  | entry :: rest =>
      let c := FastConfig.ofConfig E (Config.start E entry)
      match fastExec E ch fuel c with
      | .ok c' =>
          match fastRun E ch fuel rest with
          | .ok rows => .ok (c' :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

end LeanModels.Sv.Kernel
