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

theorem FastConfig.toConfig_ofConfig (E : Elab) (c : Config) :
    (FastConfig.ofConfig E c).toConfig = c := by
  cases c
  simp [FastConfig.ofConfig, FastConfig.toConfig, FastConfig.store]
  rw [arrayStore_cells]

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

theorem fastStep_assign_eq (E : Elab) (ch : Choice) (c : FastConfig)
    (p : ProcId) (rest : List ProcId) (t : Lhs2) (e : Expr2)
    (a' : Array Val)
    (hchoose : ch.choose c.k c.active = p :: rest)
    (hp : E.procs[p]? = some (.assign t e))
    (hfast : fastActivateAssign E c t e = .ok a') :
    fastStep E ch c =
      .ok (some (FastConfig.mk a' c.fallback
        (rest ++ (E.triggered (E.view c.store)
          (E.view ((FastConfig.mk a' c.fallback [] (c.k + 1)).store))).filter
            (fun q => decide (q ∉ rest))) (c.k + 1))) := by
  unfold fastStep
  rw [hchoose]
  have hv : E.view ({ cells := a', fallback := c.fallback, active := [], k := c.k + 1 } : FastConfig).store =
      E.view ({ cells := a', fallback := c.fallback, active := [], k := c.k + 1 } : FastConfig).store := rfl
  simp [hp, hfast, fastTriggered, hv]

theorem step_assign_eq (E : Elab) (ch : Choice) (c : FastConfig)
    (p : ProcId) (rest : List ProcId) (s' : Store)
    (hchoose : ch.choose c.k c.active = p :: rest)
    (hact : activate E p c.store = .ok (.ok (), s')) :
    step E ch c.toConfig =
      .next (Config.mk s' (rest ++
        (E.triggered (E.view c.store) (E.view s')).filter (fun q => decide (q ∉ rest)))
        (c.k + 1)) := by
  unfold step
  simp only [FastConfig.toConfig]
  rw [hchoose]
  simp [hact]

theorem fastStep_assign_refines_step (E : Elab) (ch : Choice) (c : FastConfig)
    (p : ProcId) (rest : List ProcId) (t : Lhs2) (e : Expr2)
    (a' : Array Val) (s' : Store)
    (hchoose : ch.choose c.k c.active = p :: rest)
    (hp : E.procs[p]? = some (.assign t e))
    (hfast : fastActivateAssign E c t e = .ok a')
    (hact : activate E p c.store = .ok (.ok (), s'))
    (hstore : arrayStore a' c.fallback = s') :
    ∃ fc, fastStep E ch c = .ok (some fc) ∧
      step E ch c.toConfig = .next fc.toConfig := by
  let fc := FastConfig.mk a' c.fallback
    (rest ++ (E.triggered (E.view c.store) (E.view s')).filter
      (fun q => decide (q ∉ rest))) (c.k + 1)
  refine ⟨fc, ?_, ?_⟩
  · have h := fastStep_assign_eq E ch c p rest t e a' hchoose hp hfast
    simpa [fc, hstore, FastConfig.store] using h
  · have h := step_assign_eq E ch c p rest s' hchoose hact
    simpa [fc, FastConfig.toConfig, FastConfig.store, hstore] using h

theorem fastStep_fallback_eq (E : Elab) (ch : Choice) (c : FastConfig)
    (p : ProcId) (rest : List ProcId)
    (hchoose : ch.choose c.k c.active = p :: rest)
    (hassign : ∀ t e, E.procs[p]? ≠ some (.assign t e)) :
    fastStep E ch c =
      match step E ch c.toConfig with
      | .next c' => .ok (some (FastConfig.ofConfig E c'))
      | .slotClosed _ => .ok none
      | .refused r => .unsupported r.observable.2 := by
  unfold fastStep
  rw [hchoose]
  cases hp : E.procs[p]? with
  | none => simp [hp, step]
  | some proc =>
      cases proc with
      | assign t e => exact (hassign t e hp).elim
      | comb body => simp [hp, step]
      | implicit body => simp [hp, step]

/-! A flat assignment is the only extra premise needed by the direct route.
The premise is stated on the source-shaped windows, so it remains parametric
and does not expand the array or the process list. -/
def FlatAssignment (E : Elab) (c : FastConfig) (t : Lhs2) : Prop :=
  ∀ ws, t.windows? E.toDesign2 = some ws →
    ∀ wn off, (wn, off) ∈ Win.placed ws →
      ∃ x, E.resolve wn.1 = some x ∧ x.path = [] ∧ x.decl < c.cells.size

def FlatAssignmentRun (E : Elab) (c : FastConfig) : Prop :=
  ∀ (p : ProcId) (t : Lhs2) (e : Expr2) (a' : Array Val),
    E.procs[p]? = some (Proc0.assign t e) →
    fastActivateAssign E c t e = .ok a' →
      ∃ ws v, t.windows? E.toDesign2 = some ws ∧
        evalPure2 (E.view c.store) e = .ok v ∧ FlatAssignment E c t

theorem flatAssignmentRun_of_flat (E : Elab) (c : FastConfig)
    (hflat : ∀ (p : ProcId) (t : Lhs2) (e : Expr2),
      E.procs[p]? = some (Proc0.assign t e) → FlatAssignment E c t) :
    FlatAssignmentRun E c := by
  intro p t e a' hp hfa
  unfold fastActivateAssign at hfa
  split at hfa
  next ws hws =>
    cases hev : evalPure2 (E.view c.store) e with
    | timeout => simp [hev] at hfa
    | unsupported msg => simp [hev] at hfa
    | ok v =>
        exact ⟨ws, v, hws, rfl, hflat p t e hp⟩
  next hnone hno =>
    simp at hfa

theorem fastStep_assign_refines_step_of_flat (E : Elab) (ch : Choice)
    (c : FastConfig) (p : ProcId) (rest : List ProcId)
    (t : Lhs2) (e : Expr2) (ws : List Win) (v : LVec) (a' : Array Val)
    (hchoose : ch.choose c.k c.active = p :: rest)
    (hp : E.procs[p]? = some (.assign t e))
    (hws : t.windows? E.toDesign2 = some ws)
    (hv : evalPure2 (E.view c.store) e = .ok v)
    (hfast : fastActivateAssign E c t e = .ok a')
    (hflat : FlatAssignment E c t) :
    ∃ fc, fastStep E ch c = .ok (some fc) ∧
      step E ch c.toConfig = .next fc.toConfig := by
  have hflat' : ∀ wn off, (wn, off) ∈ Win.placed ws →
      ∃ x, E.resolve wn.1 = some x ∧ x.path = [] ∧ x.decl < c.cells.size :=
    hflat ws hws
  have hfastWins : fastWriteWins E c.fallback c.cells
      (v.resizeU (Win.sumWidth ws)) (Win.placed ws) = .ok a' := by
    simpa [fastActivateAssign, hws, hv] using hfast
  have hstore : arrayStore a' c.fallback =
      E.writeWins c.store (v.resizeU (Win.sumWidth ws)) (Win.placed ws) :=
    fastActivateAssign_store_eq E c t e ws v a' hws hv hfastWins hflat'
  have hact' : activate E p c.store = .ok (.ok (),
      E.writeWins c.store (v.resizeU (Win.sumWidth ws)) (Win.placed ws)) := by
    simp only [activate, hp, hws]
    rw [SemMWith.run_bind_ok (SemMWith.run_get c.store)]
    rw [SemMWith.run_bind_ok (show ofRes (evalPure2 (E.view c.store) e) c.store =
      .ok (.ok v, c.store) by rw [hv]; rfl)]
    rfl
  exact fastStep_assign_refines_step E ch c p rest t e a'
    (E.writeWins c.store (v.resizeU (Win.sumWidth ws)) (Win.placed ws))
    hchoose hp hfast hact' hstore

theorem fastStep_refines_step_of_flat (E : Elab) (ch : Choice)
    (c : FastConfig) (hflat : FlatAssignmentRun E c)
    {fc : FastConfig} (h : fastStep E ch c = .ok (some fc)) :
    step E ch c.toConfig = .next fc.toConfig := by
  cases hch : ch.choose c.k c.active with
  | nil => simp [fastStep, hch] at h
  | cons p rest =>
      cases hp : E.procs[p]? with
      | none =>
          have hfb := fastStep_fallback_eq E ch c p rest hch
            (by intro t e hpe; simp [hp] at hpe)
          rw [hfb] at h
          cases hs : step E ch c.toConfig with
          | next c' =>
              simp [hs] at h
              rw [← h, FastConfig.toConfig_ofConfig]
          | slotClosed c' => simp [hs] at h
          | refused r => simp [hs] at h
      | some proc =>
          cases proc with
          | assign t e =>
              simp only [fastStep, hch, hp] at h
              cases hfa : fastActivateAssign E c t e with
              | timeout => simp [hfa] at h
              | unsupported msg => simp [hfa] at h
              | ok a' =>
                  simp [hfa] at h
                  unfold FlatAssignmentRun at hflat
                  obtain ⟨ws, v, hws, hv, hflat'⟩ := hflat p t e a' hp hfa
                  have href := fastStep_assign_refines_step_of_flat E ch c p rest t e
                    ws v a' hch hp hws hv hfa hflat'
                  obtain ⟨fc', hfast', hstep'⟩ := href
                  have h2 : fastStep E ch c = .ok (some fc) := by
                    simpa [fastStep, hch, hp, hfa] using h
                  have hfc : fc' = fc := by
                    exact Option.some.inj (Res.ok.inj (hfast'.symm.trans h2))
                  subst fc'
                  exact hstep'
          | comb body =>
              have hfb := fastStep_fallback_eq E ch c p rest hch
                (by intro t e hpe; simp [hp] at hpe)
              rw [hfb] at h
              cases hs : step E ch c.toConfig with
              | next c' =>
                  simp [hs] at h
                  rw [← h, FastConfig.toConfig_ofConfig]
              | slotClosed c' => simp [hs] at h
              | refused r => simp [hs] at h
          | implicit body =>
              have hfb := fastStep_fallback_eq E ch c p rest hch
                (by intro t e hpe; simp [hp] at hpe)
              rw [hfb] at h
              cases hs : step E ch c.toConfig with
              | next c' =>
                  simp [hs] at h
                  rw [← h, FastConfig.toConfig_ofConfig]
              | slotClosed c' => simp [hs] at h
              | refused r => simp [hs] at h

def fastExec (E : Elab) (ch : Choice) : Nat → FastConfig → Res FastConfig
  | 0, _ => .timeout
  | n + 1, c =>
      match fastStep E ch c with
      | .ok none => .ok c
      | .ok (some c') => fastExec E ch n c'
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

theorem fastExec_succ_of_closed (E : Elab) (ch : Choice) (n : Nat)
    (c c' : FastConfig) (h : fastStep E ch c = .ok none) :
    fastExec E ch (n + 1) c = .ok c := by
  simp [fastExec, h]

theorem fastExec_succ_of_next (E : Elab) (ch : Choice) (n : Nat)
    (c c' c'' : FastConfig)
    (hstep : fastStep E ch c = .ok (some c'))
    (htail : fastExec E ch n c' = .ok c'') :
    fastExec E ch (n + 1) c = .ok c'' := by
  simp [fastExec, hstep, htail]

/-! Once the direct instrument has established its one-step refinement, the
recursive executor inherits the exact E slot judgment.  Keeping the two
one-step premises explicit makes the theorem reusable for the assignment and
fallback branches without introducing a second scheduler semantics. -/
theorem fastExec_sound_of_step_refines (E : Elab) (ch : Choice)
    (hclosed : ∀ {c : FastConfig},
      fastStep E ch c = .ok none →
        step E ch c.toConfig = .slotClosed c.toConfig)
    (hnext : ∀ {c c' : FastConfig},
      fastStep E ch c = .ok (some c') →
        step E ch c.toConfig = .next c'.toConfig)
    (n : Nat) (c c' : FastConfig)
    (h : fastExec E ch (n + 1) c = .ok c') :
    SlotCloses E ch c.toConfig c'.toConfig := by
  induction n generalizing c c' with
  | zero =>
      simp only [fastExec] at h
      cases hs : fastStep E ch c with
      | ok o =>
          cases ho : o with
          | none =>
              simp only [hs, ho, Res.ok.injEq] at h
              cases h
              have hs' : fastStep E ch c = .ok none := by simpa [ho] using hs
              exact ⟨Steps.refl _, hclosed hs'⟩
          | some c1 =>
              simp only [hs, ho] at h
              simp at h
      | timeout => simp [hs] at h
      | unsupported msg => simp [hs] at h

  | succ n ih =>
      simp only [fastExec] at h
      cases hs : fastStep E ch c with
      | ok o =>
          cases ho : o with
          | none =>
              simp only [hs, ho, Res.ok.injEq] at h
              cases h
              have hs' : fastStep E ch c = .ok none := by simpa [ho] using hs
              exact ⟨Steps.refl _, hclosed hs'⟩
          | some c1 =>
              simp only [hs, ho] at h
              change fastExec E ch (n + 1) c1 = .ok c' at h
              cases ht : fastExec E ch (n + 1) c1 with
              | ok d =>
                  have hdc : d = c' := by
                    apply Res.ok.inj
                    rw [← ht]
                    exact h
                  obtain ⟨hsteps, hclose⟩ := ih c1 d ht
                  have hs' : fastStep E ch c = .ok (some c1) := by
                    simpa [ho] using hs
                  subst c'
                  exact ⟨Steps.head (hnext hs') hsteps, hclose⟩
              | timeout => rw [ht] at h; cases h
              | unsupported msg => rw [ht] at h; cases h
      | timeout => simp [hs] at h
      | unsupported msg => simp [hs] at h

theorem fastExec_sound_of_flat (E : Elab) (ch : Choice)
    (hclosed : ∀ {c : FastConfig},
      fastStep E ch c = .ok none →
        step E ch c.toConfig = .slotClosed c.toConfig)
    (hflat : ∀ c : FastConfig, FlatAssignmentRun E c)
    (n : Nat) (c c' : FastConfig)
    (h : fastExec E ch (n + 1) c = .ok c') :
    SlotCloses E ch c.toConfig c'.toConfig := by
  exact fastExec_sound_of_step_refines E ch hclosed
    (fun {c} {c'} hs => fastStep_refines_step_of_flat E ch c (hflat c) hs)
    n c c' h

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
