import LeanModels.Sv.Kernel.Core0
import LeanModels.Sv.Comb2

/-!
# R-COMB-0: the keystone refinement on E-core-0 (`LeanModels.Sv.Kernel`)

Gate G-A of `svgolf/design/architecture/EXECUTION-PLAN.md`, designed in
`svgolf/design/architecture/X1-NOTE.md` §3. **Status: derived from E**
(`Core0.lean`); `closed_eq_combSettle2` / `rcomb0_combSettle2` are the first
slice of a **transport theorem** to Design2's `combSettle2`.

## Two layers

* **Generic** (namespace `Settles`): the whole settle argument is stated for
  an EQUATION DESIGN `d` related to E by `Settles E d rank` — each
  activation of E writes, on the view, what process `p` of `d` writes
  (`combWrite`); E's sensitivity covers `d`'s reads (`complete`); a trigger
  goes up in rank (`ranked`). For an assign-only design `d = E.toDesign2`
  (`Settles.ofProfile0`); with an `always_comb`, `d` is its lowering
  (`Core0Proc.lean`, gate G-B).
* **Assign-only** (gate G-A, the names below): the generic theorems at
  `Settles.ofProfile0`, under `Profile0` and `Acyclic E.toDesign2`.

## Statements (assign-only)

* `exec_closes` / `slot_closes`: under the profile (`Profile0`, debt D-X1a)
  and a rank certificate (`Acyclic`), from every configuration satisfying the
  settle invariant (`SettleInv`), EVERY legal schedule closes the slot, and the
  executor closes it within `potential + 1` steps. The measure is explicit:
  `potential N rank c = Σ_{q ∈ c.active} (N+1)^(N − rank q)` (`step_decreases`).
* `SlotCloses.combEqs`: the closed store solves the equations (`CombEqs`) and
  keeps every undriven bit (`Frame`).
* `combEqs_unique`: under the rank, the solution is unique given the undriven
  bits, so the closed store is schedule-independent
  (`rcomb0_schedule_independent`). `rcomb0` packages all of it.
* `closed_eq_combSettle2`, `rcomb0_combSettle2`: the closed store IS what
  `combSettle2` returns from the same start, for every Choice and every
  `ScheduleOracle` (by uniqueness, not by a fixture).
* Negative: `osc_not_acyclic`, `swap_not_acyclic` (the rank hypothesis
  fails); the `#guard` rows of `Core0.lean` show `osc` never closing and
  `swap` closing at two different stores.

## Proof architecture

E's store is related to Design2's state only through `Elab.view`;
`Elab.view_writeWins` says E's write IS `SvState.writeWins` on the view, so one
activation is `combWrite` (`step_cons`), and the window, frame and read-back
lemmas of `Comb2Base`/`Comb2Term` apply unchanged.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

open LeanModels.Sv.Comb2Term

/-! ## Name resolution and the view -/

theorem viewAux_keys (s : Store) : ∀ (ds : List Decl) (i : Nat),
    (viewAux s ds i).map Prod.fst = ds.map Decl.name
  | [], _ => rfl
  | dc :: ds, i => by simp only [viewAux, List.map_cons, viewAux_keys s ds (i + 1)]

theorem lookup_viewAux (s : Store) (n : String) : ∀ (ds : List Decl) (i : Nat),
    SvState.lookup (viewAux s ds i) n = (resolveAux n ds i).map fun x => (s x).bits
  | [], _ => rfl
  | dc :: ds, i => by
      by_cases h : (dc.name == n) = true
      · simp only [viewAux, resolveAux, SvState.lookup]
        rw [if_pos h, if_pos h]
        rfl
      · simp only [viewAux, resolveAux, SvState.lookup]
        rw [if_neg h, if_neg h]
        exact lookup_viewAux s n ds (i + 1)

theorem resolveAux_some {n : String} : ∀ {ds : List Decl} {i : Nat} {x : VarId},
    resolveAux n ds i = some x →
      ∃ j dc, x = { decl := i + j } ∧ ds[j]? = some dc ∧
        ds.find? (fun dc => dc.name == n) = some dc
  | [], _, _, h => by simp [resolveAux] at h
  | dc :: ds, i, x, h => by
      by_cases hn : (dc.name == n) = true
      · simp only [resolveAux, if_pos hn, Option.some.injEq] at h
        subst h
        exact ⟨0, dc, rfl, rfl, List.find?_cons_of_pos hn⟩
      · simp only [resolveAux, if_neg hn] at h
        obtain ⟨j, dc', rfl, hj, hf⟩ := resolveAux_some h
        refine ⟨j + 1, dc', by congr 1; omega, by simpa using hj, ?_⟩
        rw [List.find?_cons_of_neg (p := fun (dc : Decl) => dc.name == n) hn]
        exact hf

theorem resolveAux_none {n : String} : ∀ {ds : List Decl} {i : Nat},
    resolveAux n ds i = none → ds.find? (fun dc => dc.name == n) = none
  | [], _, _ => rfl
  | dc :: ds, i, h => by
      by_cases hn : (dc.name == n) = true
      · simp only [resolveAux, if_pos hn] at h
        cases h
      · simp only [resolveAux, if_neg hn] at h
        rw [List.find?_cons_of_neg (p := fun (dc : Decl) => dc.name == n) hn]
        exact resolveAux_none h

/-- A resolved name is a declaration of that name, the first one, so its
declared width is `declWidth`'s. -/
theorem Elab.resolve_some {E : Elab} {n : String} {x : VarId} (h : E.resolve n = some x) :
    ∃ dc, E.declOf x = some dc ∧ dc.name = n ∧ dc ∈ E.decls.toList ∧
      E.toDesign2.declWidth n = some dc.width := by
  obtain ⟨j, dc, rfl, hj, hf⟩ := resolveAux_some h
  refine ⟨dc, ?_, ?_, List.mem_of_find?_eq_some hf, ?_⟩
  · show E.decls[0 + j]? = some dc
    rw [Nat.zero_add, ← Array.getElem?_toList]
    exact hj
  · have := List.find?_some hf
    simpa using this
  · simp [Design2.declWidth, Elab.toDesign2, hf]

theorem Elab.resolve_none {E : Elab} {n : String} (h : E.resolve n = none) :
    E.toDesign2.declWidth n = none := by
  simp [Design2.declWidth, Elab.toDesign2, resolveAux_none h]

theorem Elab.lookup_view (E : Elab) (s : Store) (n : String) :
    SvState.lookup (E.view s) n = (E.resolve n).map fun x => (s x).bits :=
  lookup_viewAux s n _ 0

theorem Elab.keys_view (E : Elab) (s : Store) :
    (E.view s).map Prod.fst = E.decls.toList.map Decl.name :=
  viewAux_keys s _ 0

theorem viewAux_congr {s s' : Store} : ∀ (ds : List Decl) (i : Nat),
    (∀ j, i ≤ j → s { decl := j } = s' { decl := j }) → viewAux s ds i = viewAux s' ds i
  | [], _, _ => rfl
  | dc :: ds, i, h => by
      simp only [viewAux, h i (Nat.le_refl _),
        viewAux_congr ds (i + 1) fun j hj => h j (by omega)]

theorem viewAux_set (s : Store) (n : String) (v : Val) : ∀ (ds : List Decl) (i : Nat) (x : VarId),
    resolveAux n ds i = some x →
      viewAux (s.set x v) ds i = SvState.set (viewAux s ds i) n v.bits
  | [], _, _, h => by simp [resolveAux] at h
  | dc :: ds, i, x, h => by
      by_cases hn : (dc.name == n) = true
      · simp only [resolveAux, if_pos hn, Option.some.injEq] at h
        subst h
        have hname : dc.name = n := by simpa using hn
        simp only [viewAux, SvState.set]
        rw [if_pos hn, hname]
        congr 1
        · simp [Store.set]
        · refine viewAux_congr ds (i + 1) fun j hj => ?_
          have hne : ({ decl := j } : VarId) ≠ { decl := i } := by
            intro h'
            have := congrArg VarId.decl h'
            simp only at this
            omega
          simp [Store.set, hne]
      · simp only [resolveAux, if_neg hn] at h
        have hge : i + 1 ≤ x.decl := by
          obtain ⟨j, _, rfl, _⟩ := resolveAux_some h
          simp
        have hne : ({ decl := i } : VarId) ≠ x := by
          intro h'
          subst h'
          exact Nat.not_succ_le_self i hge
        simp only [viewAux, SvState.set]
        rw [if_neg hn]
        congr 1
        · simp [Store.set, hne]
        · exact viewAux_set s n v ds (i + 1) x h

/-- Writing a resolved variable is `SvState.set` on the view. -/
theorem Elab.view_set (E : Elab) (s : Store) {n : String} {x : VarId} (h : E.resolve n = some x)
    (v : Val) : E.view (s.set x v) = SvState.set (E.view s) n v.bits :=
  viewAux_set s n v _ 0 x h

/-! ## Typed stores -/

/-- X1's 4-state clause: every declaration is 4-state. -/
def AllFour (E : Elab) : Prop := ∀ dc ∈ E.decls.toList, dc.twoState = false

theorem Elab.Typed.set {E : Elab} {s : Store} (hT : E.Typed s) {x : VarId} {v : Val}
    (hv : v.ty = (s x).ty) : E.Typed (s.set x v) := by
  intro y dc hy
  by_cases hyx : y = x
  · subst hyx
    simp only [Store.set, ↓reduceIte]
    rw [hv]
    exact hT y dc hy
  · simp only [Store.set, if_neg hyx]
    exact hT y dc hy

theorem Elab.Typed.writeWin {E : Elab} {s : Store} (hT : E.Typed s) (n : String) (lo : Nat)
    (p : LVec) : E.Typed (E.writeWin s n lo p) := by
  unfold Elab.writeWin
  split
  · exact hT.set rfl
  · exact hT

theorem Elab.Typed.writeWins {E : Elab} (val : LVec) :
    ∀ {s : Store} (pl : List (Win × Nat)), E.Typed s → E.Typed (E.writeWins s val pl)
  | _, [], hT => hT
  | _, ((n, lo, _), _) :: rest, hT => Elab.Typed.writeWins val rest (hT.writeWin n lo _)

theorem Elab.typed_initStore (E : Elab) : E.Typed E.initStore := by
  intro x dc h
  simp only [Elab.initStore, h]
  rfl

theorem Elab.fourState_of_resolve {E : Elab} {s : Store} (hT : E.Typed s) (h4 : AllFour E)
    {n : String} {x : VarId} (hx : E.resolve n = some x) : (s x).ty.fourState = true := by
  obtain ⟨dc, hdecl, -, hmem, -⟩ := Elab.resolve_some hx
  rw [hT x dc hdecl]
  simp [VType.ofDecl, h4 dc hmem]

/-- One window write, through the view: `SvState.writeWins`'s step. -/
theorem Elab.view_writeWin {E : Elab} {s : Store} (hT : E.Typed s) (h4 : AllFour E) (n : String)
    (lo : Nat) (p : LVec) :
    E.view (E.writeWin s n lo p) =
      match SvState.lookup (E.view s) n with
      | some old => SvState.set (E.view s) n (old.insertAt lo p)
      | none => E.view s := by
  rw [E.lookup_view]
  unfold Elab.writeWin
  cases hx : E.resolve n with
  | none => rfl
  | some x =>
      simp only [Option.map_some]
      rw [E.view_set s hx]
      simp only [Val.write, VType.conv_of_four (Elab.fourState_of_resolve hT h4 hx)]

/-- **E's write is `SvState.writeWins` on the view.** -/
theorem Elab.view_writeWins {E : Elab} (h4 : AllFour E) (val : LVec) :
    ∀ {s : Store} (pl : List (Win × Nat)), E.Typed s →
      E.view (E.writeWins s val pl) = SvState.writeWins (E.view s) val pl
  | _, [], _ => rfl
  | s, ((n, lo, w), off) :: rest, hT => by
      simp only [Elab.writeWins, SvState.writeWins]
      rw [Elab.view_writeWins h4 val rest (hT.writeWin n lo _), Elab.view_writeWin hT h4]
      rfl

/-- A typed store's view has the comb shape. -/
theorem Elab.shape_view {E : Elab} (hd : CombDesign E.toDesign2) {s : Store} (hT : E.Typed s) :
    StateShape E.toDesign2 (E.view s) := by
  refine ⟨E.keys_view s, fun n hn => ?_⟩
  obtain ⟨i, lo, w, hW⟩ := hn
  obtain ⟨dw, hdw, -⟩ := hd.inWidth i n lo w hW
  cases hx : E.resolve n with
  | none =>
      rw [Elab.resolve_none hx] at hdw
      cases hdw
  | some x =>
      obtain ⟨dc, hdecl, -, -, hwd⟩ := Elab.resolve_some hx
      refine ⟨(s x).bits, by rw [E.lookup_view, hx]; rfl, ?_⟩
      rw [hwd, (s x).width_eq, hT x dc hdecl]
      rfl

/-! ## Processes and one activation -/

theorem Elab.proc_assign_iff {E : Elab} {p : ProcId} {t : Lhs2} {e : Expr2} :
    E.toDesign2.processes[p]? = some (.assign t e) ↔ E.procs[p]? = some (.assign t e) := by
  simp only [Elab.toDesign2, List.getElem?_toArray, List.getElem?_map, Array.getElem?_toList]
  cases E.procs[p]? with
  | none => simp
  | some q => cases q <;> simp [Proc0.toProcess2]

theorem Elab.sens_of_assign {E : Elab} {q : ProcId} {t : Lhs2} {e : Expr2}
    (h : E.toDesign2.processes[q]? = some (.assign t e)) : E.sens q = e.reads := by
  simp [Elab.sens, Elab.proc_assign_iff.mp h]

theorem Elab.size_toDesign2 (E : Elab) : E.toDesign2.processes.size = E.procs.size := by
  simp [Elab.toDesign2]

/-- **One assign activation**, run. -/
theorem activate_assign {E : Elab} {s : Store} {p : ProcId} {t : Lhs2} {e : Expr2} {ws : List Win}
    {v : LVec} (hp : E.procs[p]? = some (.assign t e)) (hws : t.windows? E.toDesign2 = some ws)
    (hv : evalPure2 (E.view s) e = .ok v) :
    activate E p s = .ok (.ok (), E.writeWins s (v.resizeU (Win.sumWidth ws)) (Win.placed ws)) := by
  simp only [activate, hp, hws]
  rw [SemMWith.run_bind_ok (SemMWith.run_get s)]
  rw [SemMWith.run_bind_ok (show ofRes (evalPure2 (E.view s) e) s = .ok (.ok v, s) by
    rw [hv]; rfl)]
  rfl

theorem Elab.mem_triggered {E : Elab} {st st' : SvState} {q : ProcId}
    (h : q ∈ E.triggered st st') : q < E.procs.size ∧ ∃ r ∈ E.sens q, ¬ r.agree st st' := by
  simp only [Elab.triggered, List.mem_filter, List.mem_range, List.any_eq_true] at h
  obtain ⟨hq, r, hr, hna⟩ := h
  exact ⟨hq, r, hr, by simpa using hna⟩

theorem Elab.not_triggered {E : Elab} {st st' : SvState} {q : ProcId} (hq : q < E.procs.size)
    (h : q ∉ E.triggered st st') : ∀ r ∈ E.sens q, r.agree st st' := by
  intro r hr
  refine Classical.byContradiction fun hna => h ?_
  simp only [Elab.triggered, List.mem_filter, List.mem_range, List.any_eq_true]
  exact ⟨hq, r, hr, by simpa using hna⟩

/-! ## The profile and the settle invariant -/

/-- The X1 profile (debt D-X1a: the Design2 comb profile on the image, plus
4-state declarations). A hypothesis, never part of E's meaning. -/
structure Profile0 (E : Elab) : Prop where
  comb : CombDesign E.toDesign2
  four : AllFour E

/-- The equation of process `i` (one conjunct of `CombEqs`). -/
def ProcEq (d : Design2) (st : SvState) (i : Nat) : Prop :=
  ∀ (t : Lhs2) (e : Expr2) (n : String) (lo w off : Nat),
    d.processes[i]? = some (.assign t e) → ((n, lo, w), off) ∈ Win.placed (t.wins d) →
      ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
        old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w

/-- **The settle invariant** (ARCH-NOTE §4.3, "every node that violates its
equation is ready"), against the equation design `d`: the store is typed, the
ready set is a set of process indices, and every process NOT ready satisfies
its equation. -/
structure SettleInv (E : Elab) (d : Design2) (c : Config) : Prop where
  typed : E.Typed c.store
  nodup : c.active.Nodup
  range : ∀ q ∈ c.active, q < E.procs.size
  eqs : ∀ q, q ∉ c.active → ProcEq d (E.view c.store) q

/-- With every process ready, the invariant holds of any typed store. -/
theorem SettleInv.init {E : Elab} {d : Design2} (hsize : d.processes.size = E.procs.size)
    {s : Store} (hT : E.Typed s) : SettleInv E d (Config.init E s) where
  typed := hT
  nodup := List.nodup_range
  range := fun _ hq => List.mem_range.mp hq
  eqs := fun q hq _ _ _ _ _ _ hp _ => by
    refine absurd (List.mem_range.mpr ?_) hq
    have := (Array.getElem?_eq_some_iff.mp hp).1
    rwa [hsize] at this

/-- Bits that no process writes, and the frame: widths and those bits agree. -/
def Undriven (d : Design2) (x : String) (b : Nat) : Prop :=
  ¬ ∃ j wn, d.Writes j wn ∧ (ReadWin.win x b 1).overlaps wn = true

structure Frame (d : Design2) (st st' : SvState) : Prop where
  width : ∀ x, (SvState.lookup st x).map LVec.width = (SvState.lookup st' x).map LVec.width
  undriven : ∀ x b, Undriven d x b → (ReadWin.win x b 1).agree st st'

theorem Frame.refl {d : Design2} (st : SvState) : Frame d st st :=
  ⟨fun _ => rfl, fun _ _ _ => ReadWin.agree_refl _ _⟩

theorem Frame.trans {d : Design2} {a b c : SvState} (h₁ : Frame d a b) (h₂ : Frame d b c) :
    Frame d a c :=
  ⟨fun x => (h₁.width x).trans (h₂.width x),
    fun x i hu => ReadWin.agree_trans (h₁.undriven x i hu) (h₂.undriven x i hu)⟩

theorem Frame.symm {d : Design2} {a b : SvState} (h : Frame d a b) : Frame d b a :=
  ⟨fun x => (h.width x).symm, fun x i hu => ReadWin.agree_symm (h.undriven x i hu)⟩

/-- One process's write is a frame step. -/
theorem Frame.combWrite {d : Design2} {st : SvState} {p : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[p]? = some (.assign t e)) (v : LVec) : Frame d st (combWrite d st t v) := by
  refine ⟨fun x => ?_, fun x b hu => ReadWin.agree_combWrite fun wn hwn => ?_⟩
  · have := ReadWin.agree_combWrite (d := d) (st := st) (t := t) (v := v) (r := .win x 0 0)
      (fun wn _ => by obtain ⟨m, lo, w⟩ := wn; simp [ReadWin.overlaps, Win.overlaps])
    simp only [ReadWin.agree] at this
    have h' := congrArg (Option.map Prod.fst) this
    simpa [Option.map_map, Function.comp_def] using h'
  · cases hov : (ReadWin.win x b 1).overlaps wn with
    | false => rfl
    | true => exact (hu ⟨p, wn, ⟨t, e, hp, hwn⟩, hov⟩).elim

/-! ## The equation design (`Settles`) -/

/-- **What the settle argument needs of an equation design `d`.** Each
activation of E, on a typed store, succeeds and writes on the view exactly
what process `p` of `d` (an assign) writes (`act`: for an assign-only design
this is `activate`'s definition, for an `always_comb` it is R-BODY);
E's sensitivity covers the reads of `d`'s right-hand sides (`complete`:
sensitivity-completeness); a process whose sensitivity overlaps a window of
`p` ranks above `p` (`ranked`, the certificate, bounded by `bound`). -/
structure Settles (E : Elab) (d : Design2) (rank : Nat → Nat) : Prop where
  comb : CombDesign d
  decls : d.decls = E.decls
  size : d.processes.size = E.procs.size
  four : AllFour E
  act : ∀ (s : Store) (p : ProcId), E.Typed s → p < E.procs.size →
    ∃ t e v s', d.processes[p]? = some (.assign t e) ∧ evalPure2 (E.view s) e = .ok v ∧
      activate E p s = .ok (.ok (), s') ∧ E.view s' = combWrite d (E.view s) t v ∧ E.Typed s'
  complete : ∀ (q : ProcId) (t : Lhs2) (e : Expr2), d.processes[q]? = some (.assign t e) →
    ∀ r ∈ e.reads, r ∈ E.sens q
  ranked : ∀ (p q : ProcId) (t : Lhs2) (e : Expr2), d.processes[p]? = some (.assign t e) →
    ∀ r ∈ E.sens q, ∀ w ∈ t.wins d, r.overlaps w = true → rank p < rank q
  bound : ∀ i, i < E.procs.size → rank i < E.procs.size

namespace Settles

variable {E : Elab} {d : Design2} {rank : Nat → Nat}

/-- The certificate of `d` follows: `d`'s reads are in E's sensitivity. -/
theorem acyclicBy (hS : Settles E d rank) : AcyclicBy d rank :=
  fun i j _ ei tj ej wj hi hj hw ⟨r, hr, hov⟩ =>
    hS.ranked j i tj ej hj r (hS.complete i _ ei hi r hr) wj hw hov

theorem acyclic (hS : Settles E d rank) : Acyclic d := ⟨rank, hS.acyclicBy⟩

theorem lt_of_proc (hS : Settles E d rank) {p : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[p]? = some (.assign t e)) : p < E.procs.size := by
  rw [← hS.size]; exact (Array.getElem?_eq_some_iff.mp hp).1

/-- A typed store's view has `d`'s comb shape. -/
theorem shape (hS : Settles E d rank) {s : Store} (hT : E.Typed s) : StateShape d (E.view s) := by
  refine ⟨by rw [E.keys_view s, hS.decls], fun n hn => ?_⟩
  obtain ⟨i, lo, w, hW⟩ := hn
  obtain ⟨dw, hdw, -⟩ := hS.comb.inWidth i n lo w hW
  have hdw' : E.toDesign2.declWidth n = some dw := by
    simp only [Design2.declWidth, hS.decls] at hdw
    exact hdw
  cases hx : E.resolve n with
  | none =>
      rw [Elab.resolve_none hx] at hdw'
      cases hdw'
  | some x =>
      obtain ⟨dc, hdecl, -, -, hwd⟩ := Elab.resolve_some hx
      refine ⟨(s x).bits, by rw [E.lookup_view, hx]; rfl, ?_⟩
      rw [hdw, ← hdw', hwd, (s x).width_eq, hT x dc hdecl]
      rfl

end Settles

/-! ## One step -/

/-- **One step is `combWrite` on the view.** If the Choice puts `p` first, the
step writes, on the view, process `p` of `d` (`step` returns `next`, never
`refused`). -/
theorem Settles.step_cons {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice} {c : Config}
    (hS : Settles E d rank) (hI : SettleInv E d c)
    {p : ProcId} {rest : List ProcId} (hch : ch.choose c.k c.active = p :: rest) :
    ∃ t e v, d.processes[p]? = some (.assign t e) ∧
      evalPure2 (E.view c.store) e = .ok v ∧
      ∃ s', E.view s' = combWrite d (E.view c.store) t v ∧ E.Typed s' ∧
        step E ch c = .next { store := s'
                              active := rest ++ (E.triggered (E.view c.store) (E.view s')).filter
                                (fun q => decide (q ∉ rest))
                              k := c.k + 1 } := by
  have hpa : p ∈ c.active := by
    have : p ∈ ch.choose c.k c.active := by rw [hch]; exact List.mem_cons_self ..
    exact (ch.choose_perm c.k c.active).mem_iff.mp this
  obtain ⟨t, e, v, s', hp, hv, ha, hview, hT⟩ := hS.act c.store p hI.typed (hI.range p hpa)
  refine ⟨t, e, v, hp, hv, s', hview, hT, ?_⟩
  unfold step
  rw [hch]
  simp only [ha]

/-- A successful step, inverted. -/
theorem Settles.step_next_spec {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    {c c' : Config} (hS : Settles E d rank) (hI : SettleInv E d c) (h : step E ch c = .next c') :
    ∃ p rest t e v, ch.choose c.k c.active = p :: rest ∧
      d.processes[p]? = some (.assign t e) ∧
      evalPure2 (E.view c.store) e = .ok v ∧
      E.view c'.store = combWrite d (E.view c.store) t v ∧ E.Typed c'.store ∧
      c'.active = rest ++ (E.triggered (E.view c.store) (E.view c'.store)).filter
        (fun q => decide (q ∉ rest)) := by
  cases hch : ch.choose c.k c.active with
  | nil => simp [step, hch] at h
  | cons p rest =>
      obtain ⟨t, e, v, hp, hv, s', hview, hT, hstep⟩ := hS.step_cons hI hch
      rw [hstep, StepResult.next.injEq] at h
      subst h
      exact ⟨p, rest, t, e, v, rfl, hp, hv, hview, hT, rfl⟩

/-- A process never reads its own windows (the certificate forbids self-reads). -/
theorem reads_not_own {d : Design2} {rank : Nat → Nat} (hr : AcyclicBy d rank) {p : Nat}
    {t : Lhs2} {e : Expr2} (hp : d.processes[p]? = some (.assign t e)) :
    ∀ r ∈ e.reads, ∀ wn ∈ t.wins d, r.overlaps wn = false := by
  intro r hr' wn hwn
  cases hov : r.overlaps wn with
  | false => rfl
  | true => exact absurd (hr p p t e t e wn hp hp hwn ⟨r, hr', hov⟩) (Nat.lt_irrefl _)

/-- **The settle invariant is preserved by every step.** -/
theorem Settles.step_inv {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    {c c' : Config} (hS : Settles E d rank) (hI : SettleInv E d c) (h : step E ch c = .next c') :
    SettleInv E d c' := by
  obtain ⟨p, rest, t, e, v, hch, hp, hv, hview, hT, hact⟩ := hS.step_next_spec hI h
  have hperm := ch.choose_perm c.k c.active
  rw [hch] at hperm
  have hs := hS.shape hI.typed
  have hr := hS.acyclicBy
  obtain ⟨_, _, _, _, hnd'⟩ := step_legal hI.nodup h
  refine ⟨hT, hnd', ?_, ?_⟩
  · intro q hq
    rw [hact] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hI.range q (hperm.mem_iff.mp (List.mem_cons_of_mem _ hq))
    · exact (Elab.mem_triggered (List.mem_filter.mp hq).1).1
  · intro q hq
    have hq_rest : q ∉ rest := fun h' => hq (by rw [hact]; exact List.mem_append_left _ h')
    by_cases hqp : q = p
    · -- the process that just ran satisfies its equation
      subst hqp
      intro tq eq n lo w off hpq hm
      rw [hp] at hpq
      simp only [Option.some.injEq, Process2.assign.injEq] at hpq
      obtain ⟨rfl, rfl⟩ := hpq
      obtain ⟨u, hu, hue⟩ := hS.comb.combWrite_readBack hs hp v hm
      refine ⟨u, v, by rw [hview]; exact hu, ?_, hue⟩
      rw [hview, ← hv]
      exact (evalPure2_congr_reads fun r hr' =>
        ReadWin.agree_combWrite fun wn hwn => reads_not_own hr hp r hr' wn hwn).symm
    · -- any other idle process: not triggered, so its reads and windows are unchanged
      have hqa : q ∉ c.active := fun h' => by
        rcases List.mem_cons.mp (hperm.mem_iff.mpr h') with h'' | h''
        · exact hqp h''
        · exact hq_rest h''
      have hold := hI.eqs q hqa
      intro tq eq n lo w off hpq hm
      obtain ⟨old, v0, hlo, hv0, hext⟩ := hold tq eq n lo w off hpq hm
      have hqn : q < E.procs.size := hS.lt_of_proc hpq
      have hnt : q ∉ E.triggered (E.view c.store) (E.view c'.store) := fun h' => hq (by
        rw [hact]
        exact List.mem_append_right _ (List.mem_filter.mpr ⟨h', by simpa using hq_rest⟩))
      have hreads := Elab.not_triggered hqn hnt
      -- the window `(n, lo, w)` of `q` is disjoint from every window of `p`
      have hwin : (ReadWin.win n lo w).agree (E.view c.store) (E.view c'.store) := by
        rw [hview]
        refine ReadWin.agree_combWrite fun wn hwn => ?_
        exact hS.comb.disjoint q p (n, lo, w) wn hqp ⟨tq, eq, hpq, Win.mem_of_mem_placed hm⟩
          ⟨t, e, hp, hwn⟩
      simp only [ReadWin.agree, hlo, Option.map_some] at hwin
      cases hlo' : SvState.lookup (E.view c'.store) n with
      | none => rw [hlo'] at hwin; cases hwin
      | some old' =>
          rw [hlo'] at hwin
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwin
          refine ⟨old', v0, rfl, ?_, hwin.2.symm.trans hext⟩
          rw [← hv0]
          exact (evalPure2_congr_reads fun r hr' =>
            hreads r (hS.complete q tq eq hpq r hr')).symm

/-- Every step is a frame step. -/
theorem Settles.step_frame {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    {c c' : Config} (hS : Settles E d rank) (hI : SettleInv E d c) (h : step E ch c = .next c') :
    Frame d (E.view c.store) (E.view c'.store) := by
  obtain ⟨p, rest, t, e, v, -, hp, -, hview, -⟩ := hS.step_next_spec hI h
  rw [hview]
  exact Frame.combWrite hp v

theorem Settles.steps_inv {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    (hS : Settles E d rank) {c c' : Config} (h : Steps E ch c c') :
    SettleInv E d c → SettleInv E d c' := by
  induction h with
  | refl => exact id
  | head hs _ ih => exact fun hI => ih (hS.step_inv hI hs)

theorem Settles.steps_frame {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    (hS : Settles E d rank) {c c' : Config} (h : Steps E ch c c') :
    SettleInv E d c → Frame d (E.view c.store) (E.view c'.store) := by
  induction h with
  | refl c => exact fun _ => Frame.refl _
  | head hs _ ih => exact fun hI => (hS.step_frame hI hs).trans (ih (hS.step_inv hI hs))

/-! ## The rank measure -/

/-- Weighted size of a ready list. -/
def wsum (w : ProcId → Nat) : List ProcId → Nat
  | [] => 0
  | q :: qs => w q + wsum w qs

theorem wsum_append (w : ProcId → Nat) : ∀ l₁ l₂, wsum w (l₁ ++ l₂) = wsum w l₁ + wsum w l₂
  | [], _ => by simp [wsum]
  | q :: qs, l₂ => by simp only [List.cons_append, wsum, wsum_append w qs l₂, Nat.add_assoc]

theorem wsum_perm (w : ProcId → Nat) {l₁ l₂ : List ProcId} (h : l₁.Perm l₂) :
    wsum w l₁ = wsum w l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [wsum, ih]
  | swap x y l => simp only [wsum]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem wsum_le (w : ProcId → Nat) (B : Nat) :
    ∀ l : List ProcId, (∀ q ∈ l, w q ≤ B) → wsum w l ≤ l.length * B
  | [], _ => by simp [wsum]
  | q :: qs, h => by
      have h1 := h q (List.mem_cons_self ..)
      have h2 := wsum_le w B qs fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [wsum, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (qs.length * B)]
      exact Nat.add_le_add h1 h2

/-- **The explicit rank measure**: each ready process weighs
`(N+1)^(N − rank q)`, so a lower rank weighs more than all `N` processes of
higher rank together. -/
def potential (N : Nat) (rank : Nat → Nat) (c : Config) : Nat :=
  wsum (fun q => (N + 1) ^ (N - rank q)) c.active

/-- At most `N` processes, all of rank above `r`, weigh less than one of rank `r`. -/
theorem wsum_higher_lt {N r : Nat} (hr : r < N) {rank : Nat → Nat} {l : List ProcId}
    (hnd : l.Nodup) (hsub : ∀ q ∈ l, q < N) (hrk : ∀ q ∈ l, r < rank q) :
    wsum (fun q => (N + 1) ^ (N - rank q)) l < (N + 1) ^ (N - r) := by
  have hB : 0 < (N + 1) ^ (N - r - 1) := Nat.pow_pos (Nat.succ_pos N)
  have hterm : ∀ q ∈ l, (N + 1) ^ (N - rank q) ≤ (N + 1) ^ (N - r - 1) := fun q hq =>
    Nat.pow_le_pow_right (Nat.succ_pos N) (by have := hrk q hq; omega)
  have hsum := wsum_le _ _ l hterm
  have hlen : l.length ≤ N := by
    have := hnd.length_le_of_subset (l₂ := List.range N) fun q hq => List.mem_range.mpr (hsub q hq)
    rwa [List.length_range] at this
  have hk : N - r = (N - r - 1) + 1 := by omega
  rw [hk, Nat.pow_succ, Nat.mul_comm, Nat.add_mul, Nat.one_mul]
  exact Nat.lt_of_le_of_lt (Nat.le_trans hsum (Nat.mul_le_mul_right _ hlen))
    (Nat.lt_add_of_pos_right hB)

/-- **Every step strictly decreases the measure** and keeps the invariant. A
triggered process senses a bit the running process wrote, so it ranks
strictly higher. -/
theorem Settles.step_decreases {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    {c : Config} (hS : Settles E d rank) (hI : SettleInv E d c) {p : ProcId} {rest : List ProcId}
    (hch : ch.choose c.k c.active = p :: rest) :
    ∃ c', step E ch c = .next c' ∧ SettleInv E d c' ∧
      potential E.procs.size rank c' < potential E.procs.size rank c := by
  obtain ⟨t, e, v, hp, hv, s', hview, hT, hstep⟩ := hS.step_cons hI hch
  refine ⟨_, hstep, hS.step_inv hI hstep, ?_⟩
  have hperm := ch.choose_perm c.k c.active
  rw [hch] at hperm
  have hpn : p < E.procs.size := hS.lt_of_proc hp
  -- every newly ready process has a strictly higher rank than `p`
  have hrk : ∀ q ∈ (E.triggered (E.view c.store) (E.view s')).filter (fun q => decide (q ∉ rest)),
      rank p < rank q := by
    intro q hq
    obtain ⟨-, r, hr', hna⟩ := Elab.mem_triggered (List.mem_filter.mp hq).1
    rw [hview] at hna
    have hex : ∃ wn ∈ t.wins d, r.overlaps wn = true := by
      refine Classical.byContradiction fun hno => hna (ReadWin.agree_combWrite fun wn hwn => ?_)
      cases hov : r.overlaps wn with
      | false => rfl
      | true => exact (hno ⟨wn, hwn, hov⟩).elim
    obtain ⟨wn, hwn, hov⟩ := hex
    exact hS.ranked p q t e hp r hr' wn hwn hov
  have hlt := wsum_higher_lt (hS.bound p hpn) (rank := rank)
    (l := (E.triggered (E.view c.store) (E.view s')).filter (fun q => decide (q ∉ rest)))
    ((List.nodup_range.filter _).filter _)
    (fun q hq => (Elab.mem_triggered (List.mem_filter.mp hq).1).1) hrk
  simp only [potential]
  rw [← wsum_perm (fun q => (E.procs.size + 1) ^ (E.procs.size - rank q)) hperm, wsum_append]
  simp only [wsum]
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hlt _) (Nat.le_of_eq (Nat.add_comm _ _))

/-! ## The slot closes, under every legal schedule -/

/-- The executor closes the slot within any budget above the measure. -/
theorem Settles.exec_closes_of_lt {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (ch : Choice) : ∀ (m : Nat) (c : Config),
      potential E.procs.size rank c < m → SettleInv E d c → ∃ c', exec E ch m c = .closed c'
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, c, hm, hI => by
      cases hch : ch.choose c.k c.active with
      | nil =>
          refine ⟨c, ?_⟩
          simp only [exec, step, hch]
      | cons p rest =>
          obtain ⟨c₁, hstep, hI₁, hlt⟩ := hS.step_decreases hI hch
          obtain ⟨c', hc'⟩ := hS.exec_closes_of_lt ch m c₁ (by omega) hI₁
          exact ⟨c', by simp only [exec, hstep]; exact hc'⟩

/-- **Every legal schedule closes the slot within `potential + 1` steps.** -/
theorem Settles.exec_closes {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (ch : Choice) {c : Config} (hI : SettleInv E d c) :
    ∃ c', exec E ch (potential E.procs.size rank c + 1) c = .closed c' :=
  hS.exec_closes_of_lt ch _ c (Nat.lt_succ_self _) hI

/-- **The slot closes** under every legal schedule, and the invariant holds there. -/
theorem Settles.slot_closes {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (ch : Choice) {c : Config} (hI : SettleInv E d c) :
    ∃ c', SlotCloses E ch c c' ∧ SettleInv E d c' := by
  obtain ⟨c', hc'⟩ := hS.exec_closes ch hI
  have hcl := exec_sound hc'
  exact ⟨c', hcl, hS.steps_inv hcl.1 hI⟩

/-- A closed slot has drained the Active region. -/
theorem active_nil_of_closed {E : Elab} {ch : Choice} {c : Config}
    (h : step E ch c = .slotClosed c) : c.active = [] := by
  have hperm := ch.choose_perm c.k c.active
  cases hch : ch.choose c.k c.active with
  | nil =>
      rw [hch] at hperm
      exact List.perm_nil.mp hperm.symm
  | cons p rest =>
      simp only [step, hch] at h
      split at h <;> simp at h

/-- **The closed store solves `d`'s equations** and keeps every undriven bit. -/
theorem Settles.slotCloses_combEqs {E : Elab} {d : Design2} {rank : Nat → Nat} {ch : Choice}
    {c c' : Config} (hS : Settles E d rank) (hI : SettleInv E d c) (h : SlotCloses E ch c c') :
    CombEqs d (E.view c'.store) ∧ StateShape d (E.view c'.store) ∧
      Frame d (E.view c.store) (E.view c'.store) := by
  have hI' := hS.steps_inv h.1 hI
  have hnil := active_nil_of_closed h.2
  refine ⟨?_, hS.shape hI'.typed, hS.steps_frame h.1 hI⟩
  intro i
  exact hI'.eqs i (by rw [hnil]; exact List.not_mem_nil)

/-! ## Uniqueness under the rank -/

/-- **The solution is unique under the rank**: two shaped solutions of the
equations that agree on the undriven bits (and widths) are equal. The rank
induction of `CombPassSeq.combAgreeLow`, without passes. -/
theorem combEqs_unique {d : Design2} (hd : CombDesign d) (ha : Acyclic d) {st st' : SvState}
    (hs : StateShape d st) (hs' : StateShape d st') (he : CombEqs d st) (he' : CombEqs d st')
    (hf : Frame d st st') : st = st' := by
  obtain ⟨rank, hr, hlt⟩ := ha.exists_rank_lt
  have key : ∀ r, CombAgreeLow d rank r st st' := by
    intro r
    induction r with
    | zero =>
        exact ⟨hf.width, fun x b hlow => hf.undriven x b fun ⟨j, wn, hW, hov⟩ =>
          Nat.not_lt_zero _ (hlow j wn hW hov)⟩
    | succ r ih =>
        refine ⟨hf.width, fun x b hlow => ?_⟩
        by_cases hdrv : ∃ j wn, d.Writes j wn ∧ (ReadWin.win x b 1).overlaps wn = true
        · obtain ⟨j, ⟨nj, loj, wj⟩, hWj, hov⟩ := hdrv
          have hrj : rank j < r + 1 := hlow j _ hWj hov
          obtain ⟨tj, ej, hpj, hwj⟩ := hWj
          obtain ⟨offj, hoff⟩ := Win.exists_mem_placed hwj
          rw [ReadWin.overlaps_win_one] at hov
          obtain ⟨rfl, hb₁, hb₂⟩ := hov
          obtain ⟨u, v, hu, hv, hue⟩ := he j tj ej x loj wj offj hpj hoff
          obtain ⟨u', v', hu', hv', hue'⟩ := he' j tj ej x loj wj offj hpj hoff
          have hvv : v = v' := by
            have := evalPure2_eq_of_combAgreeLow hr hpj (ih.mono (Nat.le_of_lt_succ hrj))
            rw [hv, hv'] at this
            cases this
            rfl
          subst hvv
          have huw : u.width = u'.width := by
            have := hf.width x
            rw [hu, hu'] at this
            simpa using this
          exact agree_bit_of_extract hu hu' huw (hue.trans hue'.symm) hb₁ hb₂
        · exact hf.undriven x b hdrv
  exact StateShape.eq_of_agree_bits hd hs hs' fun x b =>
    (key d.processes.size).2 x b fun j _ hW _ => hlt j (lt_of_writes hW)

/-- **Schedule independence**: any two legal schedules close the slot at the same
store (its view; the view determines every declared variable). -/
theorem Settles.schedule_independent {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) {c c₁ c₂ : Config} {ch₁ ch₂ : Choice} (hI : SettleInv E d c)
    (h₁ : SlotCloses E ch₁ c c₁) (h₂ : SlotCloses E ch₂ c c₂) :
    E.view c₁.store = E.view c₂.store := by
  obtain ⟨he₁, hs₁, hf₁⟩ := hS.slotCloses_combEqs hI h₁
  obtain ⟨he₂, hs₂, hf₂⟩ := hS.slotCloses_combEqs hI h₂
  exact combEqs_unique hS.comb hS.acyclic hs₁ hs₂ he₁ he₂ (hf₁.symm.trans hf₂)

/-- **R-COMB-0, generic** (derived from E). From every configuration
satisfying the settle invariant, under every legal schedule, the slot closes;
the closed store solves `d`'s equations, keeps the undriven bits, and is the
ONLY shaped solution that does. -/
theorem Settles.rcomb {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (ch : Choice) {c : Config} (hI : SettleInv E d c) :
    ∃ c', SlotCloses E ch c c' ∧ CombEqs d (E.view c'.store) ∧
      Frame d (E.view c.store) (E.view c'.store) ∧
      ∀ st, StateShape d st → CombEqs d st → Frame d (E.view c.store) st → st = E.view c'.store := by
  obtain ⟨c', hcl, -⟩ := hS.slot_closes ch hI
  obtain ⟨he, hs, hf⟩ := hS.slotCloses_combEqs hI hcl
  exact ⟨c', hcl, he, hf, fun st hst hest hfst =>
    combEqs_unique hS.comb hS.acyclic hst hs hest he (hfst.symm.trans hf)⟩

/-! ## Agreement with `combSettle2` (transport, first slice) -/

theorem Frame.of_combPass2 {d : Design2} (hd : CombDesign d) {f : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d f st is = .ok st') : Frame d st st' :=
  ⟨fun x => combPass2_width hd hs h x, fun _ _ hu => (combPass2_frame hd hs h).2 _ fun i _ wn hW =>
    Bool.eq_false_iff.mpr fun hov => hu ⟨i, wn, hW, hov⟩⟩

/-- `combSettle2` keeps every undriven bit (bit granularity; `combSettle2_eqs`
states it per signal). -/
theorem combSettle2_frame {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle} :
    ∀ {fuel : Nat} {st S : SvState} {k k' : Nat}, StateShape d st →
      combSettle2 d σ fuel st k = .ok (S, k') → Frame d st S
  | 0, _, _, _, _, _, h => by simp [combSettle2] at h
  | f + 1, st, S, k, k', hs, h => by
      simp only [combSettle2, Res.bind_eq_ok] at h
      obtain ⟨st', hpass, hrest⟩ := h
      have hF := Frame.of_combPass2 hd hs hpass
      by_cases heq : (st' == st) = true
      · rw [if_pos heq] at hrest
        simp only [Res.ok.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, -⟩ := hrest
        exact hF
      · rw [if_neg heq] at hrest
        exact hF.trans (combSettle2_frame hd (combPass2_frame hd hs hpass).1 hrest)

/-- **E's closed store is `combSettle2 d`'s result** (fuel-free form): whenever
`combSettle2` on the equation design returns from the view of the slot's start
(any schedule, any fuel), it returns E's closed view. -/
theorem Settles.closed_eq_combSettle2 {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) {ch : Choice} {c c' : Config} (hI : SettleInv E d c)
    (h : SlotCloses E ch c c') {σ : ScheduleOracle} {fuel k : Nat} {S : SvState} {k' : Nat}
    (hS2 : combSettle2 d σ fuel (E.view c.store) k = .ok (S, k')) :
    E.view c'.store = S := by
  obtain ⟨heqs, hsh, hF⟩ := hS.slotCloses_combEqs hI h
  have hs0 := hS.shape hI.typed
  obtain ⟨heqS, hshS, -⟩ := combSettle2_eqs hS.comb hs0 hS2
  exact combEqs_unique hS.comb hS.acyclic hsh hshS heqs heqS (hF.symm.trans
    (combSettle2_frame hS.comb hs0 hS2))

/-- **Agreement with `combSettle2 d`**: from any typed store with every process
ready, for every legal Choice and every `ScheduleOracle`, E closes the slot,
`combSettle2 d` returns at its explicit fuel, and the two agree. -/
theorem Settles.rcomb_combSettle2 {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (ch : Choice) (σ : ScheduleOracle) {s : Store} (hT : E.Typed s)
    (k fuel : Nat) (hf : d.settleFuel ≤ fuel) :
    ∃ c' S k', SlotCloses E ch (Config.init E s) c' ∧
      combSettle2 d σ fuel (E.view s) k = .ok (S, k') ∧ E.view c'.store = S := by
  have hI := SettleInv.init hS.size hT (d := d)
  obtain ⟨c', hcl, -⟩ := hS.slot_closes ch hI
  obtain ⟨S, k', hS2⟩ := combSettle2_terminates_of_le hS.comb hS.acyclic hf σ (E.view s) k
    (hS.shape hT)
  exact ⟨c', S, k', hcl, hS2, hS.closed_eq_combSettle2 hI hcl hS2⟩

/-! ## The assign-only instance (gate G-A) -/

/-- **An assign-only design is its own equation design.** -/
theorem Settles.ofProfile0 {E : Elab} (hP : Profile0 E) {rank : Nat → Nat}
    (hr : AcyclicBy E.toDesign2 rank) (hR : ∀ i, i < E.procs.size → rank i < E.procs.size) :
    Settles E E.toDesign2 rank where
  comb := hP.comb
  decls := rfl
  size := E.size_toDesign2
  four := hP.four
  act := fun s p hT hpn => by
    obtain ⟨t, e, ws, hp, hws⟩ := hP.comb.writes_of_lt (by rwa [Elab.size_toDesign2])
    have hs := Elab.shape_view hP.comb hT
    obtain ⟨v, hv⟩ := hP.comb.evalPure2_ok hs hp
    refine ⟨t, e, v, E.writeWins s (v.resizeU (Win.sumWidth ws)) (Win.placed ws), hp, hv,
      activate_assign (Elab.proc_assign_iff.mp hp) hws hv, ?_, hT.writeWins _ _⟩
    rw [Elab.view_writeWins hP.four _ _ hT, combWrite, Lhs2.wins_of_windows? hws]
  complete := fun q t e hp r hr' => by rw [Elab.sens_of_assign hp]; exact hr'
  ranked := fun p q t e hp r hr' w hw hov => by
    cases hq : E.procs[q]? with
    | none => simp [Elab.sens, hq] at hr'
    | some pq =>
        cases pq with
        | assign tq eq =>
            have hq' : E.toDesign2.processes[q]? = some (.assign tq eq) :=
              Elab.proc_assign_iff.mpr hq
            rw [Elab.sens_of_assign hq'] at hr'
            exact hr q p tq eq t e w hq' hp hw ⟨r, hr', hov⟩
        | comb body =>
            exfalso
            have hq' : E.toDesign2.processes[q]? = some (.alwaysComb body) := by
              simp [Elab.toDesign2, hq, Proc0.toProcess2]
            obtain ⟨_, _, _, h, -⟩ := hP.comb.assign q _ hq'
            cases h
  bound := hR

/-- Compress any certificate of an assign-only design into a `Settles`. -/
theorem Settles.ofProfile0' {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2) :
    ∃ rank, AcyclicBy E.toDesign2 rank ∧ Settles E E.toDesign2 rank := by
  obtain ⟨rank, hr, hR⟩ := ha.exists_rank_lt
  rw [Elab.size_toDesign2] at hR
  exact ⟨rank, hr, Settles.ofProfile0 hP hr hR⟩

/-- The step invariant, assign-only. -/
theorem step_inv {E : Elab} {ch : Choice} {c c' : Config} (hP : Profile0 E) {rank : Nat → Nat}
    (hr : AcyclicBy E.toDesign2 rank) (hI : SettleInv E E.toDesign2 c)
    (h : step E ch c = .next c') : SettleInv E E.toDesign2 c' := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ⟨rank, hr⟩
  exact hS.step_inv hI h

/-- **Every legal process-atomic schedule closes the slot, within an explicit
bound** (assign-only): for a compressed rank, the executor at budget
`potential + 1` closes it, for every Choice. -/
theorem exec_closes {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2) {c : Config}
    (hI : SettleInv E E.toDesign2 c) : ∃ rank, AcyclicBy E.toDesign2 rank ∧
      ∀ ch : Choice, ∃ c', exec E ch (potential E.procs.size rank c + 1) c = .closed c' := by
  obtain ⟨rank, hr, hS⟩ := Settles.ofProfile0' hP ha
  exact ⟨rank, hr, fun ch => hS.exec_closes ch hI⟩

/-- **The slot closes** under every legal schedule (assign-only). -/
theorem slot_closes {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2) (ch : Choice)
    {c : Config} (hI : SettleInv E E.toDesign2 c) :
    ∃ c', SlotCloses E ch c c' ∧ SettleInv E E.toDesign2 c' := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ha
  exact hS.slot_closes ch hI

/-- **The closed store solves the equations** (assign-only). -/
theorem SlotCloses.combEqs {E : Elab} {ch : Choice} {c c' : Config} (hP : Profile0 E)
    {rank : Nat → Nat} (hr : AcyclicBy E.toDesign2 rank) (hI : SettleInv E E.toDesign2 c)
    (h : SlotCloses E ch c c') :
    CombEqs E.toDesign2 (E.view c'.store) ∧ StateShape E.toDesign2 (E.view c'.store) ∧
      Frame E.toDesign2 (E.view c.store) (E.view c'.store) := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ⟨rank, hr⟩
  exact hS.slotCloses_combEqs hI h

/-- **Schedule independence** (assign-only). -/
theorem rcomb0_schedule_independent {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2)
    {c c₁ c₂ : Config} {ch₁ ch₂ : Choice} (hI : SettleInv E E.toDesign2 c)
    (h₁ : SlotCloses E ch₁ c c₁) (h₂ : SlotCloses E ch₂ c c₂) :
    E.view c₁.store = E.view c₂.store := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ha
  exact hS.schedule_independent hI h₁ h₂

/-- **R-COMB-0, assign-only** (derived from E). -/
theorem rcomb0 {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2) (ch : Choice) {c : Config}
    (hI : SettleInv E E.toDesign2 c) :
    ∃ c', SlotCloses E ch c c' ∧ CombEqs E.toDesign2 (E.view c'.store) ∧
      Frame E.toDesign2 (E.view c.store) (E.view c'.store) ∧
      ∀ st, StateShape E.toDesign2 st → CombEqs E.toDesign2 st →
        Frame E.toDesign2 (E.view c.store) st → st = E.view c'.store := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ha
  exact hS.rcomb ch hI

/-- **E's closed store is `combSettle2`'s result** (assign-only, fuel-free form). -/
theorem closed_eq_combSettle2 {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2)
    {ch : Choice} {c c' : Config} (hI : SettleInv E E.toDesign2 c) (h : SlotCloses E ch c c')
    {σ : ScheduleOracle} {fuel k : Nat} {S : SvState} {k' : Nat}
    (hS2 : combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (S, k')) :
    E.view c'.store = S := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ha
  exact hS.closed_eq_combSettle2 hI h hS2

/-- **Agreement with `combSettle2`** (assign-only; transport theorem, first
slice). -/
theorem rcomb0_combSettle2 {E : Elab} (hP : Profile0 E) (ha : Acyclic E.toDesign2) (ch : Choice)
    (σ : ScheduleOracle) {s : Store} (hT : E.Typed s) (k fuel : Nat)
    (hf : E.toDesign2.settleFuel ≤ fuel) :
    ∃ c' S k', SlotCloses E ch (Config.init E s) c' ∧
      combSettle2 E.toDesign2 σ fuel (E.view s) k = .ok (S, k') ∧ E.view c'.store = S := by
  obtain ⟨_, -, hS⟩ := Settles.ofProfile0' hP ha
  exact hS.rcomb_combSettle2 ch σ hT k fuel hf

/-! ## Negative cases: the rank hypothesis fails -/

namespace Core0Smoke

/-- `assign y = ~y` reads its own window: no rank exists. (`Core0.lean`'s
`#guard`s show it never closes the slot.) -/
theorem osc_not_acyclic : ¬ Acyclic osc.toDesign2 := by
  rintro ⟨rank, h⟩
  have hp : osc.toDesign2.processes[0]? = some (.assign (.ident "y") (.unary .bnot (.ident "y"))) := by
    simp [Elab.toDesign2, osc, Proc0.toProcess2]
  have hw : ("y", 0, 1) ∈ (Lhs2.ident "y").wins osc.toDesign2 := by
    simp [Lhs2.wins_ident, Design2.declWidth, Elab.toDesign2, osc]
  exact Nat.lt_irrefl _
    (h 0 0 _ _ _ _ _ hp hp hw ⟨.whole "y", by simp [Expr2.reads], by simp [ReadWin.overlaps]⟩)

/-- `assign a = b; assign b = a` is a cycle: no rank exists. (`Core0.lean`'s
`#guard`s show two schedules closing it at different stores.) -/
theorem swap_not_acyclic : ¬ Acyclic swap.toDesign2 := by
  rintro ⟨rank, h⟩
  have hp0 : swap.toDesign2.processes[0]? = some (.assign (.ident "a") (.ident "b")) := by
    simp [Elab.toDesign2, swap, Proc0.toProcess2]
  have hp1 : swap.toDesign2.processes[1]? = some (.assign (.ident "b") (.ident "a")) := by
    simp [Elab.toDesign2, swap, Proc0.toProcess2]
  have hwa : ("a", 0, 1) ∈ (Lhs2.ident "a").wins swap.toDesign2 := by
    simp [Lhs2.wins_ident, Design2.declWidth, Elab.toDesign2, swap]
  have hwb : ("b", 0, 1) ∈ (Lhs2.ident "b").wins swap.toDesign2 := by
    simp [Lhs2.wins_ident, Design2.declWidth, Elab.toDesign2, swap]
  have h01 := h 0 1 _ _ _ _ _ hp0 hp1 hwb
    ⟨.whole "b", by simp [Expr2.reads], by simp [ReadWin.overlaps]⟩
  have h10 := h 1 0 _ _ _ _ _ hp1 hp0 hwa
    ⟨.whole "a", by simp [Expr2.reads], by simp [ReadWin.overlaps]⟩
  omega

end Core0Smoke

/-! ## Axioms -/

#print axioms exec_sound
#print axioms step_legal
#print axioms Settles.step_inv
#print axioms Settles.step_decreases
#print axioms Settles.exec_closes
#print axioms Settles.slot_closes
#print axioms Settles.slotCloses_combEqs
#print axioms Settles.schedule_independent
#print axioms Settles.rcomb
#print axioms Settles.closed_eq_combSettle2
#print axioms Settles.rcomb_combSettle2
#print axioms Settles.ofProfile0
#print axioms combEqs_unique
#print axioms step_inv
#print axioms exec_closes
#print axioms slot_closes
#print axioms SlotCloses.combEqs
#print axioms rcomb0
#print axioms rcomb0_schedule_independent
#print axioms closed_eq_combSettle2
#print axioms rcomb0_combSettle2
#print axioms Core0Smoke.osc_not_acyclic
#print axioms Core0Smoke.swap_not_acyclic

end LeanModels.Sv.Kernel
