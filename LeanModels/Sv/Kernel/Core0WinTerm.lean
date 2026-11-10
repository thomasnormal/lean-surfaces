import LeanModels.Sv.Kernel.Core0Win

/-!
# D-X1f2: `combSettle2` terminates on window-acyclic designs (`LeanModels.Sv.Kernel`)

The termination half of R-COMB-1's `rcomb1` (X1-NOTE §12, debt D-X1f). **Status: a `run2` theorem
under E's hypotheses**: it is about `combSettle2`, with E's window rank (`WSettles`, `Core0Win.lean`)
as hypothesis, so it is not derived from E. Imported by no existing module.

`combSettle2_terminates_win`: under `WSettles E dW (winOwn ps) rank` (the window rank of the
per-window lowering `dW`), `combSettle2` on the design itself returns from every shaped state,
under every process-atomic legal schedule. The process-level lowering `d'` may be cyclic (`ibexLow_not_acyclic`).

Route (the plan accepted for D-X1f2):
1. One process of `d'` and the equations it owns in `dW` write the same state: both are
   `WriteRel dW (winOwn ps p)` of the start state (`run_writeRel`, `seq_run`), and that relation
   has one shaped solution (`WriteRel.unique`). So a pass of `d'` is a pass of `dW` over the
   owned equations in the same process order (`pass_win`).
2. The settle sequence of `d'` is therefore a `CombPassSeq` of `dW`, which the window rank makes
   constant from pass `|dW|` on (`CombPassSeq.stable`); `combSettle2_ok_of_stable` closes the
   settle on `d'`.
3. `CombSim.of_lowerComb'` carries the settle from `d'` to the design.

Fixture: `Core0Smoke.ibex_terminates` (MEASURED before: `combSettle2 ibex.toDesign2` completes
from fuel 8 under both orders; now proved for every process-atomic legal schedule and every shaped start).
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv.Comb2Term

set_option autoImplicit false

/-! ## `WriteRel`: one shaped solution, and one more equation -/

theorem WriteRel.nil (d : Design2) (st : SvState) : WriteRel d [] st st :=
  ⟨fun _ => rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => ReadWin.agree_refl _ _⟩

/-- **A write relation has one shaped solution.** -/
theorem WriteRel.unique {d : Design2} (hd : CombDesign d) {js : List Nat} {st₀ r r' : SvState}
    (h : WriteRel d js st₀ r) (h' : WriteRel d js st₀ r') (hs : StateShape d r)
    (hs' : StateShape d r') : r = r' := by
  refine StateShape.eq_of_agree_bits hd hs hs' fun n b => ?_
  by_cases hc : ∃ j ∈ js, ∃ wn, d.Writes j wn ∧ (ReadWin.win n b 1).overlaps wn = true
  · obtain ⟨j, hj, ⟨m, lo, w⟩, ⟨t, e, hp, hwn⟩, hov⟩ := hc
    rw [ReadWin.overlaps_win_one] at hov
    obtain ⟨rfl, hb₁, hb₂⟩ := hov
    obtain ⟨off, hoff⟩ := Win.exists_mem_placed hwn
    obtain ⟨u, v, hu, hv, he⟩ := h.eqs j hj t e n lo w off hp hoff
    obtain ⟨u', v', hu', hv', he'⟩ := h'.eqs j hj t e n lo w off hp hoff
    rw [hv, Res.ok.injEq] at hv'
    subst hv'
    have hw : u.width = u'.width := by
      have := (h.width n).symm.trans (h'.width n)
      rw [hu, hu'] at this
      simpa using this
    exact agree_bit_of_extract hu hu' hw (he.trans he'.symm) hb₁ hb₂
  · have hout : ∀ j ∈ js, ∀ wn, d.Writes j wn → (ReadWin.win n b 1).overlaps wn = false :=
      fun j hj wn hW => Bool.eq_false_iff.mpr fun hov => hc ⟨j, hj, wn, hW, hov⟩
    exact ReadWin.agree_trans (ReadWin.agree_symm (h.out n b hout)) (h'.out n b hout)

/-- **One more equation**: an assign run after the equations `js`, its right-hand side reading
the start state's value, extends the write relation. -/
theorem WriteRel.snoc {d : Design2} (hd : CombDesign d) {js : List Nat} {st₀ m : SvState}
    (hR : WriteRel d js st₀ m) (hs : StateShape d m) {j : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[j]? = some (.assign t e)) (hj : j ∉ js) {v : LVec}
    (hv : evalPure2 st₀ e = .ok v) : WriteRel d (js ++ [j]) st₀ (combWrite d m t v) where
  width x := (hR.width x).trans (SvState.writeWins_width x).symm
  eqs i hi := by
    intro t' e' n lo w off hp' hm
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨old, v', hold, hv', hext⟩ := hR.eqs i hi t' e' n lo w off hp' hm
      have hag : (ReadWin.win n lo w).agree m (combWrite d m t v) :=
        ReadWin.agree_combWrite fun wn hwn =>
          hd.disjoint i j _ wn (fun h => hj (h ▸ hi)) ⟨t', e', hp', Win.mem_of_mem_placed hm⟩
            ⟨t, e, hp, hwn⟩
      simp only [ReadWin.agree, hold, Option.map_some] at hag
      cases hc : SvState.lookup (combWrite d m t v) n with
      | none => rw [hc] at hag; cases hag
      | some old' =>
          rw [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hag
          exact ⟨old', v', rfl, hv', hag.2 ▸ hext⟩
    · rw [List.mem_singleton] at hi
      subst hi
      rw [hp, Option.some.injEq, Process2.assign.injEq] at hp'
      obtain ⟨rfl, rfl⟩ := hp'
      obtain ⟨u, hu, hue⟩ := hd.combWrite_readBack hs hp v hm
      exact ⟨u, v, hu, hv, hue⟩
  out n b h := ReadWin.agree_trans (hR.out n b fun i hi => h i (List.mem_append_left _ hi))
    (ReadWin.agree_combWrite fun wn hwn => h j (by simp) wn ⟨t, e, hp, hwn⟩)

/-- **Running a group of equations in sequence** (no equation of the group reads a window of the
group) writes every equation of the group at its start-state value. -/
theorem seq_run {d : Design2} (hd : CombDesign d) {own : List Nat}
    (hown : ∀ j ∈ own, ∃ t e, d.processes[j]? = some (.assign t e))
    (hgrp : ∀ j ∈ own, ∀ j' ∈ own, ∀ t e, d.processes[j]? = some (.assign t e) →
      ∀ r ∈ e.reads, ∀ wn, d.Writes j' wn → r.overlaps wn = false) {st₀ : SvState} :
    ∀ (L done : List Nat) (m : SvState), (done ++ L).Nodup → (∀ j ∈ done ++ L, j ∈ own) →
      StateShape d m → WriteRel d done st₀ m →
      ∃ f r, combPass2 d f m L = .ok r ∧ StateShape d r ∧ WriteRel d (done ++ L) st₀ r
  | [], done, m, _, _, hs, hR => ⟨0, m, rfl, hs, by simpa using hR⟩
  | j :: L, done, m, hnd, hmem, hs, hR => by
      have hjo := hmem j (by simp)
      obtain ⟨t, e, hp⟩ := hown j hjo
      obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hp
      have hv₀ : evalPure2 st₀ e = .ok v := by
        refine (evalPure2_congr_reads fun r hr => ?_).trans hv
        refine ReadWin.agree_of_bits hR.width fun n i hri => hR.out n i fun i' hi' wn hW =>
          Bool.eq_false_iff.mpr fun hov => ?_
        have := hgrp j hjo i' (hmem i' (List.mem_append_left _ hi')) t e hp r hr wn hW
        rw [ReadWin.overlaps_of_bit hri hov] at this
        cases this
      have hjd : j ∉ done := fun h => (List.nodup_append.mp hnd).2.2 j h j (by simp) rfl
      obtain ⟨f, r, hpass, hsr, hRr⟩ := seq_run hd hown hgrp L (done ++ [j]) _
        (by simpa using hnd) (by simpa using hmem) (hs.combWrite t v) (hR.snoc hd hs hp hjd hv₀)
      refine ⟨max f (e.size + 1), r, ?_, hsr, by simpa using hRr⟩
      rw [combPass2_cons_some hp, runCombProcess2_mono
        (runCombProcess2_assign_write hd hs hp (Nat.lt_succ_self _) hv) (by simp) _
        (Nat.le_max_right _ _), Res.ok_bind]
      exact combPass2_mono hpass (by simp) _ (Nat.le_max_left _ _)

/-! ## A process of the lowering and the equations it owns -/

/-- The equations process `p` owns are the per-window lowering of its process. -/
theorem winOwn_lowering {E : Elab} {ps : List (Nat × Process2)} (hw : E.toDesign2.lowerWin = some ps)
    {p : Nat} {pr : Process2} {g : List Process2} (hpr : E.toDesign2.processes[p]? = some pr)
    (hg : pr.lowerWin E.toDesign2 = some g) :
    (∀ j ∈ winOwn ps p, ∃ q ∈ g, (E.toDesign2.winDesign ps).processes[j]? = some q) ∧
    ∀ q ∈ g, ∃ j ∈ winOwn ps p, (E.toDesign2.winDesign ps).processes[j]? = some q := by
  constructor
  · intro j hj
    obtain ⟨q, hq⟩ := mem_winOwn.mp hj
    obtain ⟨pr', g', hpr', hg', hqg⟩ := (Design2.mem_lowerWin hw).mp (mem_of_getElem?' hq)
    rw [hpr, Option.some.injEq] at hpr'
    subst hpr'
    rw [hg, Option.some.injEq] at hg'
    subst hg'
    exact ⟨q, hqg, by rw [Design2.winDesign_proc, hq]; rfl⟩
  · intro q hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((Design2.mem_lowerWin hw).mpr ⟨pr, g, hpr, hg, hq⟩)
    exact ⟨j, mem_winOwn.mpr ⟨q, hj⟩, by rw [Design2.winDesign_proc, hj]; rfl⟩

/-- **A process of the lowering writes the equations it owns**, at the start state's values. -/
theorem run_writeRel {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps) (hdW : CombDesign (E.toDesign2.winDesign ps)) {p : Nat}
    {q : Process2} (hq : d'.processes[p]? = some q) {st r : SvState} (hs : StateShape d' st)
    {f : Nat} (h : runCombProcess2 f st q = .ok r) :
    StateShape d' r ∧ WriteRel (E.toDesign2.winDesign ps) (winOwn ps p) st r := by
  have hdecls : d'.decls = (E.toDesign2.winDesign ps).decls := (Design2.lowerComb_spec hl).2.1
  have hsW := shape_win_of_lower hl hw hs
  obtain ⟨pr, hpr, hlc⟩ := Design2.lowerComb_proc' hl hq
  obtain ⟨g, hg⟩ := Design2.lowerWin_total hw hpr
  obtain ⟨hown, hcov⟩ := winOwn_lowering hw hpr hg
  cases pr with
  | assign t e =>
      simp only [Process2.lowerComb, Option.some.injEq] at hlc
      subst hlc
      simp only [Process2.lowerWin, Option.some.injEq] at hg
      subst hg
      obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok hd' hs hq h
      refine ⟨hs.combWrite t v, ?_⟩
      have hcw : combWrite d' st t v = combWrite (E.toDesign2.winDesign ps) st t v := by
        simp only [combWrite, wins_congr_decls hdecls t]
      obtain ⟨j₀, hj₀, -⟩ := hcov _ (List.mem_singleton_self _)
      rw [hcw]
      exact WriteRel.ofCombWrite hdW hsW hv (fun j hj => by
        obtain ⟨q, hq', hjq⟩ := hown j hj
        rw [List.mem_singleton] at hq'
        rw [hjq, hq']) hj₀
  | alwaysComb body =>
      obtain ⟨S, hsym, -, rfl⟩ := Process2.lowerWin_alwaysComb hg
      obtain ⟨S', hsym', -, rfl⟩ := Process2.lowerComb_alwaysComb hlc
      rw [hsym, Option.some.injEq] at hsym'
      subst hsym'
      obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok (t := S.target) (e := S.rhs) hd' hs hq h
      refine ⟨hs.combWrite _ v, ?_⟩
      have hb : ∀ y ∈ E.toDesign2.symNames, ∃ v, SvState.lookup st y = some v := fun y hy =>
        hs.lookup_of_mem (by rw [hdecls]; simpa [Design2.symNames, Design2.winDesign] using hy)
      have hok : SymOk E.toDesign2 st S := SymOk.of_shape (Design2.lowerComb_spec hl).2.1 hq hs
      obtain ⟨⟨st'', nba⟩, hrun⟩ := (symExec_total hb body.fuelB).1 body [] S st [] hsym hok
        (SymRel.init st) (Nat.le_refl _)
      obtain ⟨-, hR⟩ := (symExec_sound body.fuelB).1 body [] S st [] st'' nba hsym hok
        (SymRel.init st) hrun
      exact WriteRel.ofSymRel hdW (SymRel.of_combWrite hd' hs hq hR hv) hsW
        (fun j hj => by
          obtain ⟨q, hq', hjq⟩ := hown j hj
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq'
          exact ⟨x, hx, hjq⟩)
        (fun x hx => hcov _
          (List.mem_map_of_mem (f := fun x : Win × Expr2 => Process2.assign x.1.lhs x.2) hx))
  | _ => simp [Process2.lowerWin] at hg

/-- **One process of the lowering is a pass of the equations it owns.** -/
theorem proc_pass {E : Elab} {d' : Design2} {ps : List (Nat × Process2)} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps)
    (hS : WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank) {p : Nat} {q : Process2}
    (hq : d'.processes[p]? = some q) {st r : SvState} (hs : StateShape d' st) {f : Nat}
    (h : runCombProcess2 f st q = .ok r) :
    StateShape d' r ∧ ∃ f', combPass2 (E.toDesign2.winDesign ps) f' st (winOwn ps p) = .ok r := by
  obtain ⟨hsr, hR⟩ := run_writeRel hl hd' hw hS.comb hq hs h
  have hown : ∀ j ∈ winOwn ps p, ∃ t e,
      (E.toDesign2.winDesign ps).processes[j]? = some (.assign t e) := by
    intro j hj
    obtain ⟨q', hq'⟩ := mem_winOwn.mp hj
    have hp' : (E.toDesign2.winDesign ps).processes[j]? = some q' := by
      rw [Design2.winDesign_proc, hq']; rfl
    obtain ⟨t, e, ws, rfl, -⟩ := hS.comb.assign j q' hp'
    exact ⟨t, e, hp'⟩
  have hnd : (winOwn ps p).Nodup := by unfold winOwn; exact (List.nodup_range (n := _)).filter _
  obtain ⟨f', r', hpass, hsr', hR'⟩ := seq_run hS.comb hown
    (fun j hj j' hj' t e hp => hS.group p j j' t e hj hj' hp) (winOwn ps p) [] st
    (by simpa using hnd) (by simp) (shape_win_of_lower hl hw hs) (WriteRel.nil _ st)
  rw [List.nil_append] at hR'
  refine ⟨hsr, f', ?_⟩
  rw [hpass, WriteRel.unique hS.comb hR' hR hsr' (shape_win_of_lower hl hw hsr)]

/-- **A pass of the lowering is a pass of the equation design**, over the equations each
process owns, in the same process order. -/
theorem pass_win {E : Elab} {d' : Design2} {ps : List (Nat × Process2)} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps)
    (hS : WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank) :
    ∀ (os : List Nat) (st r : SvState) (f : Nat), StateShape d' st →
      combPass2 d' f st os = .ok r →
      ∃ f', combPass2 (E.toDesign2.winDesign ps) f' st (os.flatMap (winOwn ps)) = .ok r
  | [], st, r, f, _, h => by
      simp only [combPass2, Res.ok.injEq] at h
      subst h
      exact ⟨0, rfl⟩
  | p :: os, st, r, f, hs, h => by
      cases hq : d'.processes[p]? with
      | none =>
          rw [combPass2_cons_none hq] at h
          have hnil : winOwn ps p = [] := List.eq_nil_iff_forall_not_mem.mpr fun j hj => by
            obtain ⟨q, hjq⟩ := mem_winOwn.mp hj
            obtain ⟨pr, g, hpr, -, -⟩ := (Design2.mem_lowerWin hw).mp (mem_of_getElem?' hjq)
            obtain ⟨q', -, hq'⟩ := Design2.lowerComb_proc hl hpr
            rw [hq] at hq'
            cases hq'
          rw [List.flatMap_cons, hnil, List.nil_append]
          exact pass_win hl hd' hw hS os st r f hs h
      | some q =>
          rw [combPass2_cons_some hq, Res.bind_eq_ok] at h
          obtain ⟨m, hm, hrest⟩ := h
          obtain ⟨hsm, f1, h1⟩ := proc_pass hl hd' hw hS hq hs hm
          obtain ⟨f2, h2⟩ := pass_win hl hd' hw hS os m r f hsm hrest
          refine ⟨max f1 f2, ?_⟩
          rw [List.flatMap_cons, combPass2_append,
            combPass2_mono h1 (by simp) _ (Nat.le_max_left _ _), Res.ok_bind]
          exact combPass2_mono h2 (by simp) _ (Nat.le_max_right _ _)

/-! ## Termination -/

theorem nodup_flatMap_own {own : Nat → List Nat} (hnd : ∀ p, (own p).Nodup)
    (hdisj : ∀ p q j, j ∈ own p → j ∈ own q → p = q) :
    ∀ {os : List Nat}, os.Nodup → (os.flatMap own).Nodup
  | [], _ => List.nodup_nil
  | p :: os, h => by
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hnd p, nodup_flatMap_own hnd hdisj (List.nodup_cons.mp h).2, fun a ha b hb hab => ?_⟩
      subst hab
      obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.mp hb
      exact (List.nodup_cons.mp h).1 (hdisj p q a ha hbq ▸ hq)

/-- **D-X1f2: `combSettle2` terminates on a window-acyclic design**, from every state shaped for
its process-level lowering, under every process-atomic legal schedule (the existence half of `rcomb1`, window rank). -/
theorem combSettle2_terminates_win {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    {rank : Nat → Nat} (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps)
    (hS : WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank) (σ : ScheduleOracle) (k : Nat)
    {st : SvState} (hs : StateShape d' st) :
    ∃ fuel S k', combSettle2 E.toDesign2 σ fuel st k = .ok (S, k') ∧ StateShape d' S := by
  have hsize : E.procs.size = d'.processes.size := by
    rw [(Design2.lowerComb_spec hl).2.2.1, Elab.size_toDesign2]
  have hq : CombPassSeq (E.toDesign2.winDesign ps) (combSettleSeq d' σ k st)
      (fun q => (σ.choose (k + q) d'.combIndices).flatMap (winOwn ps)) :=
    { shape0 := shape_win_of_lower hl hw hs
      nodup := fun q => nodup_flatMap_own
        (fun p => by unfold winOwn; exact (List.nodup_range (n := _)).filter _) hS.disj
        (hd'.nodup_choose σ (k + q))
      mem := fun q j hj => by
        obtain ⟨p, hp, hjp⟩ := hS.cover j hj
        exact List.mem_flatMap.mpr ⟨p, (hd'.mem_choose σ (k + q) p).mpr (hsize ▸ hp), hjp⟩
      pass := fun q => pass_win hl hd' hw hS _ _ _ _ (combSettleSeq_shape hd' σ k hs q)
        (combSettleSeq_spec hd' σ k hs q).2 }
  have hstab := hq.stable hS.comb hS.ranked hS.bound
  obtain ⟨S, k', h, hsS⟩ := combSettle2_ok_of_stable (σ := σ) (k := k) hd' hs
    (E.toDesign2.winDesign ps).processes.size 0 _
    (by rw [Nat.zero_add]; exact (hstab _ (Nat.le_succ _)).symm) (Nat.le_refl _)
  obtain ⟨-, f', hf'⟩ := (CombSim.of_lowerComb' hl hd').combSettle2 σ _ st k S k' hs h
  exact ⟨f', S, k', hf', hsS⟩

/-- **The fixture**: the settle on `ibex`'s design terminates, though its process-level lowering
is cyclic (`ibexLow_not_acyclic`). -/
theorem Core0Smoke.ibex_terminates (σ : ScheduleOracle) (k : Nat) {st : SvState}
    (hs : StateShape Core0Smoke.ibexLow st) :
    ∃ fuel S k', combSettle2 Core0Smoke.ibex.toDesign2 σ fuel st k = .ok (S, k') :=
  let ⟨f, S, k', h, _⟩ := combSettle2_terminates_win Core0Smoke.ibex_lower
    Core0Smoke.ibexLow_comb Core0Smoke.ibex_lowerWin Core0Smoke.ibex_wsettles σ k hs
  ⟨f, S, k', h⟩

#print axioms WriteRel.unique
#print axioms WriteRel.snoc
#print axioms seq_run
#print axioms run_writeRel
#print axioms proc_pass
#print axioms pass_win
#print axioms combSettle2_terminates_win
#print axioms Core0Smoke.ibex_terminates

end LeanModels.Sv.Kernel
