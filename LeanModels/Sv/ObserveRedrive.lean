import LeanModels.Sv.Observe
import LeanModels.Sv.ObserveFrame
import LeanModels.Sv.Comb2Sound

/-!
# Re-driving the held inputs: a comb run is the run of its re-driven stimulus

**Status: provisional over `run2`** (library, never trusted). Imported by nothing in the tree.

For an assign-only (comb-profile) design, take any completed `runObs2` run `r` of a stimulus. Replace
each entry by the one that re-drives every input port to the value it holds in that cycle's PRE
sample (`redriveEntry`). That stimulus has the SAME run, at the same fuel, under the same schedule
(`runObs2_redrive`). Each cycle's applied state is identical (`applyInputs2_redriveEntry`), because
an input holds in the pre sample exactly what `applyInputs2` gave it: comb processes never write an
input (`CombDesign.notInput`).

This is agent A's re-driving argument (branch `arch-x1`, `Kernel/Core0Obs.lean`: `inputsOf`,
`applyInputs2_redrive`), restated over `run2` alone. A uses it for E → `run2`; here it closes the
direction "v1 ⇒ inputs read from the pre sample" (`svgolf/design/architecture/ObsCombRedrive.lean`).
Every input value a pre sample shows is then also bound by a stimulus entry, so the held-input cycles
that v1 does not constrain disappear. `redriveEntry` is A's `inputsOf` under another name, to avoid a
clash before A switches to this file. No typed-stimulus restriction is needed over `run2`: the
re-driving entry binds exactly the values the pre sample holds.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv

/-- The stimulus entry that re-drives every input port of `d` to its value in `st`. -/
def redriveEntry (d : Design2) (st : SvState) : SvState :=
  d.inputNames.toList.filterMap fun n => (SvState.lookup st n).map fun v => (n, v)

theorem lookup_redriveEntry (d : Design2) (st : SvState) (n : String) :
    SvState.lookup (redriveEntry d st) n =
      if n ∈ d.inputNames.toList then SvState.lookup st n else none :=
  lookup_filterMap (SvState.lookup st) n _

/-- **Re-driving the inputs**: from `st₀`, the entry that drives every input to its value in `st₂`
gives the state `st₁` that agrees with `st₀` off the inputs and with `st₂` on them. -/
theorem applyInputs2_redriveEntry {d : Design2} (hd : CombDesign d) {st₀ st₁ st₂ : SvState}
    (hs₀ : StateShape d st₀) (hs₁ : StateShape d st₁)
    (hoff : ∀ n, n ∉ d.inputNames.toList → SvState.lookup st₁ n = SvState.lookup st₀ n)
    (hon : ∀ n, n ∈ d.inputNames.toList → SvState.lookup st₂ n = SvState.lookup st₁ n) :
    applyInputs2 d (redriveEntry d st₂) st₀ = st₁ := by
  have hkeys : ∀ n ∈ d.inputNames.toList, n ∈ st₀.map Prod.fst :=
    fun n hn => hs₀.keys ▸ Design2.mem_names_of_mem_inputNames hn
  apply SvState.ext
  · rw [keys_applyInputs2 d _ hd.inFourState hkeys, hs₀.keys, hs₁.keys]
  · rw [keys_applyInputs2 d _ hd.inFourState hkeys, hs₀.keys]; exact hd.nodup
  · intro n
    rw [lookup_applyInputs2 d _ _ n hd.inFourState, lookup_redriveEntry]
    by_cases hn : n ∈ d.inputNames.toList
    · rw [if_pos hn, if_pos hn, hon n hn]
      obtain ⟨v, hv⟩ := hs₁.lookup_of_mem (Design2.mem_names_of_mem_inputNames hn)
      rw [hv]; rfl
    · rw [if_neg hn]; exact (hoff n hn).symm

/-- A cycle reads its stimulus entry only through `applyInputs2`. -/
theorem cycleObs2_congr_entry {d : Design2} {σ : ScheduleOracle} {F : Nat} {e e' st : SvState}
    {k : Nat} (h : applyInputs2 d e st = applyInputs2 d e' st) :
    cycleObs2 d σ F e st k = cycleObs2 d σ F e' st k := by
  unfold cycleObs2 cyclePre2
  rw [h]

/-- One comb cycle from a shaped state: both samples are shaped, and an input holds in the pre
sample what `applyInputs2` gave it. -/
theorem cycleObs2_comb_shape {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle} {F : Nat}
    {e st : SvState} {k : Nat} {o : CycleObs SvState} {k' : Nat} (hs : StateShape d st)
    (h : cycleObs2 d σ F e st k = .ok (o, k')) :
    StateShape d o.pre ∧ StateShape d o.post ∧
      ∀ n ∈ d.inputNames.toList, SvState.lookup o.pre n = SvState.lookup (applyInputs2 d e st) n := by
  obtain ⟨st1, k1, k2, h1, hnil, -, -, hpost⟩ := pre_sample_spec h
  obtain ⟨hpre, -⟩ := hnil (hd.resetIndices_eq st st1)
  obtain ⟨-, hs1, hnd1⟩ := combSettle2_eqs hd (StateShape.of_applyInputs2 hd hs e) h1
  rw [← hpre] at hs1 hnd1
  unfold cyclePost2 at hpost
  rw [hd.edgeIndices_eq, σ.choose_nil] at hpost
  simp only [edgePass2, Res.ok_bind] at hpost
  have hc : commitNba2 o.pre [] = o.pre := rfl
  rw [hc] at hpost
  obtain ⟨-, hs2, -⟩ := combSettle2_eqs hd hs1 hpost
  exact ⟨hs1, hs2, fun n hn => hnd1 n fun hdr => hd.notInput n hdr hn⟩

/-- **A comb run is the run of its re-driven stimulus**, from any shaped state, at the same fuel and
schedule. -/
theorem runFromObs2_redrive {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle} {F : Nat} :
    ∀ (stim : List SvState) (st : SvState) (k : Nat) (r : List (CycleObs SvState)),
      StateShape d st → runFromObs2 d σ F st k stim = .ok r →
      runFromObs2 d σ F st k (r.map fun o => redriveEntry d o.pre) = .ok r
  | [], st, k, r, _, h => by
      simp only [runFromObs2, Res.ok.injEq] at h
      subst h; rfl
  | e :: rest, st, k, r, hs, h => by
      simp only [runFromObs2, Res.bind_eq_ok] at h
      obtain ⟨⟨o, k'⟩, h1, os, h2, h3⟩ := h
      simp only [Res.pure_eq, Res.ok.injEq] at h3
      subst h3
      obtain ⟨-, hspost, hin⟩ := cycleObs2_comb_shape hd hs h1
      have happ : applyInputs2 d (redriveEntry d o.pre) st = applyInputs2 d e st := by
        refine applyInputs2_redriveEntry hd hs (StateShape.of_applyInputs2 hd hs e) (fun n hn => ?_) hin
        rw [lookup_applyInputs2 d _ _ n hd.inFourState, if_neg hn]
      have hc : cycleObs2 d σ F (redriveEntry d o.pre) st k = .ok (o, k') := by
        rw [cycleObs2_congr_entry happ]; exact h1
      simp only [List.map_cons, runFromObs2, hc, Res.ok_bind,
        runFromObs2_redrive hd rest o.post k' os hspost h2]
      rfl

/-- **`runObs2` form**: every completed comb run is the run of its re-driven stimulus. -/
theorem runObs2_redrive {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle} {F : Nat}
    {stim : List SvState} {r : List (CycleObs SvState)} (h : runObs2 d σ F stim = .ok r) :
    runObs2 d σ F (r.map fun o => redriveEntry d o.pre) = .ok r :=
  by
    have hg : run2ClockGuard d = .ok () := by
      cases hq : run2ClockGuard d with
      | ok u => simpa using hq
      | timeout => simp [runObs2, hq] at h
      | unsupported msg => simp [runObs2, hq] at h
    have hfrom : runFromObs2 d σ F (initState2 d) 0 stim = .ok r := by
      simpa [runObs2, hg] using h
    have hredrive := runFromObs2_redrive hd stim (initState2 d) 0 r
      (StateShape.of_initState2 hd) hfrom
    simpa [runObs2, hg] using hredrive

/-! ## A comb-profile design writes no input port

The syntactic check of `ObserveFrame.lean` follows from the comb profile. Every process is an assign
whose target has static windows, and no driven signal is an input (`CombDesign.notInput`). So a
record that exports its `CombDesign` lemma needs no separate `writesInput` side condition. The
condition matters because at a symbolic parameter `rfl` cannot evaluate `writesInput` of an
instantiated family. -/

mutual
/-- A target with static windows writes only the names of its windows. -/
theorem Lhs2.win_of_writesName (d : Design2) (n : String) :
    ∀ (t : Lhs2) (ws : List Win), t.windows? d = some ws → t.writesName n = true →
      ∃ w ∈ ws, w.1 = n
  | .ident m, ws, h, hw => by
      simp only [Lhs2.windows?, Lhs2.window?, Option.map_map] at h
      cases hdw : d.declWidth m with
      | none => simp [hdw] at h
      | some dw =>
          simp only [hdw, Option.map_some, Function.comp, Option.some.injEq] at h
          subst h
          simp only [Lhs2.writesName, beq_iff_eq] at hw
          exact ⟨_, List.mem_singleton_self _, hw⟩
  | .slice m lo w, ws, h, hw => by
      simp only [Lhs2.windows?, Lhs2.window?, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [Lhs2.writesName, beq_iff_eq] at hw
      exact ⟨_, List.mem_singleton_self _, hw⟩
  | .index m idx ew, ws, h, hw => by
      simp only [Lhs2.writesName, beq_iff_eq] at hw
      cases idx with
      | lit c =>
          simp only [Lhs2.windows?, Lhs2.window?, Option.map_map] at h
          cases hc : c.toNat? with
          | none => simp [hc] at h
          | some k =>
              simp only [hc, Option.map_some, Function.comp, Option.some.injEq] at h
              subst h
              exact ⟨_, List.mem_singleton_self _, hw⟩
      | _ => simp [Lhs2.windows?, Lhs2.window?] at h
  | .concat ps, ws, h, hw => by
      simp only [Lhs2.windows?] at h
      simp only [Lhs2.writesName] at hw
      exact Lhs2.win_of_writesNameList d n ps ws h hw
termination_by structural t => t

theorem Lhs2.win_of_writesNameList (d : Design2) (n : String) :
    ∀ (ps : List Lhs2) (ws : List Win), Lhs2.listWindows? d ps = some ws →
      Lhs2.writesNameList n ps = true → ∃ w ∈ ws, w.1 = n
  | [], _, _, hw => by simp [Lhs2.writesNameList] at hw
  | p :: ps, ws, h, hw => by
      obtain ⟨a, b, ha, hb, rfl⟩ := Lhs2.listWindows?_cons_eq_some.mp h
      simp only [Lhs2.writesNameList, Bool.or_eq_true] at hw
      rcases hw with hw | hw
      · obtain ⟨w, hm, he⟩ := Lhs2.win_of_writesName d n p a ha hw
        exact ⟨w, List.mem_append_left _ hm, he⟩
      · obtain ⟨w, hm, he⟩ := Lhs2.win_of_writesNameList d n ps b hb hw
        exact ⟨w, List.mem_append_right _ hm, he⟩
termination_by structural ps => ps
end

/-- **A comb-profile design writes no input port.** -/
theorem CombDesign.writesInput_eq_false {d : Design2} (hd : CombDesign d) :
    d.writesInput = false := by
  unfold Design2.writesInput
  rw [List.any_eq_false]
  intro p hp
  rw [Bool.not_eq_true, List.any_eq_false]
  intro n hn hwr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hi
  obtain ⟨t, e, ws, rfl, hws⟩ := hd.assign i p hi
  obtain ⟨⟨m, lo, w⟩, hm, rfl⟩ := Lhs2.win_of_writesName d n t ws hws hwr
  exact hd.notInput m ⟨i, lo, w, t, e, hi, by rw [Lhs2.wins_of_windows? hws]; exact hm⟩ hn

#print axioms lookup_redriveEntry
#print axioms applyInputs2_redriveEntry
#print axioms cycleObs2_congr_entry
#print axioms cycleObs2_comb_shape
#print axioms runFromObs2_redrive
#print axioms runObs2_redrive
#print axioms CombDesign.writesInput_eq_false

end LeanModels.Sv.Observe
