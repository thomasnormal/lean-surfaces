import LeanModels.Sv.Kernel.Core0Obs
import LeanModels.Sv.Kernel.Core0WinTerm

/-!
# R-DESIGN2 over the window rank (D-X1g) (`LeanModels.Sv.Kernel`)

`Core0Obs.lean`'s E → `run2` argument, restated over `WSettles` (R-COMB-1) instead of the process
rank `Settles`. **Status: transport theorem** (the inclusion relates E and `run2`; the restated
cycle lemmas are about both). Imported by no existing module.

* `WSettleAgree E d own`: `SettleAgree` with the window invariant `WSettleInv`.
  `WSettleAgree.ofLowerWin` is the instance from the per-window lowering, its `settles` field
  `combSettle2_terminates_win` (D-X1f2).
* `WSettles.nextSlot_inv`, `behaves0_inv`, `slot_start`, `slot_quiet`, `cycleObs2_of_slot_wagree`,
  `runFromObs2_of_behaves0_wagree`, `runs2_of_runs_E0_wagree`: the cycle lemmas, word for word
  with `WSettles`/`WSettleInv` for `Settles`/`SettleInv`.
* `included_E0_run2_win`: every E behaviour is a `run2` behaviour of the design itself, for
  designs whose process-level lowering may be cyclic. Fixture: `Core0Smoke.ibex_included`.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv.Observe LeanModels.Sv.Comb2Term

set_option autoImplicit false

variable {E : Elab} {d : Design2} {own : ProcId → List Nat} {rank : Nat → Nat}

/-- **A slot opened by input events keeps the window invariant.** -/
theorem WSettles.nextSlot_inv (hS : WSettles E d own rank) {c : Config}
    (hI : WSettleInv E d own c) (hc : c.active = []) (entry : SvState) :
    WSettleInv E d own (Config.nextSlot E c entry) := by
  have hnames : d.inputNames = E.toDesign2.inputNames := by
    simp [Design2.inputNames, Elab.toDesign2, hS.decls]
  refine ⟨hI.typed.applyInputs entry, (List.nodup_range.filter _), fun q hq =>
    (Elab.mem_triggered hq).1, fun q hqn hq j hj => ?_⟩
  have hold := hI.eqs q hqn (by rw [hc]; exact List.not_mem_nil) j hj
  intro t e n lo w off hp hm
  obtain ⟨old, v, hlo, hv, hext⟩ := hold t e n lo w off hp hm
  have hreads := Elab.not_triggered hqn hq
  have hdr : n ∉ E.toDesign2.inputNames.toList := by
    rw [← hnames]
    exact hS.comb.notInput n ⟨j, lo, w, t, e, hp, Win.mem_of_mem_placed hm⟩
  refine ⟨old, v, ?_, ?_, hext⟩
  · show SvState.lookup (E.view (E.applyInputs c.store entry)) n = some old
    rw [Elab.lookup_view_applyInputs_of_not_input _ _ hdr]; exact hlo
  rw [← hv]
  exact (evalPure2_congr_reads fun r hr => hreads r (hS.complete q j t e hj hp r hr)).symm

theorem WSettles.behaves0_inv (hS : WSettles E d own rank) {env : List SvState} {ch : Choice}
    {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) :
    ∀ t, WSettleInv E d own (cfg t) ∧ (cfg t).active = []
  | 0 => ⟨hS.steps_inv hb.1.1 (WSettleInv.init hS.startReady ((Elab.typed_initStore E).applyInputs _)),
      active_nil_of_closed hb.1.2⟩
  | t + 1 =>
      have ih := hS.behaves0_inv hb t
      ⟨hS.steps_inv (hb.2 t).1 (hS.nextSlot_inv ih.1 ih.2 _), active_nil_of_closed (hb.2 t).2⟩

theorem WSettles.slot_start (hS : WSettles E d own rank) {env : List SvState} {ch : Choice}
    {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) (c : Nat) :
    ∃ (C : Config) (s₀ : Store), C.store = E.applyInputs s₀ (slotEntry env (2 * c)) ∧
      E.Typed s₀ ∧ WSettleInv E d own C ∧ SlotCloses E ch C (cfg (2 * c)) ∧
      (c = 0 → s₀ = E.initStore) ∧ (0 < c → s₀ = (cfg (2 * c - 1)).store) := by
  cases c with
  | zero =>
      exact ⟨Config.start E (slotEntry env 0), E.initStore, rfl, E.typed_initStore,
        WSettleInv.init hS.startReady ((Elab.typed_initStore E).applyInputs _), hb.1, fun _ => rfl,
        fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ c =>
      have hidx : 2 * (c + 1) - 1 + 1 = 2 * (c + 1) := by omega
      have hinv := hS.behaves0_inv hb (2 * (c + 1) - 1)
      have hcl := hb.2 (2 * (c + 1) - 1)
      rw [hidx] at hcl
      exact ⟨Config.nextSlot E (cfg (2 * (c + 1) - 1)) (slotEntry env (2 * (c + 1))),
        (cfg (2 * (c + 1) - 1)).store, rfl, hinv.1.typed, hS.nextSlot_inv hinv.1 hinv.2 _, hcl,
        fun h => absurd h (Nat.succ_ne_zero c), fun _ => rfl⟩

theorem WSettles.slot_quiet (hS : WSettles E d own rank) {env : List SvState} {ch : Choice}
    {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) (c : Nat) :
    cfg (2 * c + 1) = cfg (2 * c) := by
  have hcl := hb.2 (2 * c)
  have hentry : slotEntry env (2 * c + 1) = [] := by
    have h1 : (2 * c + 1) % 2 = 1 := by omega
    simp [slotEntry, h1]
  rw [hentry, nextSlot_nil (hS.behaves0_inv hb (2 * c)).2] at hcl
  exact slotCloses_closed (hS.behaves0_inv hb (2 * c)).2 hcl

/-- **`SettleAgree` over the window invariant.** -/
structure WSettleAgree (E : Elab) (d : Design2) (own : ProcId → List Nat) : Prop where
  edge : E.toDesign2.edgeIndices = []
  reset : ∀ a b, E.toDesign2.resetIndices a b = []
  closed : ∀ {ch : Choice} {c c' : Config}, WSettleInv E d own c → SlotCloses E ch c c' →
    ∀ {σ : ScheduleOracle} {fuel k : Nat} {S : SvState} {k' : Nat},
      combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (S, k') → E.view c'.store = S
  settles : ∀ {ch : Choice} {c c' : Config}, WSettleInv E d own c → SlotCloses E ch c c' →
    ∀ (σ : ScheduleOracle) (k : Nat), ∃ fuel k',
      combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (E.view c'.store, k')

/-- **The instance from the per-window lowering**: `closed` is `WSettles.closed_eq_combSettle2`,
`settles` is `combSettle2_terminates_win` (D-X1f2). -/
theorem WSettleAgree.ofLowerWin {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps)
    (hS : WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank) :
    WSettleAgree E (E.toDesign2.winDesign ps) (winOwn ps) where
  edge := (Design2.lowerComb_phases hl).1
  reset := (Design2.lowerComb_phases hl).2.1
  closed := fun {_ _ _} hI h {_ _ _ _ _} hS2 => WSettles.closed_eq_combSettle2 hl hd' hw hS hI h hS2
  settles := fun hI h σ k => by
    have hs : StateShape d' (E.view _) :=
      Elab.shape_view_of hd' (Design2.lowerComb_spec hl).2.1 hI.typed
    obtain ⟨f, S, k', hS2, -⟩ := combSettle2_terminates_win hl hd' hw hS σ k hs
    exact ⟨f, k', by rw [WSettles.closed_eq_combSettle2 hl hd' hw hS hI h hS2]; exact hS2⟩

/-- **One cycle agrees**, window rank. -/
theorem cycleObs2_of_slot_wagree (hS : WSettles E d own rank) (hA : WSettleAgree E d own)
    {ch : Choice} {C c' : Config} {s₀ : Store} {entry : SvState} (hT0 : E.Typed s₀)
    (hC : C.store = E.applyInputs s₀ entry) (hI : WSettleInv E d own C)
    (hcl : SlotCloses E ch C c') (σ : ScheduleOracle) (k : Nat) :
    ∃ F₀ k', ∀ F, F₀ ≤ F → cycleObs2 E.toDesign2 σ F
        (inputsOf E.toDesign2 (E.view c'.store)) (E.view s₀) k =
      .ok (⟨E.view c'.store, E.view c'.store⟩, k') := by
  have hdd : E.toDesign2.decls = d.decls := hS.decls.symm
  have hd := hS.comb
  have hre : applyInputs2 E.toDesign2 (inputsOf E.toDesign2 (E.view c'.store)) (E.view s₀) =
      E.view C.store := by
    rw [applyInputs2_congr hdd, inputsOf_congr hdd]
    have hF := hS.steps_frame hcl.1 hI
    refine applyInputs2_redrive hd (hS.shape hT0) (hS.shape hI.typed) (fun n hn => ?_)
      (fun n hn => ?_)
    · rw [hC]; exact Elab.lookup_view_applyInputs_of_not_input _ _ (by rwa [inputNames_congr hdd])
    · exact (Frame.lookup_input hd hF hn).symm
  have hI' : WSettleInv E d own c' := hS.steps_inv hcl.1 hI
  obtain ⟨F1, k1, h1⟩ := hA.settles hI hcl σ k
  obtain ⟨F2, k2, h2⟩ := hA.settles hI' hcl.self σ (k1 + 1)
  refine ⟨max F1 F2, k2, fun F hF => ?_⟩
  have h1' := combSettle2_mono h1 (fun h => by cases h) F (Nat.le_trans (Nat.le_max_left _ _) hF)
  have h2' := combSettle2_mono h2 (fun h => by cases h) F (Nat.le_trans (Nat.le_max_right _ _) hF)
  rw [← hre] at h1'
  have hnil : σ.choose k1 E.toDesign2.edgeIndices = [] := by
    rw [hA.edge]; exact List.perm_nil.mp (σ.choose_perm k1 [])
  simp only [cycleObs2, cyclePre2, h1', Res.ok_bind, resetPhase2_of_nil (hA.reset _ _), cyclePost2,
    hnil, edgePass2, commitNba2, List.foldl_nil, h2']
  rfl

theorem runFromObs2_of_behaves0_wagree (hS : WSettles E d own rank) (hA : WSettleAgree E d own)
    (hinit : InitTyped E.toDesign2) {env : List SvState} {ch : Choice} {cfg : Nat → Config}
    (hb : Behaves0 E env ch cfg) (σ : ScheduleOracle) :
    ∀ (n c0 k : Nat) (st : SvState),
      (c0 = 0 → st = initState2 E.toDesign2) → (0 < c0 → st = E.view (cfg (2 * c0 - 1)).store) →
      ∃ F₀, ∀ F, F₀ ≤ F → runFromObs2 E.toDesign2 σ F st k
          ((List.range' c0 n).map fun c => inputsOf E.toDesign2 (E.view (cfg (2 * c)).store)) =
        .ok ((List.range' c0 n).map fun c =>
          ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩) := by
  have hnd : (E.decls.toList.map Decl.name).Nodup := hS.decls ▸ hS.comb.nodup
  intro n
  induction n with
  | zero => intro _ _ _ _ _; exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
      intro c0 k st h0 hpos
      simp only [List.range', List.map_cons]
      obtain ⟨C, s₀, hC, hT0, hI, hcl, hz, hp⟩ := hS.slot_start hb c0
      have hst : st = E.view s₀ := by
        cases c0 with
        | zero => rw [h0 rfl, hz rfl]; exact (view_initStore hnd hinit).symm
        | succ c => rw [hpos (Nat.succ_pos c), hp (Nat.succ_pos c)]
      subst hst
      obtain ⟨F1, k', hcyc⟩ := cycleObs2_of_slot_wagree hS hA hT0 hC hI hcl σ k
      have hq := hS.slot_quiet hb c0
      obtain ⟨F2, hrest⟩ := ih (c0 + 1) k' (E.view (cfg (2 * c0)).store)
        (fun h => absurd h (Nat.succ_ne_zero c0))
        (fun _ => by rw [show 2 * (c0 + 1) - 1 = 2 * c0 + 1 by omega, hq])
      refine ⟨max F1 F2, fun F hF => ?_⟩
      simp only [runFromObs2, hcyc F (Nat.le_trans (Nat.le_max_left _ _) hF), Res.ok_bind]
      rw [hrest F (Nat.le_trans (Nat.le_max_right _ _) hF)]
      simp only [Res.ok_bind, hq]
      rfl

theorem runs2_of_runs_E0_wagree (hS : WSettles E d own rank) (hA : WSettleAgree E d own)
    (hinit : InitTyped E.toDesign2) {ch : Choice} {env : List SvState}
    {r : List (CycleObs SvState)} (hr : Obs_E0.Runs E ch env r) (σ : ScheduleOracle) :
    Obs_run2.Runs E.toDesign2 σ (r.map fun o => inputsOf E.toDesign2 o.pre) r := by
  obtain ⟨b, ⟨cfg, hb, hbt⟩, rfl⟩ := hr
  have hr : ((List.range env.length).map fun c =>
      (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState)) =
      (List.range' 0 env.length).map fun c =>
        ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩ := by
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro c _
    rw [Nat.add_sub_cancel, hbt, hbt]
  obtain ⟨F₀, hF⟩ := runFromObs2_of_behaves0_wagree hS hA hinit hb σ env.length 0 0 _
    (fun _ => rfl) (fun h => absurd h (Nat.lt_irrefl 0))
  refine ⟨F₀, ?_⟩
  show runObs2 E.toDesign2 σ F₀
      (((List.range env.length).map fun c =>
        (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState)).map
          fun o => inputsOf E.toDesign2 o.pre) =
    .ok ((List.range env.length).map fun c =>
      (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState))
  rw [hr, List.map_map]
  unfold runObs2
  have hg : run2ClockGuard E.toDesign2 = .ok () := by
    unfold run2ClockGuard run2ClockNames Elab.toDesign2
    have hnames : List.filterMap (run2Clock? ∘ Proc0.toProcess2) E.procs.toList = [] := by
      induction E.procs.toList with
      | nil => rfl
      | cons p ps ih => cases p <;>
          simp only [List.filterMap_cons, Function.comp_apply, Proc0.toProcess2,
            run2Clock?, ih]
    have hi : ∀ ps : List Proc0,
        (ps.map Proc0.toProcess2).any (fun p =>
          match p with
          | .unsupported svKind _ => svKind.startsWith "SignalEventControl:"
          | _ => false) = false := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => cases p <;>
          simp only [List.map_cons, List.any_cons, Proc0.toProcess2, ih, Bool.false_or] <;>
            native_decide
    have hc : (List.filterMap run2Clock? (E.procs.toList.map Proc0.toProcess2)).eraseDups = [] := by
      simpa [Function.comp_def] using congrArg List.eraseDups hnames
    rw [hc]
    simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
    have hi' := hi E.procs.toList
    split
    · next h => exact Bool.noConfusion (hi'.symm.trans h)
    · rfl
  simp only [hg, Res.ok_bind]
  exact hF F₀ (Nat.le_refl _)

/-- **R-DESIGN2, comb slice, E → `run2`, window rank** (transport theorem): for a design whose
bodies lower per window to an equation design with a window rank (`WSettles`), every E behaviour
is a `run2` behaviour of the design itself. Its process-level lowering may be cyclic. -/
theorem included_E0_run2_win {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps)
    (hS : WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank)
    (hinit : InitTyped E.toDesign2) (k : Clocking) :
    Included Obs_E0 Obs_run2 k E E.toDesign2 := by
  refine ⟨rfl, fun ch e₁ b _ hb => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hb
  exact ⟨ch, _, trivial, r,
    runs2_of_runs_E0_wagree hS (WSettleAgree.ofLowerWin hl hd' hw hS) hinit hr ch, rfl⟩

namespace Core0Smoke

theorem ibex_initTyped : InitTyped ibex.toDesign2 := by
  intro dc hdc v hv
  simp [ibex, Elab.toDesign2] at hdc
  rcases hdc with rfl | rfl | rfl | rfl <;> simp at hv

/-- **The payoff fixture**: E → `run2` for `ibex`, whose process-level lowering is cyclic
(`ibexLow_not_acyclic`, `ibex_no_settles`: the process-rank route has no instance). -/
theorem ibex_included (k : Clocking) : Included Obs_E0 Obs_run2 k ibex ibex.toDesign2 :=
  included_E0_run2_win ibex_lower ibexLow_comb ibex_lowerWin ibex_wsettles ibex_initTyped k

end Core0Smoke

#print axioms WSettles.nextSlot_inv
#print axioms WSettleAgree.ofLowerWin
#print axioms cycleObs2_of_slot_wagree
#print axioms runFromObs2_of_behaves0_wagree
#print axioms included_E0_run2_win
#print axioms Core0Smoke.ibex_included

end LeanModels.Sv.Kernel
