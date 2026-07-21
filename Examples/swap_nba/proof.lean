/-
Proof module for `Examples/swap_nba/spec.lean` (three-file example layout,
SV lane). M0 theorem 2 of `docs/sv-design-m0.md` — the nonblocking-assign
swap is correct under EVERY schedule — relocated verbatim from the retired
`LeanModels/Sv/Proofs.lean` (raw theorems + canonical-trace lemmas) and
`LeanModels/Sv/Delab.lean` (surface corollaries). Shared infrastructure
(`sv_simp`, `appIn`, `combSettle_nil`, the schedule-oracle case splits)
lives in `LeanModels/Sv/Obs.lean`.

House rules inherited from the Python lane: induction on the MATHEMATICAL
structure (stimulus lists), never on fuel; fuel witnesses are generous
slack constants consumed in threshold form (`∀ F, 8 ≤ F → …`); `∀ σ` is
handled by the finite `ScheduleOracle.choose_*` case splits.

The proof architecture: one **forward canonical-trace lemma**
(`swapNba_run`, by one symbolic cycle `swapNba_cycleStep` and one induction
over the stimulus), then every hypothesis-form theorem follows by
**cross-fuel determinism** (`run_det`) — the trace *is* the canonical one,
and the spec content becomes pure list mathematics (`swapNbaTrace_chain`).

The design literal below is a hand-built copy of the extracted envelope;
`spec.lean` certifies (at elab time, from disk) that it is node-for-node
equal to `Examples/swap_nba/swap_nba.sv.json`.
-/
import LeanModels.Sv.Delab

namespace Examples.swap_nba.proof

open LeanModels.Sv

/-- `Examples/swap_nba/swap_nba.sv` (nonblocking assigns — the correct
swap). -/
def swapNbaDesign : Design :=
  { name := "swap_nba"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (.ofNat 8 1) },
      { name := "b", width := 8, init := some (.ofNat 8 2) }]
    processes := #[
      .alwaysPlain "clk" (.nbaAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.nbaAssign "b" (.ident "a"))] }

/-! ### Design-index facts (`rfl`; what σ's `choose` gets applied to) -/

theorem swapNba_combIndices : swapNbaDesign.combIndices = [] := rfl
theorem swapNba_edgeIndices : swapNbaDesign.edgeIndices = [0, 1] := rfl
theorem swapNba_p0 :
    swapNbaDesign.processes[0]? =
      some (.alwaysPlain "clk" (.nbaAssign "a" (.ident "b"))) := rfl
theorem swapNba_p1 :
    swapNbaDesign.processes[1]? =
      some (.alwaysPlain "clk" (.nbaAssign "b" (.ident "a"))) := rfl

theorem initState_swapNba :
    initState swapNbaDesign =
      [("clk", LVec.xVec 1), ("a", LVec.ofNat 8 1), ("b", LVec.ofNat 8 2)] := rfl

/-! ## Applied inputs -/

theorem applyInputs_swapNba (inputs : SvState) (c va vb : LVec) :
    applyInputs swapNbaDesign inputs [("clk", c), ("a", va), ("b", vb)] =
      [("clk", appIn inputs "clk" c), ("a", va), ("b", vb)] := by
  show (match SvState.lookup inputs "clk" with
        | some v => SvState.set [("clk", c), ("a", va), ("b", vb)] "clk" v
        | none => [("clk", c), ("a", va), ("b", vb)]) = _
  cases h : SvState.lookup inputs "clk" <;> simp [appIn, h, SvState.set]

/-! ## Theorem 2: `swap_nba` swaps every cycle, under EVERY schedule -/

/-- Canonical `swap_nba` trace: from register values `(va, vb)`, each cycle
snapshots `(vb, va)` and recurses swapped; `clk` follows the stimulus. -/
def swapNbaTrace (c va vb : LVec) : List SvState → List SvState
  | [] => []
  | inp :: rest =>
      [("clk", appIn inp "clk" c), ("a", vb), ("b", va)] ::
        swapNbaTrace (appIn inp "clk" c) vb va rest

/-- One symbolic `swap_nba` cycle, ∀ σ (threshold form, slack 8): the comb
phases are empty (`combSettle_nil`), the edge phase runs the two NBA
processes in either `choose_pair` order — both orders queue
`a ↦ vb, b ↦ va` because NBA reads see the pre-commit state — and the
commit swaps the registers. -/
theorem swapNba_cycleStep (σ : ScheduleOracle) (inputs : SvState) (c va vb : LVec)
    (k : Nat) : ∀ F, 8 ≤ F →
    cycleStep swapNbaDesign σ F inputs [("clk", c), ("a", va), ("b", vb)] k =
      .ok ([("clk", appIn inputs "clk" c), ("a", vb), ("b", va)], k + 3) := by
  intro F hF
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  simp only [cycleStep, applyInputs_swapNba]
  rw [combSettle_nil swapNba_combIndices]
  simp only [Res.ok_bind, swapNba_edgeIndices]
  rcases σ.choose_pair (k + 1) 0 1 with hc | hc <;> rw [hc]
  · sv_simp [swapNba_p0, swapNba_p1]
    rw [combSettle_nil swapNba_combIndices]
  · sv_simp [swapNba_p0, swapNba_p1]
    rw [combSettle_nil swapNba_combIndices]

/-- The canonical run, ∀ σ ∀ stimulus (threshold form): induction over the
stimulus splicing `swapNba_cycleStep` at every cycle. -/
theorem swapNba_runFrom (σ : ScheduleOracle) :
    ∀ (stim : List SvState) (c va vb : LVec) (k F : Nat), 8 ≤ F →
      runFrom swapNbaDesign σ F [("clk", c), ("a", va), ("b", vb)] k stim =
        .ok (swapNbaTrace c va vb stim) := by
  intro stim
  induction stim with
  | nil => intro c va vb k F hF; simp [runFrom, swapNbaTrace]
  | cons inp rest ih =>
    intro c va vb k F hF
    simp only [runFrom, swapNbaTrace]
    rw [swapNba_cycleStep σ inp c va vb k F hF]
    simp only [Res.ok_bind]
    rw [ih (appIn inp "clk" c) vb va (k + 3) F hF]
    simp

/-- `swap_nba`'s full trace characterization: for EVERY schedule and EVERY
stimulus, any fuel ≥ 8 completes with the canonical trace. -/
theorem swapNba_run (σ : ScheduleOracle) (stim : List SvState) :
    ∀ F, 8 ≤ F →
      run swapNbaDesign σ F stim =
        .ok (swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim) := by
  intro F hF
  rw [run, initState_swapNba]
  exact swapNba_runFrom σ stim _ _ _ 0 F hF

/-- Non-vacuity: every schedule and stimulus yields the canonical trace. -/
theorem swap_nba_total (σ : ScheduleOracle) (stim : List SvState) :
    Runs swapNbaDesign σ stim
      (swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim) :=
  ⟨8, swapNba_run σ stim 8 (Nat.le_refl 8)⟩

/-- The swap property of the canonical trace, as pure list mathematics:
every adjacent snapshot pair (initial state prepended) swaps `a`/`b`. -/
theorem swapNbaTrace_chain :
    ∀ (stim : List SvState) (c va vb : LVec) (i : Nat) (s s' : SvState),
      (([("clk", c), ("a", va), ("b", vb)] : SvState) :: swapNbaTrace c va vb stim)[i]?
          = some s →
      (([("clk", c), ("a", va), ("b", vb)] : SvState) :: swapNbaTrace c va vb stim)[i + 1]?
          = some s' →
      SvState.lookup s' "a" = SvState.lookup s "b" ∧
      SvState.lookup s' "b" = SvState.lookup s "a" := by
  intro stim
  induction stim with
  | nil =>
    intro c va vb i s s' _ hs'
    rcases i with _ | j <;> simp [swapNbaTrace] at hs'
  | cons inp rest ih =>
    intro c va vb i s s' hs hs'
    cases i with
    | zero =>
      simp only [swapNbaTrace, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hs hs'
      subst hs hs'
      simp [SvState.lookup]
    | succ j =>
      simp only [swapNbaTrace, List.getElem?_cons_succ] at hs hs'
      exact ih (appIn inp "clk" c) vb va j s s' hs hs'

/-- **M0 theorem 2** (`docs/sv-design-m0.md`): for the `swap_nba` design,
under EVERY schedule, every fuel, and every stimulus, each post-edge
snapshot swaps `a`/`b` relative to its predecessor (the initial state
included) — the gallery's `Sv.onPosedge fun s s' => s'.a = s.b ∧ s'.b = s.a`
at M0's cycle level. Proof: the trace is the canonical one (`run_det`), and
the canonical trace swaps by construction (`swapNbaTrace_chain`). -/
theorem swap_nba_spec (σ : ScheduleOracle) {fuel : Nat} {stim tr : List SvState}
    (h : run swapNbaDesign σ fuel stim = .ok tr) :
    ∀ (i : Nat) (s s' : SvState),
      (initState swapNbaDesign :: tr)[i]? = some s →
      (initState swapNbaDesign :: tr)[i + 1]? = some s' →
      SvState.lookup s' "a" = SvState.lookup s "b" ∧
      SvState.lookup s' "b" = SvState.lookup s "a" := by
  have htr : tr = swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim :=
    run_det h (swapNba_run σ stim 8 (Nat.le_refl 8))
  subst htr
  rw [initState_swapNba]
  intro i s s' hs hs'
  exact swapNbaTrace_chain stim _ _ _ i s s' hs hs'

/-- Bonus (the gallery's `swap_nba_det`): `swap_nba` is schedule-
deterministic — ALL legal schedules produce the same trace. -/
theorem swap_nba_det : Deterministic swapNbaDesign := by
  intro σ₁ σ₂ stim tr₁ tr₂ h₁ h₂
  have e₁ := Runs.functional h₁ (swap_nba_total σ₁ stim)
  have e₂ := Runs.functional h₂ (swap_nba_total σ₂ stim)
  rw [e₁, e₂]

/-! ## The surface forms (spec.lean's statements; `sv_prove` corollaries) -/

/-- **M0 theorem 2, surface form** (gallery `swap_nba_spec` shape): under
every schedule, every posedge step swaps `a`/`b` — the pre-edge startup
state included. Corollary of `swap_nba_spec`. -/
theorem swap_nba_swaps :
    swapNbaDesign ⊨ onPosedge fun s s' =>
      SvState.lookup s' "a" = SvState.lookup s "b" ∧
      SvState.lookup s' "b" = SvState.lookup s "a" := by
  sv_prove [swap_nba_spec]

/-- `swap_nba` really runs, under every schedule: the canonical swapped
trace, in `⇓[σ]` form (= `swap_nba_total`). -/
theorem swap_nba_runs (σ : ScheduleOracle) (stim : List SvState) :
    swapNbaDesign / stim ⇓[σ]
      swapNbaTrace (LVec.xVec 1) (LVec.ofNat 8 1) (LVec.ofNat 8 2) stim := by
  sv_prove [swap_nba_total σ stim]

-- `sv_prove`'s Deterministic-from-totality arm re-derives the raw bonus.
example : Deterministic swapNbaDesign := by sv_prove [swap_nba_total]

/-! ## Non-vacuity pins (`#guard`)

The canonical trace reproduces the Xcelium-verified outcomes (same values
as `Tests.lean`/the differential harness), so the theorems above are about
the behavior the simulator actually exhibits. -/

-- swap_nba: (1,2) → (2,1) → (1,2)
#guard (swapNbaTrace (LVec.xVec 1) (.ofNat 8 1) (.ofNat 8 2)
    [[("clk", LVec.ofNat 1 1)], [("clk", LVec.ofNat 1 1)]]).map
      (SvState.showSignal · "a") == ["00000010", "00000001"]
#guard (swapNbaTrace (LVec.xVec 1) (.ofNat 8 1) (.ofNat 8 2)
    [[("clk", LVec.ofNat 1 1)], [("clk", LVec.ofNat 1 1)]]).map
      (SvState.showSignal · "b") == ["00000001", "00000010"]

end Examples.swap_nba.proof
