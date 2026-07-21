import LeanModels.Sv.Obs

/-!
# The M0 theorems (`LeanModels.Sv`)

The four normative theorems of `docs/sv-design-m0.md` ("Normative theorems"),
plus the `sv_simp` symbolic-execution tactic and the canonical-trace lemmas
they ride on. House rules inherited from the Python lane: induction on the
MATHEMATICAL structure (stimulus/cycle lists), never on fuel; fuel witnesses
are generous slack constants consumed in threshold form
(`∀ F, 8 ≤ F → …` — never exact-offset fuel arithmetic); `∀ σ` handled by
the finite `ScheduleOracle.choose_*` case splits (Obs.lean).

## The proof architecture (what the Surface phase should reuse)

For each ∀σ design we prove a **forward canonical-trace lemma** — e.g.
`swapNba_run : ∀ F, 8 ≤ F → run swapNbaDesign σ F stim = .ok (swapNbaTrace …)`
— by one symbolic cycle (`swapNba_cycleStep`, `counter_cycleStep`) and one
induction over the stimulus (`runFrom`). Every hypothesis-form theorem
(`run … = .ok tr → P tr`) then follows by **cross-fuel determinism**
(`run_det`): `tr` *is* the canonical trace, and the spec content becomes a
pure list-induction lemma about the canonical trace — no interpreter in
sight. This is the SV analog of the Python lane's
threshold-evaluation-plus-`at_least` discipline, and it scales: a new design
needs one cycle lemma, one trace function, and pure mathematics.

The theorems:

1. `run_deterministic` — same σ, same fuel, same trace (`rfl`; pinned
   because the contract asks to state that `run` is a function). The
   substantive versions are `run_det`/`Runs.functional` (Obs.lean, cross-
   fuel) and the bonus `swap_nba_det`/`counter_det`
   (`Deterministic` — cross-*schedule*).
2. `swap_nba_spec` — ∀ σ: every post-edge snapshot swaps `a`/`b` relative to
   its predecessor (initial state included), for every fuel and stimulus.
3. `race_blk_racy` — explicit σ_src/σ_rev witnesses with the
   Xcelium-verified `(2,2)` vs `(1,1)` traces on the same 1-cycle stimulus
   (kernel evaluation via `decide`; no `native_decide` anywhere), plus
   `race_blk_not_deterministic : ¬ Deterministic raceBlkDesign` — the
   gallery's `sv_witness` shape.
4. `counter_from_reset` — ∀ σ: from any trace snapshot that sampled
   `rst` true, the `count` column *is* the gallery's golden model
   `counterModel : BitVec 8 → Bool → BitVec 8` iterated over the sampled
   resets (`⊑@clk[from rst]` at M0's cycle level). Startup x-collapse
   (`x + 1 = x`) is why the reset hypothesis is load-bearing: before it no
   `BitVec 8` state corresponds to the trace.

The design literals below are hand-built copies of the extracted envelopes;
`Tests.lean` certifies (at elab time, from disk) that these exact literals
are node-for-node equal to `Examples/sv/*.sv.json`.
-/

namespace LeanModels.Sv

/-! ## `sv_simp` — one stack frame of symbolic execution

Mirror of the Python lane's `py_simp` freeze discipline: simp with every
interpreter equation EXCEPT the recursion points, which stay frozen so
threshold/inversion lemmas can be applied to them:

* `combSettle` — the comb-settle fixpoint loop (resolve with
  `combSettle_nil` on comb-free designs, or `combSettle_at_least`);
* `runFrom` — `run`'s stimulus recursion (resolve by induction over the
  stimulus, or `run_at_least`/`Runs.at_least`).

`Design.combIndices`/`Design.edgeIndices` are also left out: for a concrete
design they are decided by a one-line `rfl` lemma (see
`swapNba_edgeIndices`), which keeps goals free of `List.range`/`filter`
noise. Pass design-specific facts (`swapNba_p0`, …) as extras, exactly like
passing the program literal to `py_simp`. -/

open Lean Lean.Parser.Tactic in
/-- `sv_simp [extra, lemmas] (at h)?` — one stack frame's worth of symbolic
execution of the SV interpreter: simp with every interpreter equation except
the frozen recursion points `combSettle` and `runFrom` (see the section
comment above). Pass design-specific facts (`swapNba_p0`, program literals,
branch hypotheses) as extras. -/
macro (name := svSimpTactic) "sv_simp" "[" args:(simpStar <|> simpErase <|> simpLemma),*
    "]" loc:(location)? : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic| set_option linter.unusedSimpArgs false in
      simp [execStmts, execStmt, evalExpr, evalExprs, evalUnaryOp, evalBinOp,
            readSignal, SvState.lookup, SvState.set, SvState.showSignal,
            runCombProcess, combPass, runEdgeProcess, edgePass, commitNba,
            applyInputs, initState, cycleStep, run, Process.isCombPhase,
            Process.isEdgePhase, Design.inputNames, Design.outputNames,
            and_assoc, $extra,*] $(loc)?)

@[inherit_doc svSimpTactic]
macro "sv_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| sv_simp [] $(loc)?)

/-! ## The theorem-bearing M0 designs

Hand-built literals, node-for-node equal to the extracted envelopes
(`Tests.lean` checks this against `Examples/sv/*.sv.json` from disk). All
three have no comb-phase processes, so `combSettle_nil` applies. -/

/-- `Examples/sv/counter.sv`. -/
def counterDesign : Design :=
  { name := "counter"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "rst", width := 1, isInput := true },
      { name := "count", width := 8, isOutput := true }]
    processes := #[
      .alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "count" (.lit (.ofNat 8 0)))
        (some (.nbaAssign "count"
          (.binary .add (.ident "count") (.lit (.ofNat 8 1))))))] }

/-- `Examples/sv/race_blk.sv` (blocking assigns — the race). -/
def raceBlkDesign : Design :=
  { name := "race_blk"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (.ofNat 8 1) },
      { name := "b", width := 8, init := some (.ofNat 8 2) }]
    processes := #[
      .alwaysPlain "clk" (.blockingAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.blockingAssign "b" (.ident "a"))] }

/-- `Examples/sv/swap_nba.sv` (nonblocking assigns — the correct swap). -/
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

theorem counter_combIndices : counterDesign.combIndices = [] := rfl
theorem counter_edgeIndices : counterDesign.edgeIndices = [0] := rfl
theorem counter_p0 :
    counterDesign.processes[0]? =
      some (.alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "count" (.lit (.ofNat 8 0)))
        (some (.nbaAssign "count"
          (.binary .add (.ident "count") (.lit (.ofNat 8 1))))))) := rfl

theorem swapNba_combIndices : swapNbaDesign.combIndices = [] := rfl
theorem swapNba_edgeIndices : swapNbaDesign.edgeIndices = [0, 1] := rfl
theorem swapNba_p0 :
    swapNbaDesign.processes[0]? =
      some (.alwaysPlain "clk" (.nbaAssign "a" (.ident "b"))) := rfl
theorem swapNba_p1 :
    swapNbaDesign.processes[1]? =
      some (.alwaysPlain "clk" (.nbaAssign "b" (.ident "a"))) := rfl

theorem initState_counter :
    initState counterDesign =
      [("clk", LVec.xVec 1), ("rst", LVec.xVec 1), ("count", LVec.xVec 8)] := rfl

theorem initState_swapNba :
    initState swapNbaDesign =
      [("clk", LVec.xVec 1), ("a", LVec.ofNat 8 1), ("b", LVec.ofNat 8 2)] := rfl

/-! ## Applied inputs -/

/-- The value an input port holds after sub-step 1 of a cycle: the stimulus
entry's value if present, else the held previous value. Canonical traces are
written in terms of `appIn`, so they are exact for *every* stimulus (partial
entries included). -/
def appIn (inputs : SvState) (name : String) (old : LVec) : LVec :=
  (SvState.lookup inputs name).getD old

theorem applyInputs_swapNba (inputs : SvState) (c va vb : LVec) :
    applyInputs swapNbaDesign inputs [("clk", c), ("a", va), ("b", vb)] =
      [("clk", appIn inputs "clk" c), ("a", va), ("b", vb)] := by
  show (match SvState.lookup inputs "clk" with
        | some v => SvState.set [("clk", c), ("a", va), ("b", vb)] "clk" v
        | none => [("clk", c), ("a", va), ("b", vb)]) = _
  cases h : SvState.lookup inputs "clk" <;> simp [appIn, h, SvState.set]

theorem applyInputs_counter (inputs : SvState) (c r v : LVec) :
    applyInputs counterDesign inputs [("clk", c), ("rst", r), ("count", v)] =
      [("clk", appIn inputs "clk" c), ("rst", appIn inputs "rst" r), ("count", v)] := by
  show (match SvState.lookup inputs "rst" with
        | some w => SvState.set
            (match SvState.lookup inputs "clk" with
             | some u => SvState.set [("clk", c), ("rst", r), ("count", v)] "clk" u
             | none => [("clk", c), ("rst", r), ("count", v)]) "rst" w
        | none =>
            match SvState.lookup inputs "clk" with
            | some u => SvState.set [("clk", c), ("rst", r), ("count", v)] "clk" u
            | none => [("clk", c), ("rst", r), ("count", v)]) = _
  cases hclk : SvState.lookup inputs "clk" <;> cases hrst : SvState.lookup inputs "rst" <;>
    simp [appIn, hclk, hrst, SvState.set]

/-! ## Theorem 1: `run` is a function of `(design, σ, fuel, stimulus)`

Stated to pin it, per the contract ("should be `rfl`-adjacent"). The
substantive determinism facts are `run_det`/`Runs.functional` (Obs.lean —
cross-fuel at fixed σ) and `swap_nba_det`/`counter_det` below
(cross-schedule). -/

theorem run_deterministic (d : Design) (σ : ScheduleOracle) (fuel : Nat)
    (stim : List SvState) : run d σ fuel stim = run d σ fuel stim := rfl

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

/-! ## Theorem 3: `race_blk` is schedule-dependent -/

/-- The 1-cycle stimulus of the race witnesses (one posedge, `clk` driven
high — the interpreter's cycle semantics does not consult it, but the
stimulus mirrors the harness's). -/
def raceStim : List SvState := [[("clk", LVec.ofNat 1 1)]]

/-- Source order runs `a = b` then `b = a`: `a` picks up `2`, then `b` reads
the ALREADY-UPDATED `a` — `(2, 2)`. Kernel evaluation (`decide`). -/
theorem race_blk_src :
    run raceBlkDesign σ_src 8 raceStim =
      .ok [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 2), ("b", LVec.ofNat 8 2)]] := by
  decide

/-- Reverse order runs `b = a` first — `(1, 1)`. -/
theorem race_blk_rev :
    run raceBlkDesign σ_rev 8 raceStim =
      .ok [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 1), ("b", LVec.ofNat 8 1)]] := by
  decide

/-- **M0 theorem 3** (`docs/sv-design-m0.md`): two legal schedules, same
1-cycle stimulus, different traces — the Xcelium-verified `(2,2)` vs
`(1,1)` race, with σ_src/σ_rev as the concrete witnesses. -/
theorem race_blk_racy :
    ∃ (σ₁ σ₂ : ScheduleOracle) (tr₁ tr₂ : List SvState),
      Runs raceBlkDesign σ₁ raceStim tr₁ ∧ Runs raceBlkDesign σ₂ raceStim tr₂ ∧
      tr₁ ≠ tr₂ :=
  ⟨σ_src, σ_rev,
   [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 2), ("b", LVec.ofNat 8 2)]],
   [[("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 8 1), ("b", LVec.ofNat 8 1)]],
   ⟨8, race_blk_src⟩, ⟨8, race_blk_rev⟩, by decide⟩

/-- The gallery's `race_blk_racy` shape: the blocking-assign race means
`race_blk` is NOT schedule-deterministic. -/
theorem race_blk_not_deterministic : ¬ Deterministic raceBlkDesign := by
  intro h
  have := h σ_src σ_rev raceStim _ _ ⟨8, race_blk_src⟩ ⟨8, race_blk_rev⟩
  exact absurd this (by decide)

/-! ## Theorem 4: `counter` refines its golden model from reset -/

/-- The gallery's golden model (`docs/sv-spec-surface.md` example 2),
verbatim. -/
def counterModel (s : BitVec 8) (rst : Bool) : BitVec 8 :=
  if rst then 0 else s + 1

/-- Iterate the golden model over a list of sampled reset values, emitting
one state per cycle. -/
def counterModelRun (s : BitVec 8) : List Bool → List (BitVec 8)
  | [] => []
  | r :: rs => counterModel s r :: counterModelRun (counterModel s r) rs

/-- The reset value a snapshot *sampled*: `rst` is only ever written by
`applyInputs` (sub-step 1), so the trace snapshot carries exactly the value
the edge process's `if (rst)` saw that cycle. -/
def sampledRst (s : SvState) : Bool :=
  ((SvState.lookup s "rst").getD (LVec.xVec 1)).condTrue

/-- Canonical `counter` trace: `clk`/`rst` follow the stimulus, `count`
steps by `if rst then 0 else count + 1` at `LVec` level (x-collapse
included: from the all-x startup, `x + 1 = x`). -/
def counterTrace (c r v : LVec) : List SvState → List SvState
  | [] => []
  | inp :: rest =>
      let c' := appIn inp "clk" c
      let r' := appIn inp "rst" r
      let v' := if r'.condTrue then LVec.ofNat 8 0 else v.add (LVec.ofNat 8 1)
      [("clk", c'), ("rst", r'), ("count", v')] :: counterTrace c' r' v' rest

/-- Snapshot-shape helpers (the canonical trace has one fixed shape). -/
@[simp] theorem lookup_count_state (c r v : LVec) :
    SvState.lookup [("clk", c), ("rst", r), ("count", v)] "count" = some v := by
  simp [SvState.lookup]

@[simp] theorem sampledRst_state (c r v : LVec) :
    sampledRst [("clk", c), ("rst", r), ("count", v)] = r.condTrue := by
  simp [sampledRst, SvState.lookup]

/-- One symbolic `counter` cycle, ∀ σ (threshold form, slack 8): the edge
phase is a singleton, so σ is irrelevant (`choose_singleton`), and `count`
steps by the reset-mux — stated on the applied (`appIn`) input values, so it
is exact for every stimulus. -/
theorem counter_cycleStep (σ : ScheduleOracle) (inputs : SvState) (c r v : LVec)
    (k : Nat) : ∀ F, 8 ≤ F →
    cycleStep counterDesign σ F inputs [("clk", c), ("rst", r), ("count", v)] k =
      .ok ([("clk", appIn inputs "clk" c), ("rst", appIn inputs "rst" r),
            ("count", if (appIn inputs "rst" r).condTrue then LVec.ofNat 8 0
                      else v.add (LVec.ofNat 8 1))], k + 3) := by
  intro F hF
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  simp only [cycleStep, applyInputs_counter]
  rw [combSettle_nil counter_combIndices]
  simp only [Res.ok_bind, counter_edgeIndices]
  rw [σ.choose_singleton (k + 1) 0]
  by_cases hrst : (appIn inputs "rst" r).condTrue = true
  · sv_simp [counter_p0, hrst]
    rw [combSettle_nil counter_combIndices]
  · sv_simp [counter_p0, hrst]
    rw [combSettle_nil counter_combIndices]

/-- The canonical run, ∀ σ ∀ stimulus (threshold form). -/
theorem counter_runFrom (σ : ScheduleOracle) :
    ∀ (stim : List SvState) (c r v : LVec) (k F : Nat), 8 ≤ F →
      runFrom counterDesign σ F [("clk", c), ("rst", r), ("count", v)] k stim =
        .ok (counterTrace c r v stim) := by
  intro stim
  induction stim with
  | nil => intro c r v k F hF; simp [runFrom, counterTrace]
  | cons inp rest ih =>
    intro c r v k F hF
    simp only [runFrom, counterTrace]
    rw [counter_cycleStep σ inp c r v k F hF]
    simp only [Res.ok_bind]
    rw [ih _ _ _ (k + 3) F hF]
    simp

/-- `counter`'s full trace characterization: for EVERY schedule and EVERY
stimulus, any fuel ≥ 8 completes with the canonical trace (x startup
included). -/
theorem counter_run (σ : ScheduleOracle) (stim : List SvState) :
    ∀ F, 8 ≤ F →
      run counterDesign σ F stim =
        .ok (counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim) := by
  intro F hF
  rw [run, initState_counter]
  exact counter_runFrom σ stim _ _ _ 0 F hF

/-- Non-vacuity: every schedule and stimulus yields the canonical trace. -/
theorem counter_total (σ : ScheduleOracle) (stim : List SvState) :
    Runs counterDesign σ stim
      (counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim) :=
  ⟨8, counter_run σ stim 8 (Nat.le_refl 8)⟩

/-- Bonus: `counter` is schedule-deterministic. -/
theorem counter_det : Deterministic counterDesign := by
  intro σ₁ σ₂ stim tr₁ tr₂ h₁ h₂
  have e₁ := Runs.functional h₁ (counter_total σ₁ stim)
  have e₂ := Runs.functional h₂ (counter_total σ₂ stim)
  rw [e₁, e₂]

private theorem ofNat8_zero : LVec.ofNat 8 0 = LVec.ofBitVec (0 : BitVec 8) := by
  decide

private theorem ofNat8_one : LVec.ofNat 8 1 = LVec.ofBitVec (1 : BitVec 8) := by
  decide

/-- The `LVec`-level count step on an embedded `BitVec` state IS the golden
model — the bridge between interpreter arithmetic and `counterModel`
(`LVec.add_ofBitVec` from the value-core layer). -/
theorem counter_step_ofBitVec (b : BitVec 8) (r : LVec) :
    (if r.condTrue then LVec.ofNat 8 0 else (LVec.ofBitVec b).add (LVec.ofNat 8 1)) =
      LVec.ofBitVec (counterModel b r.condTrue) := by
  cases hr : r.condTrue
  · simp only [Bool.false_eq_true, if_false, counterModel]
    rw [ofNat8_one, LVec.add_ofBitVec]
  · simp only [if_true, counterModel]
    exact ofNat8_zero

/-- Pure list mathematics: from an embedded (`BitVec`) count state, the
canonical trace's `count` column IS the golden-model run over its own
sampled-reset column. -/
theorem counterTrace_model_column :
    ∀ (stim : List SvState) (c r : LVec) (b : BitVec 8),
      (counterTrace c r (LVec.ofBitVec b) stim).map (fun s => SvState.lookup s "count") =
        (counterModelRun b ((counterTrace c r (LVec.ofBitVec b) stim).map sampledRst)).map
          (fun x => some (LVec.ofBitVec x)) := by
  intro stim
  induction stim with
  | nil => intro c r b; rfl
  | cons inp rest ih =>
    intro c r b
    simp only [counterTrace, counter_step_ofBitVec, List.map_cons, sampledRst_state,
      lookup_count_state, counterModelRun, ih]

/-- Pure list mathematics, the from-reset form: from any snapshot that
sampled `rst` true, the `count` column of the canonical trace is `0`
followed by the golden-model run over the subsequent sampled resets. -/
theorem counterTrace_from_reset :
    ∀ (stim : List SvState) (c r v : LVec) (i : Nat) (s : SvState),
      (counterTrace c r v stim)[i]? = some s → sampledRst s = true →
      ((counterTrace c r v stim).drop i).map (fun s' => SvState.lookup s' "count") =
        ((0 : BitVec 8) ::
            counterModelRun 0 (((counterTrace c r v stim).drop (i + 1)).map sampledRst)).map
          (fun b => some (LVec.ofBitVec b)) := by
  intro stim
  induction stim with
  | nil => intro c r v i s hi _; simp [counterTrace] at hi
  | cons inp rest ih =>
    intro c r v i s hi hr
    cases i with
    | zero =>
      simp only [counterTrace, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [sampledRst_state] at hr
      simp only [counterTrace, hr, if_true, List.drop_zero, List.drop_succ_cons,
        List.map_cons, lookup_count_state, ofNat8_zero, List.cons.injEq]
      exact ⟨trivial, counterTrace_model_column rest _ _ 0⟩
    | succ j =>
      simp only [counterTrace, List.getElem?_cons_succ] at hi
      simp only [counterTrace, List.drop_succ_cons]
      exact ih _ _ _ j s hi hr

/-- **M0 theorem 4** (`docs/sv-design-m0.md`): for EVERY schedule, fuel, and
stimulus — from any trace snapshot `i` that sampled `rst` true, `count`
follows the gallery's golden model `counterModel` (`if rst then 0 else
s + 1` on `BitVec 8`) iterated over the sampled reset values of the
remaining cycles:

* snapshot `i` itself shows `count = 0` (reset lands in the same cycle —
  the NBA commits before the trace snapshot), and
* snapshot `i + 1 + j` shows the `j`-th golden-model state.

`sampledRst` reads the trace, not the raw stimulus, because a partial
stimulus entry HOLDS the previous `rst` — the trace records what the edge
actually sampled. The reset hypothesis is load-bearing (`⊑@clk[from rst]`):
before the first reset `count` is all-x (`x + 1 = x`, LRM startup), so no
`BitVec 8` state corresponds to the trace. -/
theorem counter_from_reset (σ : ScheduleOracle) {fuel : Nat}
    {stim tr : List SvState} (h : run counterDesign σ fuel stim = .ok tr)
    {i : Nat} {s : SvState} (hi : tr[i]? = some s) (hr : sampledRst s = true) :
    (tr.drop i).map (fun s' => SvState.lookup s' "count") =
      ((0 : BitVec 8) :: counterModelRun 0 ((tr.drop (i + 1)).map sampledRst)).map
        (fun b => some (LVec.ofBitVec b)) := by
  have htr : tr = counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim :=
    run_det h (counter_run σ stim 8 (Nat.le_refl 8))
  subst htr
  exact counterTrace_from_reset stim _ _ _ i s hi hr

/-! ## Non-vacuity pins (`#guard`)

The canonical traces reproduce the Xcelium-verified outcomes (same values
as `Tests.lean`/the differential harness), so the theorems above are about
the behavior the simulator actually exhibits. -/

-- swap_nba: (1,2) → (2,1) → (1,2)
#guard (swapNbaTrace (LVec.xVec 1) (.ofNat 8 1) (.ofNat 8 2)
    [[("clk", LVec.ofNat 1 1)], [("clk", LVec.ofNat 1 1)]]).map
      (SvState.showSignal · "a") == ["00000010", "00000001"]
#guard (swapNbaTrace (LVec.xVec 1) (.ofNat 8 1) (.ofNat 8 2)
    [[("clk", LVec.ofNat 1 1)], [("clk", LVec.ofNat 1 1)]]).map
      (SvState.showSignal · "b") == ["00000001", "00000010"]

-- counter: x through pre-reset edges (x+1 = x), reset to 0, then count
#guard (counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8)
    [[("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 0)],
     [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 0)],
     [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 1)],
     [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 0)],
     [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 0)]]).map
      (SvState.showSignal · "count")
  == ["xxxxxxxx", "xxxxxxxx", "00000000", "00000001", "00000010"]

-- an rst-less stimulus entry HOLDS reset (sampledRst reads what the edge saw)
#guard (counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8)
    [[("rst", LVec.ofNat 1 1)], []]).map (SvState.showSignal · "count")
  == ["00000000", "00000000"]

end LeanModels.Sv
