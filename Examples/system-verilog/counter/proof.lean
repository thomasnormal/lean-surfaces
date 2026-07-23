/-
Proof module for `Examples/system-verilog/counter/spec.lean` (three-file example layout,
SV lane). M0 theorem 4 of `docs/sv-design-m0.md` — `counter` refines its
golden model from reset — relocated verbatim from the retired
`LeanModels/Sv/Proofs.lean` (raw theorems + canonical-trace lemmas) and
`LeanModels/Sv/Delab.lean` (bridges + surface corollaries). Shared
infrastructure (`sv_simp`, `appIn`, `combSettle_nil`, the schedule-oracle
case splits) lives in `LeanModels/Sv/Obs.lean`.

The proof architecture (same as `Examples/system-verilog/swap_nba/proof.lean`): one
symbolic cycle (`counter_cycleStep`, σ-irrelevant via `choose_singleton`),
one induction over the stimulus (`counter_runFrom`), cross-fuel determinism
(`run_det`) to pin any hypothesis trace to the canonical one, then pure
list mathematics about the canonical trace. Startup x-collapse (`x + 1 =
x`) is why the reset hypothesis is load-bearing: before the first sampled
reset no `BitVec 8` state corresponds to the trace.

The design literal below is a hand-built copy of the extracted envelope;
`spec.lean` certifies (at elab time, from disk) that it is node-for-node
equal to `Examples/system-verilog/counter/counter.sv.json`.
-/
import LeanModels.Sv.Delab

namespace Examples.«system-verilog».counter.proof

open LeanModels.Sv

/-- `Examples/system-verilog/counter/counter.sv`. -/
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

/-! ### Design-index facts (`rfl`; what σ's `choose` gets applied to) -/

theorem counter_combIndices : counterDesign.combIndices = [] := rfl
theorem counter_edgeIndices : counterDesign.edgeIndices = [0] := rfl
theorem counter_p0 :
    counterDesign.processes[0]? =
      some (.alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "count" (.lit (.ofNat 8 0)))
        (some (.nbaAssign "count"
          (.binary .add (.ident "count") (.lit (.ofNat 8 1))))))) := rfl

theorem initState_counter :
    initState counterDesign =
      [("clk", LVec.xVec 1), ("rst", LVec.xVec 1), ("count", LVec.xVec 8)] := rfl

/-! ## Applied inputs -/

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

/-! ## Bridges: raw forms ↔ surface forms

The raw theorems speak `sampledRst`/`counterModelRun`/`"count"`; the
judgments speak `sampled · rst`/`modelRun model`/`Design.firstOutput d`.
Each bridge is one definitional or one-induction lemma, consumed as
`sv_prove` simp extras. -/

/-- `sampledRst` is the generic `sampled` (Surface.lean) at `"rst"`. -/
theorem sampledRst_eq : sampledRst = fun s => sampled s "rst" := rfl

/-- `counterModelRun` is `modelRun` (Surface.lean) at `counterModel`. -/
theorem counterModelRun_eq (s : BitVec 8) (rs : List Bool) :
    counterModelRun s rs = modelRun counterModel s rs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp [counterModelRun, modelRun, ih]

/-- `counter`'s observed column is its (only) output port, `count`. -/
theorem counter_firstOutput : counterDesign.firstOutput = "count" := rfl

/-! ## The surface forms (spec.lean's statements; `sv_prove` corollaries) -/

/-- **M0 theorem 4, surface form** — the gallery's
`counter ⊑@clk[from rst] counterModel`, verbatim: from the first sampled
reset, the sampled `count` column follows the golden model, for every legal
schedule and every abstract pre-reset state. Corollary of
`counter_from_reset` through the three bridges. -/
theorem counter_refines : counterDesign ⊑@clk[from rst] counterModel := by
  sv_prove [counter_from_reset, sampledRst_eq, counterModelRun_eq, counter_firstOutput]

/-- `counter` really runs, under every schedule (= `counter_total`). -/
theorem counter_runs (σ : ScheduleOracle) (stim : List SvState) :
    counterDesign / stim ⇓[σ]
      counterTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 8) stim := by
  sv_prove [counter_total σ stim]

-- `sv_prove`'s Deterministic-from-totality arm re-derives the raw bonus.
example : Deterministic counterDesign := by sv_prove [counter_total]

/-! ## Non-vacuity pins (`#guard`)

The canonical trace reproduces the Xcelium-verified outcomes (same values
as `Tests.lean`/the differential harness). -/

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

end Examples.«system-verilog».counter.proof
