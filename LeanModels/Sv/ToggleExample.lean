import LeanModels.Sv.Delab
import LeanModels.Sv.Tests

/-!
# `toggle` — a T-flip-flop against its golden model (`LeanModels.Sv`)

New-design walkthrough for `Examples/sv/toggle.sv`:

```systemverilog
module toggle (input logic clk, rst, en, output logic q);
  always_ff @(posedge clk)
    if (rst) q <= 1'b0;
    else if (en) q <= ~q;
endmodule
```

following the recipe of `LeanModels/Sv/Proofs.lean` ("a new design needs one
cycle lemma, one trace function, and pure mathematics"):

* `toggleDesign` — hand-built literal, certified node-for-node equal to the
  extracted envelope `Examples/sv/toggle.sv.json` by the `#eval` below;
* `#sv_check` — concrete runs (reset, toggle, hold, and the pre-reset x);
* `toggle_cycleStep` → `toggle_run` → `toggle_total` — the ∀σ canonical
  trace, by the threshold-fuel + `choose_singleton` script;
* `toggle_from_reset` — the raw from-reset column theorem;
* `toggle_refines_model` — the surface `⊨` form: after any sampled reset,
  `q` follows the golden model
  `fun q (rst, en) => if rst then false else if en then !q else q`
  iterated over the sampled `(rst, en)` inputs, from EVERY abstract pre-reset
  state `q₀`.

**Why `⊨` and not `⊑@clk[from rst]`:** the M0 refinement judgment
(`RefinesFromReset`, Surface.lean) fixes the model input type to one `Bool`
(the sampled reset) per cycle — by design, per its docstring. `toggle`'s
transition function needs the sampled `(rst, en)` *pair*, so the judgment
cannot state it; this file states the same ∀`s₀`-from-reset content through
`⊨`/`Sv.spec` instead, with the reset-collapse argument inlined (the analog
of `RefinesFromReset.of_reset_column`).
-/

namespace LeanModels.Sv

/-! ## The design (extractor-certified literal) -/

/-- `Examples/sv/toggle.sv`, hand-transcribed; the `#eval` below certifies
node-for-node equality with the extracted envelope (same discipline as
`Tests.lean`'s `checkIngest`). -/
def toggleDesign : Design :=
  { name := "toggle"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "rst", width := 1, isInput := true },
      { name := "en", width := 1, isInput := true },
      { name := "q", width := 1, isOutput := true }]
    processes := #[
      .alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "q" (.lit (.ofNat 1 0)))
        (some (.ifStmt (.ident "en")
          (.nbaAssign "q" (.unary .bnot (.ident "q")))
          none)))] }

#eval show IO Unit from do
  let d ← EnvelopeIngest.loadFile "Examples/sv/toggle.sv.json"
  unless d == toggleDesign do
    throw (IO.userError "Examples/sv/toggle.sv.json ≠ toggleDesign")
  unless !d.hasUnsupported do
    throw (IO.userError "toggle envelope has unsupported nodes")

/-! ## Concrete runs (`#sv_check`) -/

-- reset pulse, then en for 3 cycles: q toggles 0, 1, 0, 1
#sv_check toggleDesign
    [[clk := 1, rst := 1], [clk := 1, rst := 0, en := 1],
     [clk := 1, rst := 0, en := 1], [clk := 1, rst := 0, en := 1]]
  shows q = [0, 1, 0, 1]

-- en = 0 holds q (the elseless inner if is a no-op)
#sv_check toggleDesign [[clk := 1, rst := 1], [rst := 0, en := 0], [en := 0]]
  shows q = [0, 0, 0]

-- before the first reset q is x, and ~x = x: reset is load-bearing
#sv_check toggleDesign [[clk := 1, rst := 0, en := 1]] shows q = [x]

/-! ## Design-index facts (`rfl`) and applied inputs -/

theorem toggle_inputNames : toggleDesign.inputNames = #["clk", "rst", "en"] := rfl
theorem toggle_combIndices : toggleDesign.combIndices = [] := rfl
theorem toggle_edgeIndices : toggleDesign.edgeIndices = [0] := rfl
theorem toggle_p0 :
    toggleDesign.processes[0]? =
      some (.alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "q" (.lit (.ofNat 1 0)))
        (some (.ifStmt (.ident "en")
          (.nbaAssign "q" (.unary .bnot (.ident "q")))
          none)))) := rfl

theorem initState_toggle :
    initState toggleDesign =
      [("clk", LVec.xVec 1), ("rst", LVec.xVec 1),
       ("en", LVec.xVec 1), ("q", LVec.xVec 1)] := rfl

/-- Sub-step 1 on the toggle state shape, in `appIn` form (exact for every
stimulus, partial entries included — `Proofs.lean`'s `applyInputs_counter`
pattern). -/
theorem applyInputs_toggle (inputs : SvState) (c r e v : LVec) :
    applyInputs toggleDesign inputs [("clk", c), ("rst", r), ("en", e), ("q", v)] =
      [("clk", appIn inputs "clk" c), ("rst", appIn inputs "rst" r),
       ("en", appIn inputs "en" e), ("q", v)] := by
  cases hclk : SvState.lookup inputs "clk" <;>
    cases hrst : SvState.lookup inputs "rst" <;>
      cases hen : SvState.lookup inputs "en" <;>
        simp [applyInputs, toggle_inputNames, appIn, hclk, hrst, hen, SvState.set]

/-! ## Canonical trace -/

/-- Canonical `toggle` trace: `clk`/`rst`/`en` follow the stimulus, `q`
steps by the reset/toggle mux at `LVec` level (x-collapse included: from the
all-x startup, `~x = x`). -/
def toggleTrace (c r e v : LVec) : List SvState → List SvState
  | [] => []
  | inp :: rest =>
      let c' := appIn inp "clk" c
      let r' := appIn inp "rst" r
      let e' := appIn inp "en" e
      let v' := if r'.condTrue then LVec.ofNat 1 0
                else if e'.condTrue then v.not else v
      [("clk", c'), ("rst", r'), ("en", e'), ("q", v')] :: toggleTrace c' r' e' v' rest

/-- Snapshot-shape helpers (the canonical trace has one fixed shape). -/
@[simp] theorem lookup_q_state (c r e v : LVec) :
    SvState.lookup [("clk", c), ("rst", r), ("en", e), ("q", v)] "q" = some v := by
  simp [SvState.lookup]

@[simp] theorem sampled_rst_state (c r e v : LVec) :
    sampled [("clk", c), ("rst", r), ("en", e), ("q", v)] "rst" = r.condTrue := by
  simp [sampled, SvState.lookup]

@[simp] theorem sampled_en_state (c r e v : LVec) :
    sampled [("clk", c), ("rst", r), ("en", e), ("q", v)] "en" = e.condTrue := by
  simp [sampled, SvState.lookup]

/-! ## The ∀σ canonical run (threshold-fuel script from `Proofs.lean`) -/

/-- One symbolic `toggle` cycle, ∀ σ (threshold form, slack 8): the edge
phase is a singleton, so σ is irrelevant (`choose_singleton`), and `q`
steps by the reset/toggle mux — stated on the applied (`appIn`) input
values, so it is exact for every stimulus. -/
theorem toggle_cycleStep (σ : ScheduleOracle) (inputs : SvState) (c r e v : LVec)
    (k : Nat) : ∀ F, 8 ≤ F →
    cycleStep toggleDesign σ F inputs [("clk", c), ("rst", r), ("en", e), ("q", v)] k =
      .ok ([("clk", appIn inputs "clk" c), ("rst", appIn inputs "rst" r),
            ("en", appIn inputs "en" e),
            ("q", if (appIn inputs "rst" r).condTrue then LVec.ofNat 1 0
                  else if (appIn inputs "en" e).condTrue then v.not else v)],
           k + 3) := by
  intro F hF
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  simp only [cycleStep, applyInputs_toggle]
  rw [combSettle_nil toggle_combIndices]
  simp only [Res.ok_bind, toggle_edgeIndices]
  rw [σ.choose_singleton (k + 1) 0]
  by_cases hrst : (appIn inputs "rst" r).condTrue = true
  · sv_simp [toggle_p0, hrst]
    rw [combSettle_nil toggle_combIndices]
  · by_cases hen : (appIn inputs "en" e).condTrue = true
    · sv_simp [toggle_p0, hrst, hen]
      rw [combSettle_nil toggle_combIndices]
    · sv_simp [toggle_p0, hrst, hen]
      rw [combSettle_nil toggle_combIndices]

/-- The canonical run, ∀ σ ∀ stimulus (threshold form). -/
theorem toggle_runFrom (σ : ScheduleOracle) :
    ∀ (stim : List SvState) (c r e v : LVec) (k F : Nat), 8 ≤ F →
      runFrom toggleDesign σ F [("clk", c), ("rst", r), ("en", e), ("q", v)] k stim =
        .ok (toggleTrace c r e v stim) := by
  intro stim
  induction stim with
  | nil => intro c r e v k F hF; simp [runFrom, toggleTrace]
  | cons inp rest ih =>
    intro c r e v k F hF
    simp only [runFrom, toggleTrace]
    rw [toggle_cycleStep σ inp c r e v k F hF]
    simp only [Res.ok_bind]
    rw [ih _ _ _ _ (k + 3) F hF]
    simp

/-- `toggle`'s full trace characterization: for EVERY schedule and EVERY
stimulus, any fuel ≥ 8 completes with the canonical trace (x startup
included). -/
theorem toggle_run (σ : ScheduleOracle) (stim : List SvState) :
    ∀ F, 8 ≤ F →
      run toggleDesign σ F stim =
        .ok (toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) stim) := by
  intro F hF
  rw [run, initState_toggle]
  exact toggle_runFrom σ stim _ _ _ _ 0 F hF

/-- Non-vacuity: every schedule and stimulus yields the canonical trace. -/
theorem toggle_total (σ : ScheduleOracle) (stim : List SvState) :
    Runs toggleDesign σ stim
      (toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) stim) :=
  ⟨8, toggle_run σ stim 8 (Nat.le_refl 8)⟩

/-- `toggle` really runs, in `⇓[σ]` surface form. -/
theorem toggle_runs (σ : ScheduleOracle) (stim : List SvState) :
    toggleDesign / stim ⇓[σ]
      toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) stim := by
  sv_prove [toggle_total σ stim]

/-- Bonus: `toggle` is schedule-deterministic (single edge process). -/
theorem toggle_det : Deterministic toggleDesign := by
  sv_prove [toggle_total]

/-! ## The golden model -/

/-- The task's transition function, verbatim: from state `q`, a cycle
sampling `(rst, en)` resets, toggles, or holds. -/
def toggleModel : Bool → Bool × Bool → Bool :=
  fun q (rst, en) => if rst then false else if en then !q else q

/-- Iterate the golden model over the sampled `(rst, en)` inputs, one state
per cycle (the two-input analog of `Surface.lean`'s `modelRun`). -/
def toggleModelRun (q : Bool) : List (Bool × Bool) → List Bool
  | [] => []
  | i :: rest => toggleModel q i :: toggleModelRun (toggleModel q i) rest

/-- Embed a model state as the 1-bit vector the interpreter computes on
(defined by cases so `ofBool false` is definitionally `ofNat 1 0`, the AST
literal of `q <= 1'b0`). -/
def LVec.ofBool : Bool → LVec
  | false => LVec.ofNat 1 0
  | true => LVec.ofNat 1 1

set_option linter.unusedSimpArgs false in
/-- `~` on an embedded bit is `Bool.not`. Proved at `toList` level:
`LVec.not` is `Array.map`, which does not kernel-reduce, so `decide`/`rfl`
get stuck on it (unlike every other `LVec` operator this file needs). -/
theorem LVec.not_ofBool (b : Bool) : (LVec.ofBool b).not = LVec.ofBool (!b) := by
  cases b <;>
    · refine congrArg LVec.mk (Array.ext' ?_)
      simp [LVec.ofBool, LVec.not, LVec.ofNat, Array.toList_map, Array.toList_ofFn,
        List.ofFn_succ, Logic.not]

/-- The `LVec`-level `q` step on an embedded `Bool` state IS the golden
model (the `counter_step_ofBitVec` analog). -/
theorem toggle_step_ofBool (b : Bool) (r e : LVec) :
    (if r.condTrue then LVec.ofNat 1 0
     else if e.condTrue then (LVec.ofBool b).not else LVec.ofBool b) =
      LVec.ofBool (toggleModel b (r.condTrue, e.condTrue)) := by
  rw [LVec.not_ofBool]
  cases hr : r.condTrue <;> cases he : e.condTrue <;> cases b <;> decide

/-- Pure list mathematics: from an embedded (`Bool`) `q` state, the
canonical trace's `q` column IS the golden-model run over its own sampled
`(rst, en)` columns. -/
theorem toggleTrace_model_column :
    ∀ (stim : List SvState) (c r e : LVec) (b : Bool),
      (toggleTrace c r e (LVec.ofBool b) stim).map (fun s => SvState.lookup s "q") =
        (toggleModelRun b ((toggleTrace c r e (LVec.ofBool b) stim).map
            (fun s => (sampled s "rst", sampled s "en")))).map
          (fun x => some (LVec.ofBool x)) := by
  intro stim
  induction stim with
  | nil => intro c r e b; rfl
  | cons inp rest ih =>
    intro c r e b
    simp only [toggleTrace, toggle_step_ofBool, List.map_cons, sampled_rst_state,
      sampled_en_state, lookup_q_state, toggleModelRun, ih]

/-- Pure list mathematics, the from-reset form: from any snapshot that
sampled `rst` true, the `q` column of the canonical trace is `false`
followed by the golden-model run over the subsequent sampled inputs. -/
theorem toggleTrace_from_reset :
    ∀ (stim : List SvState) (c r e v : LVec) (i : Nat) (s : SvState),
      (toggleTrace c r e v stim)[i]? = some s → sampled s "rst" = true →
      ((toggleTrace c r e v stim).drop i).map (fun s' => SvState.lookup s' "q") =
        (false :: toggleModelRun false
            (((toggleTrace c r e v stim).drop (i + 1)).map
              (fun s' => (sampled s' "rst", sampled s' "en")))).map
          (fun b => some (LVec.ofBool b)) := by
  intro stim
  induction stim with
  | nil => intro c r e v i s hi _; simp [toggleTrace] at hi
  | cons inp rest ih =>
    intro c r e v i s hi hr
    cases i with
    | zero =>
      simp only [toggleTrace, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [sampled_rst_state] at hr
      simp only [toggleTrace, hr, if_true, List.drop_zero, List.drop_succ_cons,
        List.map_cons, lookup_q_state, List.cons.injEq]
      exact ⟨rfl, toggleTrace_model_column rest _ _ _ false⟩
    | succ j =>
      simp only [toggleTrace, List.getElem?_cons_succ] at hi
      simp only [toggleTrace, List.drop_succ_cons]
      exact ih _ _ _ _ j s hi hr

/-- **Raw from-reset theorem** (the `counter_from_reset` analog): for EVERY
schedule, fuel, and stimulus — from any trace snapshot `i` that sampled
`rst` true, `q` follows the golden model iterated over the sampled
`(rst, en)` inputs of the remaining cycles (snapshot `i` itself shows
`q = 0`; the reset hypothesis is load-bearing — before it `q` is all-x,
`~x = x`). -/
theorem toggle_from_reset (σ : ScheduleOracle) {fuel : Nat}
    {stim tr : List SvState} (h : run toggleDesign σ fuel stim = .ok tr)
    {i : Nat} {s : SvState} (hi : tr[i]? = some s) (hr : sampled s "rst" = true) :
    (tr.drop i).map (fun s' => SvState.lookup s' "q") =
      (false :: toggleModelRun false ((tr.drop (i + 1)).map
          (fun s' => (sampled s' "rst", sampled s' "en")))).map
        (fun b => some (LVec.ofBool b)) := by
  have htr : tr = toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) stim :=
    run_det h (toggle_run σ stim 8 (Nat.le_refl 8))
  subst htr
  exact toggleTrace_from_reset stim _ _ _ _ i s hi hr

/-! ## The surface theorem -/

/-- **The ∀-schedule refinement, surface form**: under every legal schedule
and every stimulus, from any snapshot that sampled `rst` true, the `q`
column follows `toggleModel` iterated over the sampled `(rst, en)` columns —
starting from EVERY abstract state `q₀` (reset erases the state; before the
first reset nothing is claimed, and indeed `q` is x there). This is exactly
`⊑@clk[from rst]`'s content generalized to a two-input model — the M0
`RefinesFromReset` judgment cannot state it (its model input is the sampled
reset `Bool` alone), so it is stated through `⊨`. -/
theorem toggle_refines_model :
    toggleDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (s : SvState), tr[i]? = some s → sampled s "rst" = true →
        ∀ q₀ : Bool,
          (tr.drop i).map (fun s' => SvState.lookup s' "q") =
            (toggleModelRun q₀ ((tr.drop i).map
                (fun s' => (sampled s' "rst", sampled s' "en")))).map
              (fun b => some (LVec.ofBool b)) := by
  refine Models.of_run fun σ fuel stim tr hrun => ?_
  intro i s hi hr q₀
  have hcol := toggle_from_reset σ hrun hi hr
  obtain ⟨hlt, hs⟩ := List.getElem?_eq_some_iff.mp hi
  have hdrop : tr.drop i = s :: tr.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hs]
  rw [hdrop] at hcol ⊢
  simp only [List.map_cons, hr, toggleModelRun, toggleModel] at hcol ⊢
  simpa using hcol

/-! ## Non-vacuity pins (`#guard`) — the canonical trace shows the
`#sv_check` outcomes, so the theorems above describe real behavior -/

private def tglCyc (r e : Nat) : SvState :=
  [("clk", LVec.ofNat 1 1), ("rst", LVec.ofNat 1 r), ("en", LVec.ofNat 1 e)]

#guard (toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1)
    [tglCyc 1 0, tglCyc 0 1, tglCyc 0 1, tglCyc 0 1]).map
      (SvState.showSignal · "q") == ["0", "1", "0", "1"]

-- pre-reset the q column is x (~x = x), so no Bool state corresponds
#guard (toggleTrace (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1)
    [tglCyc 0 1, tglCyc 0 1]).map (SvState.showSignal · "q") == ["x", "x"]

-- the model run itself: reset, toggle, toggle, toggle
#guard toggleModelRun true [(true, false), (false, true), (false, true), (false, true)]
  == [false, true, false, true]

/-! ## Axiom pins (standard axioms only — no sorry, no native_decide) -/

/--
info: 'LeanModels.Sv.toggle_refines_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toggle_refines_model

/--
info: 'LeanModels.Sv.toggle_from_reset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toggle_from_reset

/-- info: 'LeanModels.Sv.toggle_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toggle_det

end LeanModels.Sv
