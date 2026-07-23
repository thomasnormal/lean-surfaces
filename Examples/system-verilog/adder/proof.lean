/-
Proof module for `Examples/system-verilog/adder/spec.lean` (three-file example layout,
SV lane) — gallery example 1 (`docs/sv-spec-surface.md`): the continuous-
assign 8-bit adder, with the two theorems the gallery names:

* known inputs add (`adder_spec`): embedded `BitVec 8` inputs settle to
  the `BitVec` sum (mod-2^8 wrap inherited from `BitVec` arithmetic);
* the §11.4.3 whole-vector x-collapse (`adder_x_collapse`): ONE `x`/`z`
  bit in either operand makes ALL EIGHT result bits `x` — arithmetic on
  unknowns never carries bit-precisely.

`adder` is the first proved design with a COMB-phase process (counter/
race_blk/swap_nba all have `combIndices = []`), so the new proof content
is the settle loop: one `combPass` computes `s := a + b`, and the pass is
idempotent, so `combSettle` reaches its fixpoint in at most two passes
(`combSettle_idem`, shared in `LeanModels/Sv/ToggleExample.lean` — the
settle-loop analog of `combSettle_nil`).
The oracle-invocation counter `k'` a cycle ends on therefore depends on
whether the pass changed anything, so the cycle lemma packages it
existentially (σ- and k-irrelevance: every phase here is a singleton or
empty ready list).

The rest is the house architecture (`Examples/system-verilog/counter/proof.lean`): one
symbolic cycle, one induction over the stimulus, cross-fuel determinism
(`run_det`) to pin any hypothesis trace to the canonical one, then pure
list mathematics about the canonical trace.

The design literal below is a hand-built copy of the extracted envelope;
`spec.lean` certifies (at elab time, from disk) that it is node-for-node
equal to `Examples/system-verilog/adder/adder.sv.json`.
-/
import LeanModels.Sv.ToggleExample

namespace Examples.«system-verilog».adder.proof

open LeanModels.Sv

/-- `Examples/system-verilog/adder/adder.sv` (continuous assign `s = a + b`),
hand-transcribed. -/
def adderDesign : Design :=
  { name := "adder"
    decls := #[
      { name := "a", width := 8, isInput := true },
      { name := "b", width := 8, isInput := true },
      { name := "s", width := 8, isOutput := true }]
    processes := #[.assign "s" (.binary .add (.ident "a") (.ident "b"))] }

/-! ### Design-index facts (`rfl`; what σ's `choose` gets applied to) -/

theorem adder_inputNames : adderDesign.inputNames = #["a", "b"] := rfl
theorem adder_combIndices : adderDesign.combIndices = [0] := rfl
theorem adder_edgeIndices : adderDesign.edgeIndices = [] := rfl
theorem adder_p0 :
    adderDesign.processes[0]? =
      some (.assign "s" (.binary .add (.ident "a") (.ident "b"))) := rfl

theorem initState_adder :
    initState adderDesign =
      [("a", LVec.xVec 8), ("b", LVec.xVec 8), ("s", LVec.xVec 8)] := rfl

/-! ## Applied inputs -/

theorem applyInputs_adder (inputs : SvState) (a b s : LVec) :
    applyInputs adderDesign inputs [("a", a), ("b", b), ("s", s)] =
      [("a", appIn inputs "a" a), ("b", appIn inputs "b" b), ("s", s)] := by
  cases ha : SvState.lookup inputs "a" <;> cases hb : SvState.lookup inputs "b" <;>
    simp [applyInputs, adder_inputNames, appIn, ha, hb, SvState.set]

/-! ## The settle loop (new for comb designs)

`sv_simp` deliberately freezes `combSettle` (the fixpoint recursion); the
thaw — one σ-ordered pass, then the fixpoint check, at most twice — is the
design-generic `combSettle_step`/`combSettle_idem` pair shared with
`Examples/system-verilog/xsel/proof.lean` (they live in `LeanModels/Sv/ToggleExample.lean`,
the lane's shared-vocabulary file). Only the per-design `combPass` fact
below is adder-specific. -/

/-- One comb pass on the adder state shape computes `s := a + b`
(threshold form, slack 4 — the expression depth). -/
theorem adder_combPass (a b s : LVec) : ∀ g, 4 ≤ g →
    combPass adderDesign g [("a", a), ("b", b), ("s", s)] [0] =
      .ok [("a", a), ("b", b), ("s", a.add b)] := by
  intro g hg
  obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le hg
  rw [Nat.add_comm]
  sv_simp [adder_p0]

/-- The adder settles to `s = a + b` in at most two passes, ∀ σ
(threshold form, slack 8): the comb ready list is the singleton `[0]`, so
σ is irrelevant (`choose_singleton`), and the pass is idempotent. -/
theorem adder_combSettle (σ : ScheduleOracle) (a b s : LVec) (k : Nat) :
    ∀ F, 8 ≤ F → ∃ k',
      combSettle adderDesign σ F [("a", a), ("b", b), ("s", s)] k =
        .ok ([("a", a), ("b", b), ("s", a.add b)], k') := by
  intro F hF
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  refine combSettle_idem adderDesign σ ?_ ?_ <;>
    rw [adder_combIndices, σ.choose_singleton] <;>
      exact adder_combPass _ _ _ _ (by omega)

/-! ## The canonical trace -/

/-- Canonical `adder` trace: `a`/`b` follow the stimulus, `s` settles to
`a + b` at `LVec` level every cycle (whole-vector x-collapse included:
from the all-x startup, `x + x = x` at all 8 bits). -/
def adderTrace (a b : LVec) : List SvState → List SvState
  | [] => []
  | inp :: rest =>
      let a' := appIn inp "a" a
      let b' := appIn inp "b" b
      [("a", a'), ("b", b'), ("s", a'.add b')] :: adderTrace a' b' rest

/-- One symbolic `adder` cycle, ∀ σ (threshold form, slack 8): apply the
inputs, settle (≤ 2 passes), empty edge phase (`choose_nil`), empty NBA
commit, settle again (already a fixpoint — 1 pass). The exit counter `k'`
depends on whether the first settle's pass changed `s`, hence the ∃. -/
theorem adder_cycleStep (σ : ScheduleOracle) (inputs : SvState) (a b s : LVec)
    (k : Nat) : ∀ F, 8 ≤ F → ∃ k',
    cycleStep adderDesign σ F inputs [("a", a), ("b", b), ("s", s)] k =
      .ok ([("a", appIn inputs "a" a), ("b", appIn inputs "b" b),
            ("s", (appIn inputs "a" a).add (appIn inputs "b" b))], k') := by
  intro F hF
  obtain ⟨k1, h1⟩ := adder_combSettle σ (appIn inputs "a" a) (appIn inputs "b" b) s k F hF
  obtain ⟨k2, h2⟩ := adder_combSettle σ (appIn inputs "a" a) (appIn inputs "b" b)
    ((appIn inputs "a" a).add (appIn inputs "b" b)) (k1 + 1) F hF
  refine ⟨k2, ?_⟩
  simp only [cycleStep, applyInputs_adder, h1, Res.ok_bind, adder_edgeIndices,
    σ.choose_nil, edgePass, commitNba, List.foldl_nil, h2]

/-- The canonical run, ∀ σ ∀ stimulus (threshold form). -/
theorem adder_runFrom (σ : ScheduleOracle) :
    ∀ (stim : List SvState) (a b s : LVec) (k F : Nat), 8 ≤ F →
      runFrom adderDesign σ F [("a", a), ("b", b), ("s", s)] k stim =
        .ok (adderTrace a b stim) := by
  intro stim
  induction stim with
  | nil => intro a b s k F hF; simp [runFrom, adderTrace]
  | cons inp rest ih =>
    intro a b s k F hF
    obtain ⟨k', hcyc⟩ := adder_cycleStep σ inp a b s k F hF
    simp only [runFrom, adderTrace]
    rw [hcyc]
    simp only [Res.ok_bind]
    rw [ih _ _ _ k' F hF]
    simp

/-- `adder`'s full trace characterization: for EVERY schedule and EVERY
stimulus, any fuel ≥ 8 completes with the canonical trace (x startup
included). -/
theorem adder_run (σ : ScheduleOracle) (stim : List SvState) :
    ∀ F, 8 ≤ F →
      run adderDesign σ F stim =
        .ok (adderTrace (LVec.xVec 8) (LVec.xVec 8) stim) := by
  intro F hF
  rw [run, initState_adder]
  exact adder_runFrom σ stim _ _ _ 0 F hF

/-- Non-vacuity: every schedule and stimulus yields the canonical trace. -/
theorem adder_total (σ : ScheduleOracle) (stim : List SvState) :
    Runs adderDesign σ stim (adderTrace (LVec.xVec 8) (LVec.xVec 8) stim) :=
  ⟨8, adder_run σ stim 8 (Nat.le_refl 8)⟩

/-- Bonus: `adder` is schedule-deterministic (singleton comb phase). -/
theorem adder_det : Deterministic adderDesign := by
  sv_prove [adder_total]

/-! ## Snapshot shape (pure list mathematics) -/

/-- Every canonical-trace snapshot is a settled `[a', b', s = a' + b']`
state — the M0 rendering of "after combinational settling" (`Sv.comb` is
still design-target; see spec.lean). -/
theorem adderTrace_snapshots :
    ∀ (stim : List SvState) (a b : LVec) (i : Nat) (st : SvState),
      (adderTrace a b stim)[i]? = some st →
      ∃ a' b', st = [("a", a'), ("b", b'), ("s", a'.add b')] := by
  intro stim
  induction stim with
  | nil => intro a b i st h; simp [adderTrace] at h
  | cons inp rest ih =>
    intro a b i st h
    cases i with
    | zero =>
      simp only [adderTrace, List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨_, _, h.symm⟩
    | succ j =>
      simp only [adderTrace, List.getElem?_cons_succ] at h
      exact ih _ _ j st h

/-! ## The two gallery theorems, raw (hypothesis) form -/

/-- **Known inputs add** (raw form): on every completed run, any snapshot
whose settled inputs are embedded `BitVec 8` values shows their `BitVec`
sum on `s` — interpreter arithmetic becomes golden-model arithmetic
through `LVec.add_ofBitVec`. -/
theorem adder_known (σ : ScheduleOracle) {fuel : Nat} {stim tr : List SvState}
    (h : run adderDesign σ fuel stim = .ok tr) (a b : BitVec 8) :
    ∀ (i : Nat) (st : SvState), tr[i]? = some st →
      SvState.lookup st "a" = some (LVec.ofBitVec a) →
      SvState.lookup st "b" = some (LVec.ofBitVec b) →
      SvState.lookup st "s" = some (LVec.ofBitVec (a + b)) := by
  have htr : tr = adderTrace (LVec.xVec 8) (LVec.xVec 8) stim :=
    run_det h (adder_run σ stim 8 (Nat.le_refl 8))
  subst htr
  intro i st hi ha hb
  obtain ⟨a', b', rfl⟩ := adderTrace_snapshots stim _ _ i st hi
  simp only [SvState.lookup] at ha hb ⊢
  simp at ha hb ⊢
  subst ha hb
  exact LVec.add_ofBitVec a b

/-- The §11.4.3 collapse at operator level: ANY `x`/`z` bit in either
operand makes the ENTIRE sum `x` (never a bit-precise carry through
unknowns) — a structural consequence of `LVec.add`'s definition. -/
theorem LVec_add_collapse (va vb : LVec)
    (h : va.allKnown = false ∨ vb.allKnown = false) :
    va.add vb = LVec.xVec (va.arithWidth vb) := by
  rcases h with h | h <;> simp [LVec.add, LVec.toNat?, h]

/-- **Whole-vector x-collapse** (raw form): on every completed run, any
snapshot with an `x`/`z` bit anywhere in either settled 8-bit operand
shows ALL EIGHT `s` bits `x`. -/
theorem adder_x_raw (σ : ScheduleOracle) {fuel : Nat} {stim tr : List SvState}
    (h : run adderDesign σ fuel stim = .ok tr) :
    ∀ (i : Nat) (st : SvState) (va vb : LVec), tr[i]? = some st →
      SvState.lookup st "a" = some va →
      SvState.lookup st "b" = some vb →
      va.width = 8 → vb.width = 8 →
      va.allKnown = false ∨ vb.allKnown = false →
      SvState.lookup st "s" = some (LVec.xVec 8) := by
  have htr : tr = adderTrace (LVec.xVec 8) (LVec.xVec 8) stim :=
    run_det h (adder_run σ stim 8 (Nat.le_refl 8))
  subst htr
  intro i st va vb hi ha hb hwa hwb hx
  obtain ⟨a', b', rfl⟩ := adderTrace_snapshots stim _ _ i st hi
  simp only [SvState.lookup] at ha hb ⊢
  simp at ha hb ⊢
  subst ha hb
  rw [LVec_add_collapse _ _ hx, LVec.arithWidth, hwa, hwb]
  exact congrArg LVec.xVec (Nat.max_self 8)

/-! ## The surface forms (spec.lean's statements; `sv_prove` corollaries) -/

/-- **Gallery example 1, known-inputs form** (`adder_spec`): for every
legal schedule and every stimulus, any settled snapshot whose inputs are
the embedded `a`/`b` shows `s = a + b` on `BitVec 8`. -/
theorem adder_spec (a b : BitVec 8) :
    adderDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState), tr[i]? = some st →
        SvState.lookup st "a" = some (LVec.ofBitVec a) →
        SvState.lookup st "b" = some (LVec.ofBitVec b) →
        SvState.lookup st "s" = some (LVec.ofBitVec (a + b)) := by
  sv_prove [adder_known]

/-- **Gallery example 1, x-collapse form** (`adder_x_collapse`): one
unknown bit anywhere in either operand x-poisons the whole sum
(LRM §11.4.3). -/
theorem adder_x_collapse :
    adderDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState) (va vb : LVec), tr[i]? = some st →
        SvState.lookup st "a" = some va →
        SvState.lookup st "b" = some vb →
        va.width = 8 → vb.width = 8 →
        va.allKnown = false ∨ vb.allKnown = false →
        SvState.lookup st "s" = some (LVec.xVec 8) := by
  sv_prove [adder_x_raw]

/-- `adder` really runs, under every schedule (= `adder_total`). -/
theorem adder_runs (σ : ScheduleOracle) (stim : List SvState) :
    adderDesign / stim ⇓[σ] adderTrace (LVec.xVec 8) (LVec.xVec 8) stim := by
  sv_prove [adder_total σ stim]

/-! ## Non-vacuity pins (`#guard`)

The canonical trace reproduces the Xcelium-verified outcomes (same values
as `Tests.lean`/the differential harness). -/

-- known add and mod-2^8 wrap: 5+3 = 8, 200+100 = 300 ≡ 44
#guard (adderTrace (LVec.xVec 8) (LVec.xVec 8)
    [[("a", LVec.ofNat 8 5), ("b", LVec.ofNat 8 3)],
     [("a", LVec.ofNat 8 200), ("b", LVec.ofNat 8 100)]]).map
      (SvState.showSignal · "s") == ["00001000", "00101100"]

-- ONE x input bit → ALL EIGHT result bits x (§11.4.3)
#guard (adderTrace (LVec.xVec 8) (LVec.xVec 8)
    [[("a", LVec.lit "0000000x"), ("b", LVec.ofNat 8 3)]]).map
      (SvState.showSignal · "s") == ["xxxxxxxx"]

-- held (absent) inputs stay x from startup → s all-x
#guard (adderTrace (LVec.xVec 8) (LVec.xVec 8) [[]]).map
      (SvState.showSignal · "s") == ["xxxxxxxx"]

end Examples.«system-verilog».adder.proof
