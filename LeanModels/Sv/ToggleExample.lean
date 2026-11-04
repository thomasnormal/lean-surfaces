import LeanModels.Sv.Delab

/-!
# `toggle` — walkthrough pointer + shared `Bool` embedding (`LeanModels.Sv`)

The `toggle` T-flip-flop walkthrough that used to live in this file has been
promoted to the three-file example layout, like every other proved SV design:

* `Examples/system-verilog/toggle/toggle.sv` — the design (`always_ff` reset/enable toggle)
* `Examples/system-verilog/toggle/toggle.sv.json` — generated envelope
* `Examples/system-verilog/toggle/spec.lean` — envelope certification, `#sv_check`
  non-vacuity runs, and the surface theorem statements (`:= by proofs`)
* `Examples/system-verilog/toggle/proof.lean` — the real proofs (namespace
  `Examples.«system-verilog».toggle.proof`), relocated from this file verbatim: the certified
  design literal, the ∀σ canonical trace (`toggle_cycleStep` → `toggle_run` →
  `toggle_total`), the golden model
  `fun q (rst, en) => if rst then false else if en then !q else q`, and the
  from-reset refinement `toggle_refines_model`.

This file remains (it is imported by `LeanModels.lean`, keeping the lane
explicitly in `lake build`) as the home of the **`Bool` embedding for 1-bit
signals** — `LVec.ofBool` and its `~`-commutation lemma — which is shared
spec-surface vocabulary: `Examples/system-verilog/toggle/proof.lean` uses it for the golden
model's state, `Examples/system-verilog/xsel/proof.lean` for the known-select theorem. It
also hosts the **comb settle-loop helpers** (`combSettle_step`/
`combSettle_idem`) shared by the comb-phase examples
(`Examples/system-verilog/adder/proof.lean`, `Examples/system-verilog/xsel/proof.lean`). Neither can live
in `Basic.lean`/`Obs.lean` (kept byte-untouched during the concurrent
workflows), and both belong to `LeanModels.Sv`, not to any one example.
-/

namespace LeanModels.Sv

/-- Embed a model state as the 1-bit vector the interpreter computes on
(defined by cases so `ofBool false` is definitionally `ofNat 1 0`, the AST
literal of `q <= 1'b0`). -/
def LVec.ofBool : Bool → LVec
  | false => LVec.ofNat 1 0
  | true => LVec.ofNat 1 1

set_option linter.unusedSimpArgs false in
/-- `~` on an embedded bit is `Bool.not`. Proved at `toList` level:
`LVec.not` is `Array.map`, which does not kernel-reduce, so `decide`/`rfl`
get stuck on it (unlike every other `LVec` operator the 1-bit examples
need). -/
theorem LVec.not_ofBool (b : Bool) : (LVec.ofBool b).not = LVec.ofBool (!b) := by
  cases b <;>
    · refine congrArg LVec.mk (Array.ext' ?_)
      simp [LVec.ofBool, LVec.not, LVec.ofNat, Array.toList_map, Array.toList_ofFn,
        List.ofFn_succ, Logic.not]

set_option linter.unusedSimpArgs false in
/-- `if (·)` truthiness of an embedded bit is the bit itself (`§12.4`
`condTrue` — same `toList`-level proof discipline as `LVec.not_ofBool`,
`Array.any` being no friendlier to the kernel than `Array.map`). -/
theorem LVec.condTrue_ofBool (b : Bool) : (LVec.ofBool b).condTrue = b := by
  cases b <;>
    · simp only [LVec.ofBool, LVec.condTrue, LVec.ofNat, ← Array.any_toList]
      simp [Array.toList_ofFn, List.ofFn_succ]

/-- `if (·)` truthiness of a single 4-state bit: true iff the bit is `l1` —
in particular `x` and `z` select the ELSE branch (X-optimism, §12.4). -/
theorem LVec.condTrue_ofLogic (b : Logic) : (LVec.ofLogic b).condTrue = (b == .l1) := by
  simp only [LVec.ofLogic, LVec.condTrue, ← Array.any_toList]
  cases b <;> simp

/-! ## The comb settle loop (shared by the comb-phase examples)

`sv_simp` (Obs.lean) deliberately freezes `combSettle` — the fixpoint
recursion; these two lemmas are the thaw for designs whose settle pass is
idempotent: unfold one σ-ordered pass, then the fixpoint check, at most
twice. Design-generic — only the per-design `combPass` facts
(`adder_combPass`, `xsel_combPass`) are example-specific. -/

/-- Unfold exactly ONE settle iteration (fuel in successor form, so this
never loops the way `simp [combSettle]` would). -/
theorem combSettle_step (d : Design) (σ : ScheduleOracle) {f : Nat}
    {st st1 : SvState} {k : Nat}
    (hpass : combPass d f st (σ.choose k d.combIndices) = .ok st1) :
    combSettle d σ (f + 1) st k =
      if st1 == st then .ok (st1, k + 1) else combSettle d σ f st1 (k + 1) := by
  simp only [combSettle, hpass, Res.ok_bind]

/-- A settle whose pass is idempotent completes in at most two passes:
pass once (fixpoint check may fail — the pass changed the state), pass
again (now a fixpoint). The invocation counter comes out existential:
which of the two exits is taken depends on the incoming state. -/
theorem combSettle_idem (d : Design) (σ : ScheduleOracle) {f k : Nat}
    {st st1 : SvState}
    (h1 : combPass d (f + 1) st (σ.choose k d.combIndices) = .ok st1)
    (h2 : combPass d f st1 (σ.choose (k + 1) d.combIndices) = .ok st1) :
    ∃ k', combSettle d σ (f + 2) st k = .ok (st1, k') := by
  by_cases hst : st1 = st
  · refine ⟨k + 1, ?_⟩
    rw [show f + 2 = (f + 1) + 1 from rfl, combSettle_step d σ h1]
    subst hst
    simp
  · refine ⟨k + 2, ?_⟩
    rw [show f + 2 = (f + 1) + 1 from rfl, combSettle_step d σ h1]
    rw [beq_eq_false_iff_ne.mpr hst]
    simp only [Bool.false_eq_true, if_false]
    rw [combSettle_step d σ h2]
    simp

end LeanModels.Sv
