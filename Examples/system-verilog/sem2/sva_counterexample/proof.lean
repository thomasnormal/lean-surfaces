import LeanModels.Sv.Sva
import LeanModels.Sv.SvaInvariant
import LeanModels.Sv.XMono

namespace Examples.«system-verilog».sem2.sva_counterexample.proof

open LeanModels.Sv

private def check : SvaCheck :=
  { kind := .assert, clock := "clk",
    property := .implies (.atom (.lit true)) (.atom (.lit false)) }

private def counterexample : List SvState :=
  [[("a", LVec.lit "1"), ("b", LVec.lit "0")]]

/-- The E SVA evaluator replays a concrete failing sampled trace. -/
theorem counterexample_eval : SvaCheck.evalEdges counterexample check = .ok false := by
  have ha : boolLogic (LVec.ofLogic .l1) = .l1 := by
    have h : (LVec.ofLogic Logic.l1).condTrue = true := by
      simp only [LVec.ofLogic, LVec.condTrue, ← Array.any_toList]
      simp [XMono.beq_l1]
    simp [boolLogic, h]
  have hb : boolLogic (LVec.ofLogic .l0) = .l0 := by
    have hc : (LVec.ofLogic Logic.l0).condTrue = false := by
      simp only [LVec.ofLogic, LVec.condTrue, ← Array.any_toList]
      apply Bool.eq_false_iff.mpr
      intro h
      have heq : Logic.l0 = Logic.l1 := (XMono.beq_l1 _).mp h
      cases heq
    have hz : (LVec.ofLogic Logic.l0).isKnownZero = true := by
      simp only [LVec.ofLogic, LVec.isKnownZero, ← Array.all_toList]
      simp [XMono.beq_l0]
    simp [boolLogic, hc, hz]
  simp only [check, counterexample, SvaCheck.evalEdges, SvaCheck.step,
    SvaProp.at, SvaSeq.matches, Except.bind, SvaBool.evalChecked, allAt,
    SvaBool.evalLogic,
    signalAt, logicAt, SvState.lookup, Option.map]
  change Except.ok false = Except.ok false
  rfl

theorem counterexample_replay : SvaCheck.evalEdges counterexample check ≠ .ok true := by
  rw [counterexample_eval]
  intro h
  cases h

theorem invariant_route_smoke {q : Bool} {us : List Bool}
    (hr : SafetyTrace SafetySmoke.resetSystem false us q) :
    SafetySmoke.resetSystem.safe q :=
  SafetySmoke.reset_trace_safe hr

end Examples.«system-verilog».sem2.sva_counterexample.proof
