import LeanModels.Python.Surface
import Examples.spice.robust_divider.proof

open LeanModels.Circuit

load_circuit robustDivider from
  "Examples/spice/robust_divider/robust_divider.cir"

#circuit_check robustDivider dc shows "out" = (10 / 3 : Rat)

abbrev robustDividerOutput := (node! robustDivider "out").id

/-- Every allowed fabricated instance and supply run has a physical operating
point. This theorem prevents the safety result from being vacuous. -/
theorem robust_divider_realizable :
    RealizableUnder (RealDCBehavior robustDivider)
      Examples.spice.robust_divider.proof.RobustDividerAllowed := by proofs

/-- For all independent 5% supply and resistor corners, every admissible
operating point lies in this tight output interval. -/
theorem robust_divider_safe :
    SafeUnder (RealDCBehavior robustDivider)
      Examples.spice.robust_divider.proof.RobustDividerAllowed
      (fun _world assignment _internal =>
        (361 / 118 : ℝ) ≤ assignment.voltage robustDividerOutput ∧
        assignment.voltage robustDividerOutput ≤ 441 / 122) := by proofs

theorem robust_divider_bounded_noise
    {world : DCRunWorld} {assignment : RealDCAssignment}
    {noise : ℝ}
    (hallowed :
      Examples.spice.robust_divider.proof.RobustDividerAllowed world)
    (hbehavior : RealDCSatisfies robustDivider world assignment)
    (hnoise : BoundedNoise (1 / 100) noise) :
    (361 / 118 : ℝ) - 1 / 100 ≤
        assignment.voltage robustDividerOutput + noise ∧
      assignment.voltage robustDividerOutput + noise ≤
        441 / 122 + 1 / 100 := by proofs

theorem divider_corner_almost_sure :
    FiniteAlmostSure
      Examples.spice.robust_divider.proof.DividerCornerDistribution
      Examples.spice.robust_divider.proof.DividerSafeWorld := by proofs

theorem divider_corner_yield :
    finiteYield
      Examples.spice.robust_divider.proof.DividerCornerDistribution
      Examples.spice.robust_divider.proof.DividerSafeWorld = 1 := by proofs

/-- The observed output is unique even though the relational semantics does
not globally assume determinacy. -/
theorem robust_divider_determinate :
    DeterminateUnder (RealDCBehavior robustDivider)
      Examples.spice.robust_divider.proof.RobustDividerAllowed ℝ
      (fun _world assignment _internal =>
        assignment.voltage robustDividerOutput) := by proofs

/-- Every admissible behavior stays inside the voltage domain on which this
example's component envelope is asserted. -/
theorem robust_divider_domain :
    StaysWithinValidityDomain (RealDCBehavior robustDivider)
      Examples.spice.robust_divider.proof.RobustDividerAllowed
      Examples.spice.robust_divider.proof.DividerVoltageDomain := by proofs

theorem robust_divider_assurance :
    AssuranceCase robustDivider (RealDCBehavior robustDivider)
      Examples.spice.robust_divider.proof.RobustDividerAllowed
      (SourceBinding.identity robustDivider
        (fun _circuit => RealDCBehavior robustDivider)
        (fun _circuit =>
          Examples.spice.robust_divider.proof.RobustDividerAllowed))
      (fun _world assignment _internal =>
        (361 / 118 : ℝ) ≤
            assignment.voltage robustDividerOutput ∧
          assignment.voltage robustDividerOutput ≤ 441 / 122)
      Examples.spice.robust_divider.proof.DividerVoltageDomain := by proofs

#assurance_report robustDivider using robust_divider_assurance
  [robust_divider_determinate, robust_divider_bounded_noise,
    divider_corner_almost_sure, divider_corner_yield]

#print axioms robust_divider_realizable
#print axioms robust_divider_safe
#print axioms robust_divider_bounded_noise
#print axioms divider_corner_almost_sure
#print axioms divider_corner_yield
#print axioms robust_divider_determinate
#print axioms robust_divider_domain
#print axioms robust_divider_assurance
