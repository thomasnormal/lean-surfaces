import Examples.spice.loaded_rc.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit loadedRCDeck from "Examples/spice/loaded_rc/loaded_rc.cir"

-- DC non-vacuity: the exact solver treats the capacitor as an open circuit.
#circuit_check loadedRCDeck dc shows "out" = (10 / 3 : Rat)

theorem loaded_rc_topology :
    loadedRCDeck.toLoadedRCNominal "vstep" "rdrive" "rload" "cload" =
      .ok
        { sourceName := "vstep"
          seriesName := "rdrive"
          loadName := "rload"
          capacitorName := "cload"
          inputNode := "in"
          outputNode := "out"
          supply := 5
          seriesResistance := 1000
          loadResistance := 2000
          capacitance := 1 / 1000000 } := by proofs

theorem loaded_rc_realizable :
    RealizableUnder LoadedRCBehavior
      Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed := by proofs

theorem loaded_rc_determinate :
    DeterminateUnder LoadedRCBehavior
      Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed
      (ℝ → Option ℝ) LoadedRCHorizonObservation := by proofs

theorem loaded_rc_no_overshoot :
    SafeUnder LoadedRCBehavior
      Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed
      (fun world boundary _internal =>
        Throughout world.environment.horizon fun time =>
          0 ≤ boundary.outputVoltage time ∧
          boundary.outputVoltage time ≤ 10 / 3) := by proofs

theorem loaded_rc_domain :
    StaysWithinValidityDomain LoadedRCBehavior
      Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed
      LoadedRCVoltageDomain := by proofs

theorem loaded_rc_monotone
    {boundary : LoadedRCBoundary}
    (hbehavior :
      LoadedRCBehavior Examples.spice.loaded_rc.proof.loadedRCWorld boundary ())
    {earlier later : ℝ} (hearlier0 : 0 ≤ earlier)
    (htimes : earlier ≤ later)
    (hlaterH :
      later ≤
        Examples.spice.loaded_rc.proof.loadedRCWorld.environment.horizon) :
    boundary.outputVoltage earlier ≤ boundary.outputVoltage later := by proofs

theorem loaded_rc_settles
    {boundary : LoadedRCBoundary}
    (hbehavior :
      LoadedRCBehavior Examples.spice.loaded_rc.proof.loadedRCWorld boundary ())
    {epsilon time : ℝ} (hepsilon : 0 < epsilon)
    (htime0 : 0 ≤ time)
    (htimeH :
      time ≤ Examples.spice.loaded_rc.proof.loadedRCWorld.environment.horizon)
    (hdeadline : Real.log ((10 / 3 : ℝ) / epsilon) / 1500 ≤ time) :
    |boundary.outputVoltage time - 10 / 3| ≤ epsilon := by proofs

theorem loaded_rc_backward_euler
    {step : ℝ} (hstep : 0 < step) (steps : Nat) :
    loadedRCDAE.BackwardEulerTrajectory
      Examples.spice.loaded_rc.proof.loadedRCWorld step steps
      (loadedRCBackwardEulerTrace
        Examples.spice.loaded_rc.proof.loadedRCWorld step 0) := by proofs

theorem loaded_rc_backward_euler_no_overshoot
    {step : ℝ} (hstep : 0 < step) (index : Nat) :
    0 ≤ loadedRCBackwardEulerTrace
        Examples.spice.loaded_rc.proof.loadedRCWorld step 0 index ∧
    loadedRCBackwardEulerTrace
        Examples.spice.loaded_rc.proof.loadedRCWorld step 0 index ≤
      10 / 3 := by proofs

theorem loaded_rc_assurance :
    AssuranceCase loadedRCDeck LoadedRCBehavior
      Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed
      Examples.spice.loaded_rc.proof.loadedRCSourceBinding
      (fun world boundary _internal =>
        Throughout world.environment.horizon fun time =>
          0 ≤ boundary.outputVoltage time ∧
          boundary.outputVoltage time ≤ 10 / 3)
      LoadedRCVoltageDomain := by proofs

/-- The outer non-vacuity link: the allowed-world set is the singleton
`loadedRCWorld`, so it is inhabited and the case above could have failed. -/
theorem loaded_rc_grounded :
    GroundedUnder Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed :=
  ⟨Examples.spice.loaded_rc.proof.loadedRCWorld, rfl⟩

/-- The existential form, which an empty allowed-world set would refute. -/
theorem loaded_rc_exhibits :
    ExhibitsUnder LoadedRCBehavior
      Examples.spice.loaded_rc.proof.LoadedRCExampleAllowed
      (fun world boundary _internal =>
        Throughout world.environment.horizon fun time =>
          0 ≤ boundary.outputVoltage time ∧
          boundary.outputVoltage time ≤ 10 / 3)
      LoadedRCVoltageDomain :=
  loaded_rc_assurance.exhibits loaded_rc_grounded

/-- F2 INSTANTIATED: the settling deadline is DISCHARGED, not assumed.  At the
deck's own 10 ms horizon the output is within 10 mV of its final value, with
the deadline certified by a rational inequality at split depth 4. -/
theorem loaded_rc_settled_at_horizon
    {boundary : LoadedRCBoundary}
    (hbehavior :
      LoadedRCBehavior Examples.spice.loaded_rc.proof.loadedRCWorld boundary ()) :
    |boundary.outputVoltage (1 / 100) - 10 / 3| ≤ 1 / 100 := by proofs

#assurance_report loadedRCDeck using loaded_rc_assurance
  [loaded_rc_determinate, loaded_rc_monotone, loaded_rc_settles,
    loaded_rc_backward_euler, loaded_rc_backward_euler_no_overshoot]

#print axioms loaded_rc_realizable
#print axioms loaded_rc_determinate
#print axioms loaded_rc_no_overshoot
#print axioms loaded_rc_domain
#print axioms loaded_rc_monotone
#print axioms loaded_rc_settles
#print axioms loaded_rc_backward_euler
#print axioms loaded_rc_backward_euler_no_overshoot
#print axioms loaded_rc_assurance
#print axioms loaded_rc_settled_at_horizon
