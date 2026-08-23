import LeanModels.Python.Surface
import Examples.spice.ac_lowpass.proof

open LeanModels.Circuit LeanModels.Spice
open Examples.spice.ac_lowpass.proof

load_circuit acLowpassSpecDeck from
  "Examples/spice/ac_lowpass/ac_lowpass.cir"

#circuit_check acLowpassSpecDeck dc shows "out" = (0 : Rat)

theorem ac_lowpass_linearization :
    ExactLinearizationAt loadedRCDrivenDAE
      Examples.spice.ac_lowpass.proof.acLowpassParameter 0 0
      Examples.spice.ac_lowpass.proof.acLowpassLinear.toReal := by proofs

theorem ac_lowpass_transfer :
    HasExactFirstOrderTransfer
      Examples.spice.ac_lowpass.proof.acLowpassLinear
      Examples.spice.ac_lowpass.proof.acLowpassTransfer := by proofs

theorem ac_lowpass_stable :
    FirstOrderStable
      Examples.spice.ac_lowpass.proof.acLowpassTransfer := by proofs

theorem ac_lowpass_pole_negative :
    Examples.spice.ac_lowpass.proof.acLowpassTransfer.pole < 0 := by proofs

/-- A unit small-signal input at 1500 rad/s has the exact output
`1/3 - j/3`. -/
theorem ac_lowpass_exact :
    SafeUnder
      (ScalarACBehavior
        Examples.spice.ac_lowpass.proof.acLowpassLinear)
      Examples.spice.ac_lowpass.proof.CutoffAllowed
      (fun _scenario boundary _internal =>
        boundary.output =
          Examples.spice.ac_lowpass.proof.cutoffOutput) := by proofs

/-- The squared magnitude is exactly one half of the squared DC gain `4/9`:
this is the loaded filter's -3 dB angular frequency. -/
theorem ac_lowpass_magnitude :
    SafeUnder
      (ScalarACBehavior
        Examples.spice.ac_lowpass.proof.acLowpassLinear)
      Examples.spice.ac_lowpass.proof.CutoffAllowed
      (fun _scenario boundary _internal =>
        GaussianRat.normSq boundary.output = 2 / 9) := by proofs

theorem ac_lowpass_realizable :
    RealizableUnder
      (ScalarACBehavior
        Examples.spice.ac_lowpass.proof.acLowpassLinear)
      Examples.spice.ac_lowpass.proof.CutoffAllowed := by proofs

theorem ac_lowpass_determinate :
    DeterminateUnder
      (ScalarACBehavior
        Examples.spice.ac_lowpass.proof.acLowpassLinear)
      Examples.spice.ac_lowpass.proof.CutoffAllowed
      GaussianRat
      (fun _scenario boundary _internal => boundary.output) := by proofs

theorem ac_lowpass_assurance :
    AssuranceCase acLowpassSpecDeck
      (ScalarACBehavior
        Examples.spice.ac_lowpass.proof.acLowpassLinear)
      Examples.spice.ac_lowpass.proof.CutoffAllowed
      Examples.spice.ac_lowpass.proof.acLowpassSourceBinding
      (fun _scenario boundary _internal =>
        boundary.output =
          Examples.spice.ac_lowpass.proof.cutoffOutput)
      Examples.spice.ac_lowpass.proof.ACCutoffDomain := by proofs

/-- The outer non-vacuity link: the allowed scenario set is the singleton
`cutoffScenario`, so it is inhabited and the case above could have failed. -/
theorem ac_lowpass_grounded :
    GroundedUnder Examples.spice.ac_lowpass.proof.CutoffAllowed :=
  ⟨Examples.spice.ac_lowpass.proof.cutoffScenario, rfl⟩

/-- The existential form, which an empty allowed-scenario set would refute. -/
theorem ac_lowpass_exhibits :
    ExhibitsUnder
      (ScalarACBehavior Examples.spice.ac_lowpass.proof.acLowpassLinear)
      Examples.spice.ac_lowpass.proof.CutoffAllowed
      (fun _scenario boundary _internal =>
        boundary.output =
          Examples.spice.ac_lowpass.proof.cutoffOutput)
      Examples.spice.ac_lowpass.proof.ACCutoffDomain :=
  _root_.ac_lowpass_assurance.exhibits _root_.ac_lowpass_grounded

#assurance_report acLowpassSpecDeck using _root_.ac_lowpass_assurance
  [_root_.ac_lowpass_determinate, _root_.ac_lowpass_linearization,
    _root_.ac_lowpass_transfer, _root_.ac_lowpass_stable,
    _root_.ac_lowpass_pole_negative, _root_.ac_lowpass_magnitude]

#print axioms ac_lowpass_linearization
#print axioms ac_lowpass_transfer
#print axioms ac_lowpass_stable
#print axioms ac_lowpass_pole_negative
#print axioms ac_lowpass_exact
#print axioms ac_lowpass_magnitude
#print axioms ac_lowpass_realizable
#print axioms ac_lowpass_determinate
#print axioms ac_lowpass_assurance
