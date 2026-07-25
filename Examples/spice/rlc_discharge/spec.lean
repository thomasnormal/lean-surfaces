import LeanModels.Python.Surface
import Examples.spice.rlc_discharge.proof

open LeanModels.Circuit LeanModels.Spice
open Examples.spice.rlc_discharge.proof

load_circuit rlcSpecDeck from
  "Examples/spice/rlc_discharge/rlc_discharge.cir"

-- At DC the capacitor is open and the inductor is a short.
#circuit_check rlcSpecDeck dc shows "n1" = (0 : Rat)
#circuit_check rlcSpecDeck dc shows "n2" = (0 : Rat)

theorem rlc_topology :
    rlcSpecDeck.toRLCNominal "cstore" "lpath" "rload" =
      .ok
        { capacitorName := "cstore"
          inductorName := "lpath"
          resistorName := "rload"
          storageNode := "n1"
          loadNode := "n2"
          capacitance := 1 / 1000000
          inductance := 1 / 1000000
          resistance := 2 } := by proofs

theorem rlc_initial_energy :
    rlcEnergy Examples.spice.rlc_discharge.proof.rlcWorld
        (rlcCriticalBoundary
          Examples.spice.rlc_discharge.proof.rlcWorld) 0 =
      (1 / 80000 : ℝ) := by proofs

/-- A paired non-vacuity theorem: the critical-damping trajectory is an
explicit continuous solution of the parsed circuit's vector DAE. -/
theorem rlc_realizable :
    RealizableUnder RLCBehavior
      Examples.spice.rlc_discharge.proof.RLCExampleAllowed := by proofs

/-- For every continuous solution, stored capacitor-plus-inductor energy can
only decrease. This permits ringing while bounding all transient excursions. -/
theorem rlc_energy_dissipates :
    SafeUnder RLCBehavior
      Examples.spice.rlc_discharge.proof.RLCExampleAllowed
      (fun world boundary _internal =>
        ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
          rlcEnergy world boundary time ≤ rlcEnergy world boundary 0) := by proofs

theorem rlc_domain :
    StaysWithinValidityDomain RLCBehavior
      Examples.spice.rlc_discharge.proof.RLCExampleAllowed
      Examples.spice.rlc_discharge.proof.RLCEnergyDomain := by proofs

theorem rlc_assurance :
    AssuranceCase rlcSpecDeck RLCBehavior
      Examples.spice.rlc_discharge.proof.RLCExampleAllowed
      Examples.spice.rlc_discharge.proof.rlcSourceBinding
      (fun world boundary _internal =>
        ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
          rlcEnergy world boundary time ≤ rlcEnergy world boundary 0)
      Examples.spice.rlc_discharge.proof.RLCEnergyDomain := by proofs

#assurance_report rlcSpecDeck using _root_.rlc_assurance
  [_root_.rlc_initial_energy]

#print axioms rlc_realizable
#print axioms rlc_energy_dissipates
#print axioms rlc_domain
#print axioms rlc_assurance
