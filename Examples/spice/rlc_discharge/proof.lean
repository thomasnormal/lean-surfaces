import LeanModels.Spice.RLC
import LeanModels.Circuit.Surface

namespace Examples.spice.rlc_discharge.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit rlcDeck from
  "Examples/spice/rlc_discharge/rlc_discharge.cir"

theorem rlc_topology :
    rlcDeck.toRLCNominal "cstore" "lpath" "rload" =
      .ok
        { capacitorName := "cstore"
          inductorName := "lpath"
          resistorName := "rload"
          storageNode := "n1"
          loadNode := "n2"
          capacitance := 1 / 1000000
          inductance := 1 / 1000000
          resistance := 2 } := by
  unfold ElaboratedCircuit.toRLCNominal
  rw [rlcDeck_dc_projection]
  change LeanModels.Spice.DCCircuit.toRLCNominal rlcDeck_dc
      "cstore" "lpath" "rload" = .ok _
  norm_num [LeanModels.Spice.DCCircuit.toRLCNominal, DCCircuit.isValid,
    DCDevice.id, DCDevice.positive, DCDevice.negative,
    NodeId.beq_mk, bne, rlcDeck_dc]
  change Except.ok _ = Except.ok _
  rfl

def rlcNominal : RLCNominal :=
  match rlcDeck.toRLCNominal "cstore" "lpath" "rload" with
  | .ok nominal => nominal
  | .error _ => default

private theorem rlcNominal_eq :
    rlcNominal =
      { capacitorName := "cstore"
        inductorName := "lpath"
        resistorName := "rload"
        storageNode := "n1"
        loadNode := "n2"
        capacitance := 1 / 1000000
        inductance := 1 / 1000000
        resistance := 2 } := by
  unfold rlcNominal
  rw [rlc_topology]

/-- Five volts initially stored on the capacitor, zero inductor current, and
a one millisecond proof horizon. -/
noncomputable def rlcWorld : RLCWorld :=
  rlcNominal.world 5 0 (1 / 1000)

def RLCExampleAllowed (world : RLCWorld) : Prop :=
  world = rlcWorld

def rlcSourceBinding :
    SourceBinding rlcDeck RLCBehavior RLCExampleAllowed :=
  SourceBinding.checked
    (fun circuit =>
      circuit.toRLCNominal "cstore" "lpath" "rload")
    rlcDeck rlcNominal
    (by
      unfold rlcNominal
      rw [rlc_topology])
    (fun _nominal => RLCBehavior)
    (fun nominal world => world = nominal.world 5 0 (1 / 1000))

theorem rlc_admissible : RLCAdmissible rlcWorld := by
  norm_num [rlcWorld, rlcNominal_eq, RLCNominal.world,
    deterministicWorld, RLCAdmissible]

theorem rlc_critical : RLCCriticallyDamped rlcWorld := by
  norm_num [rlcWorld, rlcNominal_eq, RLCNominal.world,
    deterministicWorld, RLCCriticallyDamped]

theorem rlc_initial_current :
    rlcWorld.environment.initialCurrent = 0 := by
  norm_num [rlcWorld, rlcNominal_eq, RLCNominal.world,
    deterministicWorld]

theorem rlc_initial_energy :
    rlcEnergy rlcWorld (rlcCriticalBoundary rlcWorld) 0 =
      (1 / 80000 : ℝ) := by
  norm_num [rlcEnergy, rlcCriticalBoundary, rlcCriticalState,
    rlcWorld, rlcNominal_eq, RLCNominal.world, deterministicWorld]

/-- A continuous physical behavior exists over the requested horizon. -/
theorem rlc_realizable :
    RealizableUnder RLCBehavior RLCExampleAllowed := by
  intro world hworld
  subst world
  exact ⟨rlcCriticalBoundary rlcWorld, (),
    rlc_critical_realizable rlc_admissible rlc_critical
      rlc_initial_current⟩

/-- Every continuous behavior dissipates energy. The theorem allows node
voltages to ring; it proves the physically meaningful energy envelope. -/
theorem rlc_energy_dissipates :
    SafeUnder RLCBehavior RLCExampleAllowed
      (fun world boundary _internal =>
        ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
          rlcEnergy world boundary time ≤ rlcEnergy world boundary 0) := by
  intro world boundary internal hworld hbehavior
  subst world
  intro time htime0 htimeH
  exact LeanModels.Spice.rlc_energy_dissipates
    rlc_admissible hbehavior htime0 htimeH

def RLCEnergyDomain (world : RLCWorld)
    (boundary : RLCBoundary) (_internal : Unit) : Prop :=
  ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
    rlcEnergy world boundary time ≤ rlcEnergy world boundary 0

theorem rlc_domain :
    StaysWithinValidityDomain RLCBehavior RLCExampleAllowed
      RLCEnergyDomain :=
  rlc_energy_dissipates

theorem rlc_assurance :
    AssuranceCase rlcDeck RLCBehavior RLCExampleAllowed
      rlcSourceBinding
      (fun world boundary _internal =>
        ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
          rlcEnergy world boundary time ≤ rlcEnergy world boundary 0)
      RLCEnergyDomain :=
  ⟨rlc_energy_dissipates, rlc_realizable, rlc_domain⟩

end Examples.spice.rlc_discharge.proof
