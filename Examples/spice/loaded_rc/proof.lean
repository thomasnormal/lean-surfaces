import LeanModels.Spice.LoadedRC
import LeanModels.Circuit.Surface
import LeanModels.Python.Surface

namespace Examples.spice.loaded_rc.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit loadedRCDeck from "Examples/spice/loaded_rc/loaded_rc.cir"

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
          capacitance := 1 / 1000000 } := by
  unfold ElaboratedCircuit.toLoadedRCNominal
  rw [loadedRCDeck_dc_projection]
  change loadedRCDeck_dc.toLoadedRCNominal
      "vstep" "rdrive" "rload" "cload" = .ok _
  norm_num [LeanModels.Circuit.DCCircuit.toLoadedRCNominal,
    LeanModels.Spice.DCCircuit.toLoadedRCNominal,
    loadedRCTypedNodeName, DCCircuit.isValid, DCDevice.id,
    DCDevice.positive, DCDevice.negative, NodeId.beq_mk, bne,
    loadedRCDeck_dc]
  change Except.ok _ = Except.ok _
  rfl

/-- Nominal parameters are obtained by executing the checked adapter on the
literal extracted deck, rather than re-entering the circuit in Lean. -/
def loadedRCNominal : LoadedRCNominal :=
  match loadedRCDeck.toLoadedRCNominal
      "vstep" "rdrive" "rload" "cload" with
  | .ok nominal => nominal
  | .error _ => default

private theorem loadedRCNominal_eq :
    loadedRCNominal =
      { sourceName := "vstep"
        seriesName := "rdrive"
        loadName := "rload"
        capacitorName := "cload"
        inputNode := "in"
        outputNode := "out"
        supply := 5
        seriesResistance := 1000
        loadResistance := 2000
        capacitance := 1 / 1000000 } := by
  unfold loadedRCNominal
  rw [loaded_rc_topology]

/-- Zero-volt initial capacitor, proved over a 10 ms horizon. -/
noncomputable def loadedRCWorld : LoadedRCWorld :=
  loadedRCNominal.world 0 (1 / 100)

def LoadedRCExampleAllowed (world : LoadedRCWorld) : Prop :=
  world = loadedRCWorld

/-- The transient behavior and its admitted world are obtained from the
checked loaded-RC projection of this exact source deck. -/
def loadedRCSourceBinding :
    SourceBinding loadedRCDeck LoadedRCBehavior LoadedRCExampleAllowed :=
  SourceBinding.checked
    (fun circuit =>
      circuit.toLoadedRCNominal "vstep" "rdrive" "rload" "cload")
    loadedRCDeck loadedRCNominal
    (by
      unfold loadedRCNominal
      rw [loaded_rc_topology])
    (fun _nominal => LoadedRCBehavior)
    (fun nominal world => world = nominal.world 0 (1 / 100))

theorem loaded_rc_admissible : LoadedRCAdmissible loadedRCWorld := by
  norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
    deterministicWorld, LoadedRCAdmissible]

theorem loaded_rc_settling_allowed :
    LoadedRCSettlingAllowed loadedRCWorld := by
  refine ⟨loaded_rc_admissible, by norm_num [loadedRCWorld,
    loadedRCNominal_eq, LoadedRCNominal.world, deterministicWorld], ?_⟩
  norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
    deterministicWorld, loadedRCTarget]

theorem loaded_rc_target :
    loadedRCTarget loadedRCWorld = 10 / 3 := by
  norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
    deterministicWorld, loadedRCTarget]

theorem loaded_rc_rate :
    loadedRCRate loadedRCWorld = 1500 := by
  norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
    deterministicWorld, loadedRCRate]

/-- A continuous DAE solution exists on the full requested horizon. -/
theorem loaded_rc_realizable :
    RealizableUnder LoadedRCBehavior LoadedRCExampleAllowed := by
  intro world hworld
  subst world
  exact loadedRC_realizable loadedRCWorld loaded_rc_admissible

/-- The output trace is unique throughout the horizon. -/
theorem loaded_rc_determinate :
    DeterminateUnder LoadedRCBehavior LoadedRCExampleAllowed
      (ℝ → Option ℝ) LoadedRCHorizonObservation := by
  intro world hworld
  subst world
  exact loadedRC_determinate loadedRCWorld loaded_rc_admissible

/-- Every solution rises from zero toward 10/3 V without undershoot or
overshoot. -/
theorem loaded_rc_no_overshoot :
    SafeUnder LoadedRCBehavior LoadedRCExampleAllowed
      (fun world boundary _internal =>
        Throughout world.environment.horizon fun time =>
          0 ≤ boundary.outputVoltage time ∧
          boundary.outputVoltage time ≤ 10 / 3) := by
  intro world boundary internal hworld hbehavior
  subst world
  intro time htime0 htimeH
  have hbounds :=
    loadedRC_no_overshoot loadedRCWorld boundary internal
      loaded_rc_settling_allowed hbehavior time htime0 htimeH
  have hinitial :
      loadedRCWorld.environment.initialVoltage = 0 := by
    norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
      deterministicWorld]
  rw [hinitial, loaded_rc_target] at hbounds
  exact hbounds

theorem loaded_rc_domain :
    StaysWithinValidityDomain LoadedRCBehavior LoadedRCExampleAllowed
      LoadedRCVoltageDomain := by
  intro world boundary internal hworld hbehavior
  subst world
  exact loadedRC_stays_in_validity_domain loadedRCWorld boundary internal
    loaded_rc_settling_allowed hbehavior

/-- Any physical solution is monotone over the proved horizon. -/
theorem loaded_rc_monotone
    {boundary : LoadedRCBoundary}
    (hbehavior : LoadedRCBehavior loadedRCWorld boundary ())
    {earlier later : ℝ} (hearlier0 : 0 ≤ earlier)
    (htimes : earlier ≤ later)
    (hlaterH : later ≤ loadedRCWorld.environment.horizon) :
    boundary.outputVoltage earlier ≤ boundary.outputVoltage later :=
  loadedRC_monotone loaded_rc_settling_allowed hbehavior
    hearlier0 htimes hlaterH

/-- Explicit continuous-time settling deadline. -/
theorem loaded_rc_settles
    {boundary : LoadedRCBoundary}
    (hbehavior : LoadedRCBehavior loadedRCWorld boundary ())
    {epsilon time : ℝ} (hepsilon : 0 < epsilon)
    (htime0 : 0 ≤ time)
    (htimeH : time ≤ loadedRCWorld.environment.horizon)
    (hdeadline : Real.log ((10 / 3 : ℝ) / epsilon) / 1500 ≤ time) :
    |boundary.outputVoltage time - 10 / 3| ≤ epsilon := by
  have hinitial :
      loadedRCWorld.environment.initialVoltage = 0 := by
    norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
      deterministicWorld]
  have hdeadline' :
      Real.log
          (|loadedRCWorld.environment.initialVoltage -
              loadedRCTarget loadedRCWorld| / epsilon) /
        loadedRCRate loadedRCWorld ≤ time := by
    rw [hinitial, zero_sub, abs_neg, loaded_rc_target, loaded_rc_rate,
      abs_of_nonneg (show (0 : ℝ) ≤ 10 / 3 by norm_num)]
    exact hdeadline
  have hresult :=
    loadedRC_settles_by loaded_rc_admissible hbehavior hepsilon
      htime0 htimeH hdeadline'
  simpa [loaded_rc_target] using hresult

/-- F2 INSTANTIATED.  `loaded_rc_settles` is universally quantified over
`epsilon` and `time` with the settling deadline as a HYPOTHESIS, and nothing
discharged it: the claim reached the top of this deck assumed, not proved.
Here the deck's own 10 ms horizon and a 10 mV tolerance make it concrete, and
the deadline is certified by `log_le_of_le_pow` at split depth 4 -- a rational
inequality, no floating point anywhere in the path. -/
theorem loaded_rc_settled_at_horizon
    {boundary : LoadedRCBoundary}
    (hbehavior : LoadedRCBehavior loadedRCWorld boundary ()) :
    |boundary.outputVoltage (1 / 100) - 10 / 3| ≤ 1 / 100 := by
  have hhorizon : loadedRCWorld.environment.horizon = 1 / 100 := by
    norm_num [loadedRCWorld, loadedRCNominal_eq, LoadedRCNominal.world,
      deterministicWorld]
  have hdeadline : Real.log ((10 / 3 : ℝ) / (1 / 100)) / 1500 ≤ 1 / 100 := by
    have h : Real.log ((10 / 3 : ℝ) / (1 / 100)) ≤ 15 :=
      LeanModels.Circuit.log_le_of_le_pow (by norm_num) (by norm_num) 4
        (by norm_num) (by norm_num)
    linarith
  exact loaded_rc_settles hbehavior (by norm_num) (by norm_num)
    (by rw [hhorizon]) hdeadline

/-- Every executable backward-Euler prefix satisfies the numerical residual. -/
theorem loaded_rc_backward_euler
    {step : ℝ} (hstep : 0 < step) (steps : Nat) :
    loadedRCDAE.BackwardEulerTrajectory loadedRCWorld step steps
      (loadedRCBackwardEulerTrace loadedRCWorld step 0) :=
  loadedRC_backwardEuler_trajectory loaded_rc_admissible hstep steps

/-- Backward Euler is unconditionally no-overshoot for this passive RC
network: no timestep upper bound is required. -/
theorem loaded_rc_backward_euler_no_overshoot
    {step : ℝ} (hstep : 0 < step) (index : Nat) :
    0 ≤ loadedRCBackwardEulerTrace loadedRCWorld step 0 index ∧
    loadedRCBackwardEulerTrace loadedRCWorld step 0 index ≤ 10 / 3 := by
  have hbounds :=
    loadedRCBackwardEulerTrace_bounds loaded_rc_admissible hstep
      (show (0 : ℝ) ≤ loadedRCTarget loadedRCWorld by
        rw [loaded_rc_target]
        norm_num)
      index
  rwa [loaded_rc_target] at hbounds

theorem loaded_rc_assurance :
    AssuranceCase loadedRCDeck LoadedRCBehavior LoadedRCExampleAllowed
      loadedRCSourceBinding
      (fun world boundary _internal =>
        Throughout world.environment.horizon fun time =>
          0 ≤ boundary.outputVoltage time ∧
          boundary.outputVoltage time ≤ 10 / 3)
      LoadedRCVoltageDomain :=
  ⟨loaded_rc_no_overshoot, loaded_rc_realizable, loaded_rc_domain⟩

end Examples.spice.loaded_rc.proof
