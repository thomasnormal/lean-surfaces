import LeanModels.Spice.LoadedRCAC
import LeanModels.Circuit.Surface

namespace Examples.spice.ac_lowpass.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit acLowpassDeck from
  "Examples/spice/ac_lowpass/ac_lowpass.cir"

theorem ac_lowpass_topology :
    acLowpassDeck.toLoadedRCNominal
        "vdrive" "rdrive" "rload" "cload" =
      .ok
        { sourceName := "vdrive"
          seriesName := "rdrive"
          loadName := "rload"
          capacitorName := "cload"
          inputNode := "in"
          outputNode := "out"
          supply := 0
          seriesResistance := 1000
          loadResistance := 2000
          capacitance := 1 / 1000000 } := by
  unfold ElaboratedCircuit.toLoadedRCNominal
  rw [acLowpassDeck_dc_projection]
  change acLowpassDeck_dc.toLoadedRCNominal
      "vdrive" "rdrive" "rload" "cload" = .ok _
  norm_num [LeanModels.Circuit.DCCircuit.toLoadedRCNominal,
    LeanModels.Spice.DCCircuit.toLoadedRCNominal,
    loadedRCTypedNodeName, DCCircuit.isValid, DCDevice.id,
    DCDevice.positive, DCDevice.negative, NodeId.beq_mk, bne,
    acLowpassDeck_dc]
  change Except.ok _ = Except.ok _
  rfl

def acLowpassNominal : LoadedRCNominal :=
  match acLowpassDeck.toLoadedRCNominal
      "vdrive" "rdrive" "rload" "cload" with
  | .ok nominal => nominal
  | .error _ => default

private theorem acLowpassNominal_eq :
    acLowpassNominal =
      { sourceName := "vdrive"
        seriesName := "rdrive"
        loadName := "rload"
        capacitorName := "cload"
        inputNode := "in"
        outputNode := "out"
        supply := 0
        seriesResistance := 1000
        loadResistance := 2000
        capacitance := 1 / 1000000 } := by
  unfold acLowpassNominal
  rw [ac_lowpass_topology]

noncomputable def acLowpassParameter : LoadedRCInstance :=
  { seriesResistance := acLowpassNominal.seriesResistance
    loadResistance := acLowpassNominal.loadResistance
    capacitance := acLowpassNominal.capacitance }

def loadedRCNominalLinear
    (nominal : LoadedRCNominal) : ScalarLinearResidual Rat :=
  { derivativeCoefficient := nominal.capacitance
    valueCoefficient :=
      1 / nominal.seriesResistance + 1 / nominal.loadResistance
    inputCoefficient := -(1 / nominal.seriesResistance) }

def acLowpassLinear : ScalarLinearResidual Rat :=
  loadedRCNominalLinear acLowpassNominal

def acLowpassTransfer : FirstOrderTransfer Rat :=
  { derivativeCoefficient := 1 / 1000000
    denominatorConstant := 3 / 2000
    numerator := 1 / 1000 }

/-- The transfer metadata is an exact view of the source-derived linear
residual, rather than a separately asserted formula. -/
theorem ac_lowpass_transfer :
    HasExactFirstOrderTransfer acLowpassLinear acLowpassTransfer := by
  rw [show acLowpassLinear =
      loadedRCNominalLinear acLowpassNominal by rfl,
    acLowpassNominal_eq]
  norm_num [HasExactFirstOrderTransfer, loadedRCNominalLinear,
    acLowpassTransfer, FirstOrderTransfer.residual]

/-- Routh-Hurwitz for the loaded first-order filter. -/
theorem ac_lowpass_stable :
    FirstOrderStable acLowpassTransfer := by
  norm_num [FirstOrderStable, acLowpassTransfer]

theorem ac_lowpass_pole_negative :
    acLowpassTransfer.pole < 0 :=
  ac_lowpass_stable.pole_negative

/-- The exact AC residual is the real operating-point linearization of the
same source-backed continuous KCL relation. -/
theorem ac_lowpass_linearization :
    ExactLinearizationAt loadedRCDrivenDAE acLowpassParameter 0 0
      acLowpassLinear.toReal := by
  have h :=
    loadedRC_exact_linearization acLowpassParameter
      (by norm_num [acLowpassParameter, acLowpassNominal_eq])
      (by norm_num [acLowpassParameter, acLowpassNominal_eq])
      (by norm_num [acLowpassParameter, acLowpassNominal_eq])
      0
  convert h using 1 <;>
    norm_num [acLowpassLinear, ScalarLinearResidual.toReal,
      loadedRCNominalLinear, loadedRCLinearResidual, acLowpassParameter,
      acLowpassNominal_eq]

def cutoffScenario : ScalarACScenario :=
  { angularFrequency := 1500
    input := GaussianRat.ofRat 1 }

def CutoffAllowed (scenario : ScalarACScenario) : Prop :=
  scenario = cutoffScenario

def acLowpassSourceBinding :
    SourceBinding acLowpassDeck
      (ScalarACBehavior acLowpassLinear) CutoffAllowed :=
  SourceBinding.checked
    (fun circuit =>
      circuit.toLoadedRCNominal "vdrive" "rdrive" "rload" "cload")
    acLowpassDeck acLowpassNominal
    (by
      unfold acLowpassNominal
      rw [ac_lowpass_topology])
    (fun nominal =>
      ScalarACBehavior (loadedRCNominalLinear nominal))
    (fun _nominal => CutoffAllowed)

def cutoffOutput : GaussianRat := ⟨1 / 3, -(1 / 3)⟩

theorem ac_lowpass_realizable :
    RealizableUnder (ScalarACBehavior acLowpassLinear)
      CutoffAllowed := by
  intro scenario hscenario
  subst scenario
  refine ⟨⟨cutoffOutput⟩, (), ?_⟩
  apply GaussianRat.ext <;>
    norm_num [ScalarACBehavior, ScalarLinearResidual.acResidual,
      ScalarLinearResidual.acCoefficient, acLowpassLinear,
      loadedRCNominalLinear, acLowpassNominal_eq,
      cutoffScenario, cutoffOutput, GaussianRat.ofRat, GaussianRat.j,
      GaussianRat.instAdd, GaussianRat.instMul, GaussianRat.instNeg,
      GaussianRat.instZero]

theorem ac_lowpass_exact :
    SafeUnder (ScalarACBehavior acLowpassLinear) CutoffAllowed
      (fun _scenario boundary _internal =>
        boundary.output = cutoffOutput) := by
  intro scenario boundary internal hscenario hbehavior
  subst scenario
  rcases boundary with ⟨⟨real, imaginary⟩⟩
  have hreal := congrArg GaussianRat.re hbehavior
  have himaginary := congrArg GaussianRat.im hbehavior
  norm_num [ScalarACBehavior, ScalarLinearResidual.acResidual,
    ScalarLinearResidual.acCoefficient, acLowpassLinear,
    loadedRCNominalLinear, acLowpassNominal_eq,
    cutoffScenario, GaussianRat.ofRat, GaussianRat.j,
    GaussianRat.instAdd, GaussianRat.instMul, GaussianRat.instNeg,
    GaussianRat.instZero] at hreal himaginary
  change GaussianRat.mk real imaginary =
    GaussianRat.mk (1 / 3) (-(1 / 3))
  rw [GaussianRat.mk.injEq]
  constructor <;> norm_num at hreal himaginary ⊢ <;> linarith

theorem ac_lowpass_magnitude :
    SafeUnder (ScalarACBehavior acLowpassLinear) CutoffAllowed
      (fun _scenario boundary _internal =>
        GaussianRat.normSq boundary.output = 2 / 9) := by
  intro scenario boundary internal hscenario hbehavior
  have houtput :=
    ac_lowpass_exact scenario boundary internal hscenario hbehavior
  rw [houtput]
  norm_num [GaussianRat.normSq, cutoffOutput]

theorem ac_lowpass_determinate :
    DeterminateUnder (ScalarACBehavior acLowpassLinear) CutoffAllowed
      GaussianRat (fun _scenario boundary _internal => boundary.output) := by
  intro scenario hscenario leftBoundary leftInternal
    rightBoundary rightInternal hleft hright
  change leftBoundary.output = rightBoundary.output
  rw [ac_lowpass_exact scenario leftBoundary leftInternal hscenario hleft,
    ac_lowpass_exact scenario rightBoundary rightInternal hscenario hright]

def ACCutoffDomain (scenario : ScalarACScenario)
    (_boundary : ScalarACBoundary) (_internal : Unit) : Prop :=
  scenario = cutoffScenario

theorem ac_lowpass_assurance :
    AssuranceCase acLowpassDeck
      (ScalarACBehavior acLowpassLinear) CutoffAllowed
      acLowpassSourceBinding
      (fun _scenario boundary _internal =>
        boundary.output = cutoffOutput)
      ACCutoffDomain := by
  constructor
  · exact ac_lowpass_exact
  · exact ac_lowpass_realizable
  · intro scenario boundary internal hallowed hbehavior
    exact hallowed

end Examples.spice.ac_lowpass.proof
