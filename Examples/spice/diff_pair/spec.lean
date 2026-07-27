import LeanModels.Python.Surface
import Examples.spice.diff_pair.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit diffPair from "Examples/spice/diff_pair/diff_pair.cir"

-- I_TAIL/β = 1 V² is a perfect square BY DESIGN: balanced overdrive 1 V,
-- balanced outputs 3 V, balance gain −g_m·R_D = −4 exactly.
#guard (1 : Rat) / 2500 / (1 / 2500) == 1
#guard (5 : Rat) - 10000 * (1 / 2500) / 2 == 3
#guard (10000 : Rat) * (1 / 2500) * 1 == 4
-- The 3-4-5 probe: 1 − (6/5)²/4 = (4/5)², so the probe point is rational.
#guard (1 : Rat) - (6 / 5) ^ 2 / 4 == (4 / 5) ^ 2
#guard (5 : Rat) - 10000 * (1 / 2500 / 2 * (4 / 5 + 6 / 5 / 2) ^ 2) == 27 / 25
#guard (5 : Rat) - 10000 * (1 / 2500 / 2 * (4 / 5 - 6 / 5 / 2) ^ 2) == 123 / 25
-- The differential window |d| ≤ 1/2, cm ≤ 21/8 is TIGHT at the corner.
#guard (21 : Rat) / 8 + 1 / 4 + 10000 * (1 / 2500) / 2 * (1 + 1 / 4) ^ 2 == 6
-- The deck adapter accepts the committed topology.
#guard diffPair.toDiffPairNominal matches .ok _

theorem diff_pair_topology :
    diffPair.toDiffPairNominal = .ok
      { inputPNode := ⟨5⟩
        inputNNode := ⟨6⟩
        outputPNode := ⟨1⟩
        outputNNode := ⟨2⟩
        supplyNode := ⟨0⟩
        tailNode := ⟨3⟩
        threshold := 1
        beta := 1 / 2500
        drainResistance := 10000
        tailCurrent := 1 / 2500 } := by proofs

theorem diff_pair_balanced {cm outP outN tail : ℝ} (hcm : cm ≤ 4)
    (hdc : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 cm cm outP outN tail) :
    outP = 3 ∧ outN = 3 ∧ tail = cm - 2 := by proofs

theorem diff_pair_balanced_realizable {cm : ℝ} (hcm : cm ≤ 4) :
    DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 cm cm 3 3 (cm - 2) := by proofs

theorem diff_pair_cm_range (cm : ℝ) (hcm : cm ≤ 4) :
    ∃ outP outN tail,
      DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
        5 cm cm outP outN tail ∧
      outP = 3 ∧ outN = 3 ∧ tail = cm - 2 := by proofs

theorem diff_pair_dc_unique {inputP inputN p₁ n₁ s₁ p₂ n₂ s₂ : ℝ}
    (h₁ : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 inputP inputN p₁ n₁ s₁)
    (h₂ : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 inputP inputN p₂ n₂ s₂) :
    p₁ = p₂ ∧ n₁ = n₂ ∧ s₁ = s₂ := by proofs

theorem diff_pair_gain {vop von vtail : ℝ → ℝ}
    (hsol : ∀ d ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
      DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
        5 (5 / 2 + d / 2) (5 / 2 - d / 2)
        (vop d) (von d) (vtail d)) :
    HasDerivAt (fun d => vop d - von d) (-4) 0 := by proofs

theorem diff_pair_gain_deriv {vop von vtail : ℝ → ℝ}
    (hsol : ∀ d ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
      DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
        5 (5 / 2 + d / 2) (5 / 2 - d / 2)
        (vop d) (von d) (vtail d)) :
    deriv (fun d => vop d - von d) 0 = -4 := by proofs

theorem diff_pair_gain_realizable :
    ∃ vop von vtail : ℝ → ℝ,
      (∀ d ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
        DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
          5 (5 / 2 + d / 2) (5 / 2 - d / 2)
          (vop d) (von d) (vtail d)) ∧
      HasDerivAt (fun d => vop d - von d) (-4) 0 := by proofs

theorem diff_pair_cmrr {cm cm' d : ℝ}
    {outP outN tail outP' outN' tail' : ℝ}
    (hd : |d| ≤ 1 / 2) (hcm : cm ≤ 21 / 8) (hcm' : cm' ≤ 21 / 8)
    (hdc : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 (cm + d / 2) (cm - d / 2) outP outN tail)
    (hdc' : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 (cm' + d / 2) (cm' - d / 2) outP' outN' tail') :
    outP' = outP ∧ outN' = outN ∧ tail' - tail = cm' - cm := by proofs

theorem diff_pair_cmrr_realizable {cm cm' d : ℝ}
    (hd : |d| ≤ 1 / 2) (hcm : cm ≤ 21 / 8) (hcm' : cm' ≤ 21 / 8) :
    ∃ outP outN tail outP' outN' tail',
      DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
        5 (cm + d / 2) (cm - d / 2) outP outN tail ∧
      DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
        5 (cm' + d / 2) (cm' - d / 2) outP' outN' tail' ∧
      outP' = outP ∧ outN' = outN ∧ tail' - tail = cm' - cm := by proofs

theorem diff_pair_vod {d outP outN tail : ℝ} (hd : |d| ≤ 1 / 2)
    (hdc : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 (5 / 2 + d / 2) (5 / 2 - d / 2) outP outN tail) :
    outP - outN = -(4 * d * Real.sqrt (1 - d ^ 2 / 4)) := by proofs

theorem diff_pair_vod_realizable {d : ℝ} (hd : |d| ≤ 1 / 2) :
    ∃ outP outN tail,
      DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
        5 (5 / 2 + d / 2) (5 / 2 - d / 2) outP outN tail ∧
      outP - outN = -(4 * d * Real.sqrt (1 - d ^ 2 / 4)) := by proofs

theorem diff_pair_probe {outP outN tail : ℝ}
    (hdc : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 (17 / 20) (-(7 / 20)) outP outN tail) :
    outP = 27 / 25 ∧ outN = 123 / 25 ∧ tail = -(31 / 20) := by proofs

theorem diff_pair_probe_realizable :
    DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 (17 / 20) (-(7 / 20)) (27 / 25) (123 / 25) (-(31 / 20)) := by proofs

theorem diff_pair_probe_vod {outP outN tail : ℝ}
    (hdc : DiffPairDC Examples.spice.diff_pair.proof.diffPairInstance
      5 (17 / 20) (-(7 / 20)) outP outN tail) :
    outP - outN = -(96 / 25) := by proofs

#print axioms diff_pair_topology
#print axioms diff_pair_balanced
#print axioms diff_pair_balanced_realizable
#print axioms diff_pair_cm_range
#print axioms diff_pair_dc_unique
#print axioms diff_pair_gain
#print axioms diff_pair_gain_deriv
#print axioms diff_pair_gain_realizable
#print axioms diff_pair_cmrr
#print axioms diff_pair_cmrr_realizable
#print axioms diff_pair_vod
#print axioms diff_pair_vod_realizable
#print axioms diff_pair_probe
#print axioms diff_pair_probe_realizable
#print axioms diff_pair_probe_vod
