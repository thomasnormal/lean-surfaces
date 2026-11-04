import LeanModels.Python.Surface
import Examples.spice.cs_amp.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit csAmp from "Examples/spice/cs_amp/cs_amp.cir"

-- The edge-of-saturation square-law-meets-load-line quadratic
-- 12·Vov² + 5·Vov − 25 = 0 has a perfect-square discriminant BY DESIGN,
-- so the saturation window endpoint 9/4 is exactly rational.
#guard (5 : Int) ^ 2 + 4 * 12 * 25 == 35 ^ 2
#guard (12 : Rat) * (5 / 4) ^ 2 + 5 * (5 / 4) - 25 == 0
-- Exact KCL residual at the designed bias: (VDD − 13/5)/RD = β/2·Vov².
#guard ((5 : Rat) - 13 / 5) / 12000 == 1 / 2500 / 2 * (2 - 1) ^ 2
-- The deck adapter accepts the committed topology.
#guard csAmp.toCommonSourceNominal matches .ok _

theorem cs_amp_topology :
    csAmp.toCommonSourceNominal = .ok
      { inputNode := ⟨2⟩
        outputNode := ⟨1⟩
        supplyNode := ⟨0⟩
        threshold := 1
        beta := 1 / 2500
        drainResistance := 12000 } := by proofs

theorem cs_amp_op {output : ℝ}
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 2 output) :
    output = 13 / 5 := by proofs

theorem cs_amp_op_realizable :
    CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 2 (13 / 5) := by proofs

theorem cs_amp_transfer {input output : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4)
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output) :
    output = 5 - 12 / 5 * (input - 1) ^ 2 := by proofs

theorem cs_amp_saturation {input output : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4)
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output) :
    input - 1 ≤ output := by proofs

theorem cs_amp_dc_exists (input : ℝ) :
    ∃ output,
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 input output := by proofs

theorem cs_amp_transfer_realizable {input : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4) :
    CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input (5 - 12 / 5 * (input - 1) ^ 2) := by proofs

theorem cs_amp_dc_unique {input output₁ output₂ : ℝ}
    (h₁ : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output₁)
    (h₂ : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output₂) :
    output₁ = output₂ := by proofs

theorem cs_amp_cutoff {input output : ℝ}
    (hcut : input ≤ 1)
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output) :
    output = 5 := by proofs

theorem cs_amp_triode {input output : ℝ}
    (hdeep : 9 / 4 < input)
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output) :
    output < input - 1 ∧
    output =
      (24 / 5 * (input - 1) + 1 -
          Real.sqrt ((24 / 5 * (input - 1) + 1) ^ 2 - 48)) /
        (24 / 5) := by proofs

theorem cs_amp_triode_realizable :
    CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (7 / 2) (5 / 12) := by proofs

theorem cs_amp_triode_point {output : ℝ}
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (7 / 2) output) :
    output = 5 / 12 := by proofs

theorem cs_amp_regions {input output : ℝ}
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output) :
    (input ≤ 1 → output = 5) ∧
    (1 < input → input ≤ 9 / 4 → output = 5 - 12 / 5 * (input - 1) ^ 2) ∧
    (9 / 4 < input →
      output =
        (24 / 5 * (input - 1) + 1 -
            Real.sqrt ((24 / 5 * (input - 1) + 1) ^ 2 - 48)) /
          (24 / 5)) := by proofs

theorem cs_amp_regions_realizable (input : ℝ) :
    ∃ output,
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 input output ∧
      (input ≤ 1 → output = 5) ∧
      (1 < input → input ≤ 9 / 4 →
        output = 5 - 12 / 5 * (input - 1) ^ 2) ∧
      (9 / 4 < input →
        output =
          (24 / 5 * (input - 1) + 1 -
              Real.sqrt ((24 / 5 * (input - 1) + 1) ^ 2 - 48)) /
            (24 / 5)) := by proofs

theorem cs_amp_gain {vout : ℝ → ℝ}
    (hsol : ∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 v (vout v)) :
    HasDerivAt vout (-(1 / 2500 * (2 - 1) * 12000)) 2 := by proofs

theorem cs_amp_gain_deriv {vout : ℝ → ℝ}
    (hsol : ∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 v (vout v)) :
    deriv vout 2 = -(24 / 5) := by proofs

theorem cs_amp_gain_realizable :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
        CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
          5 v (vout v)) ∧
      HasDerivAt vout (-(24 / 5)) 2 := by proofs

theorem cs_amp_linearization {d out0 outd : ℝ}
    (hd : |d| ≤ 1 / 4)
    (h0 : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 2 out0)
    (hdd : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (2 + d) outd) :
    outd - out0 + 24 / 5 * d = -(12 / 5) * d ^ 2 := by proofs

theorem cs_amp_linearization_bound {d out0 outd : ℝ}
    (hd : |d| ≤ 1 / 4)
    (h0 : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 2 out0)
    (hdd : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (2 + d) outd) :
    |outd - out0 + 24 / 5 * d| = 12 / 5 * d ^ 2 := by proofs

theorem cs_amp_linearization_le {d out0 outd : ℝ}
    (hd : |d| ≤ 1 / 4)
    (h0 : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 2 out0)
    (hdd : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (2 + d) outd) :
    |outd - out0 + 24 / 5 * d| ≤ 12000 * (1 / 2500) / 2 * d ^ 2 := by proofs

theorem cs_amp_linearization_realizable {d : ℝ} (hd : |d| ≤ 1 / 4) :
    ∃ out0 outd,
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 2 out0 ∧
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 (2 + d) outd ∧
      outd - out0 + 24 / 5 * d = -(12 / 5) * d ^ 2 := by proofs

theorem cs_amp_swing {input output : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4)
    (hdc : CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 input output) :
    5 / 4 ≤ output ∧ output ≤ 22 / 5 := by proofs

theorem cs_amp_swing_max_realizable :
    CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (3 / 2) (22 / 5) := by proofs

theorem cs_amp_swing_min_realizable :
    CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
      5 (9 / 4) (5 / 4) := by proofs

-- Tolerance-box corner arithmetic (kernel-decidable): gain corners of the
-- ±10 % box, worst-corner window check at 41/20, and OP corners.
#guard (11 : Rat) / 25000 * (2 - 9 / 10) * 12000 == 726 / 125
#guard (9 : Rat) / 25000 * (2 - 11 / 10) * 12000 == 486 / 125
#guard (11 : Rat) / 25000 * 12000 / 2 * (41 / 20 - 9 / 10) ^ 2 +
  (41 / 20 - 9 / 10) == 23207 / 5000
#guard (23207 : Rat) / 5000 ≤ 5
#guard (5 : Rat) - 11 / 25000 * 12000 / 2 * (2 - 9 / 10) ^ 2 == 2257 / 1250
#guard (5 : Rat) - 9 / 25000 * 12000 / 2 * (2 - 11 / 10) ^ 2 == 4063 / 1250

theorem cs_amp_gain_interval {vto kp : ℝ} {vout : ℝ → ℝ}
    (hvto : vto ∈ Set.Icc (9 / 10 : ℝ) (11 / 10))
    (hkp : kp ∈ Set.Icc (9 / 25000 : ℝ) (11 / 25000))
    (hsol : ∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
      CommonSourceDC
        { threshold := vto, beta := kp, drainResistance := 12000 }
        5 v (vout v)) :
    HasDerivAt vout (-(kp * (2 - vto) * 12000)) 2 ∧
    -(kp * (2 - vto) * 12000) ∈
      Set.Icc (-(726 / 125) : ℝ) (-(486 / 125)) ∧
    2 - vto ≤ vout 2 ∧
    vout 2 ∈ Set.Icc (2257 / 1250 : ℝ) (4063 / 1250) := by proofs

theorem cs_amp_gain_interval_realizable {vto kp : ℝ}
    (hvto : vto ∈ Set.Icc (9 / 10 : ℝ) (11 / 10))
    (hkp : kp ∈ Set.Icc (9 / 25000 : ℝ) (11 / 25000)) :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
        CommonSourceDC
          { threshold := vto, beta := kp, drainResistance := 12000 }
          5 v (vout v)) ∧
      HasDerivAt vout (-(kp * (2 - vto) * 12000)) 2 := by proofs

theorem cs_amp_gain_interval_tight_fast :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
        CommonSourceDC
          { threshold := 9 / 10, beta := 11 / 25000,
            drainResistance := 12000 }
          5 v (vout v)) ∧
      HasDerivAt vout (-(726 / 125)) 2 := by proofs

theorem cs_amp_gain_interval_tight_slow :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
        CommonSourceDC
          { threshold := 11 / 10, beta := 9 / 25000,
            drainResistance := 12000 }
          5 v (vout v)) ∧
      HasDerivAt vout (-(486 / 125)) 2 := by proofs

#print axioms cs_amp_topology
#print axioms cs_amp_op
#print axioms cs_amp_op_realizable
#print axioms cs_amp_transfer
#print axioms cs_amp_saturation
#print axioms cs_amp_dc_exists
#print axioms cs_amp_transfer_realizable
#print axioms cs_amp_dc_unique
#print axioms cs_amp_cutoff
#print axioms cs_amp_triode
#print axioms cs_amp_triode_realizable
#print axioms cs_amp_triode_point
#print axioms cs_amp_regions
#print axioms cs_amp_regions_realizable
#print axioms cs_amp_gain
#print axioms cs_amp_gain_deriv
#print axioms cs_amp_gain_realizable
#print axioms cs_amp_linearization
#print axioms cs_amp_linearization_bound
#print axioms cs_amp_linearization_le
#print axioms cs_amp_linearization_realizable
#print axioms cs_amp_swing
#print axioms cs_amp_swing_max_realizable
#print axioms cs_amp_swing_min_realizable
#print axioms cs_amp_gain_interval
#print axioms cs_amp_gain_interval_realizable
#print axioms cs_amp_gain_interval_tight_fast
#print axioms cs_amp_gain_interval_tight_slow
