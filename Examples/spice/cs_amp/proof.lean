import LeanModels.Spice.CommonSource
import LeanModels.Circuit.Surface

namespace Examples.spice.cs_amp.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit csAmp from "Examples/spice/cs_amp/cs_amp.cir"

/-! Concrete kernel-decidable checks of the deck-header design arithmetic. -/

-- The edge-of-saturation square-law-meets-load-line quadratic
-- 12·Vov² + 5·Vov − 25 = 0 has a perfect-square discriminant BY DESIGN.
#guard (5 : Int) ^ 2 + 4 * 12 * 25 == 35 ^ 2
-- Its positive root is exactly Vov* = 5/4, so v_hi = VTO + 5/4 = 9/4.
#guard (12 : Rat) * (5 / 4) ^ 2 + 5 * (5 / 4) - 25 == 0
-- Exact KCL residual at the designed bias: (VDD − 13/5)/RD = β/2·Vov².
#guard ((5 : Rat) - 13 / 5) / 12000 == 1 / 2500 / 2 * (2 - 1) ^ 2
-- The derived transfer curve at the stated window endpoints.
#guard (5 : Rat) - 12 / 5 * (3 / 2 - 1) ^ 2 == 22 / 5
#guard (5 : Rat) - 12 / 5 * (9 / 4 - 1) ^ 2 == 5 / 4
-- Deep-triode probe input 7/2 (Vov = 5/2): the triode quadratic's
-- discriminant (24/5·Vov + 1)² − 48 = 121 = 11² is a perfect square BY
-- DESIGN, so the clipped output 5/12 is exactly rational.
#guard ((24 : Rat) / 5 * (5 / 2) + 1) ^ 2 - 48 == 11 ^ 2
-- Exact triode KCL residual at the probe: (5 − 5/12)/RD = β(Vov·v − v²/2).
#guard ((5 : Rat) - 5 / 12) / 12000 ==
  1 / 2500 * (5 / 2 * (5 / 12) - (5 / 12) ^ 2 / 2)
-- Gain design arithmetic at the bias: gm·RD = β·(V_in0 − VTO)·RD = 24/5.
#guard (1 : Rat) / 2500 * (2 - 1) * 12000 == 24 / 5
-- Second-order (linearization) coefficient: RD·KP/2 = 12/5.
#guard (12000 : Rat) * (1 / 2500) / 2 == 12 / 5
-- The deck adapter accepts the committed topology.
#guard csAmp.toCommonSourceNominal matches .ok _

/-- The checked adapter is the only path from the source deck to these
nominal parameters. -/
theorem cs_amp_topology :
    csAmp.toCommonSourceNominal = .ok
      { inputNode := ⟨2⟩
        outputNode := ⟨1⟩
        supplyNode := ⟨0⟩
        threshold := 1
        beta := 1 / 2500
        drainResistance := 12000 } := by
  circuit_reduce

def csAmpNominal : CommonSourceNominal :=
  match csAmp.toCommonSourceNominal with
  | .ok nominal => nominal
  | .error _ => default

theorem csAmpNominal_eq :
    csAmpNominal =
      { inputNode := ⟨2⟩
        outputNode := ⟨1⟩
        supplyNode := ⟨0⟩
        threshold := 1
        beta := 1 / 2500
        drainResistance := 12000 } := by
  unfold csAmpNominal
  rw [cs_amp_topology]

/-- Real-valued fabricated instance recovered from the deck through the
checked adapter. -/
noncomputable def csAmpInstance : CommonSourceInstance :=
  csAmpNominal.instance

theorem csAmpInstance_eq :
    csAmpInstance =
      { threshold := 1, beta := 1 / 2500, drainResistance := 12000 } := by
  unfold csAmpInstance
  rw [csAmpNominal_eq]
  simp only [CommonSourceNominal.instance, CommonSourceInstance.mk.injEq]
  norm_num

/-- (a) The designed operating point, DERIVED from the device equations
and KCL: at the designed bias `V_in0 = 2` every DC state has the drain at
exactly 13/5 V. -/
theorem cs_amp_op {output : ℝ}
    (hdc : CommonSourceDC csAmpInstance 5 2 output) :
    output = 13 / 5 := by
  rw [csAmpInstance_eq] at hdc
  have hop := commonSource_dc_op (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hdc
  rw [hop]
  norm_num

/-- (b) Realizability twin for the operating point: the derived voltage is
an actual DC state of the physics relation. -/
theorem cs_amp_op_realizable :
    CommonSourceDC csAmpInstance 5 2 (13 / 5) := by
  rw [csAmpInstance_eq]
  refine ⟨by norm_num, ?_⟩
  norm_num [mos1ForwardCurrent]

/-- The full transfer function on the window [3/2, 9/4], derived from
KCL. Its derivative at the designed bias is the small-signal gain −24/5,
which the gain campaign states as a literal derivative. -/
theorem cs_amp_transfer {input output : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4)
    (hdc : CommonSourceDC csAmpInstance 5 input output) :
    output = 5 - 12 / 5 * (input - 1) ^ 2 := by
  rw [csAmpInstance_eq] at hdc
  have hop := commonSource_dc_op (by norm_num) (by norm_num)
    (by norm_num; linarith)
    (by
      norm_num
      nlinarith [mul_nonneg
        (by linarith : (0 : ℝ) ≤ 5 - 4 * (input - 1))
        (by linarith : (0 : ℝ) ≤ 3 * (input - 1) + 5)])
    hdc
  rw [hop]
  norm_num

/-- (c) Saturation over the stated input interval [3/2, 9/4]: any DC
state has the device in saturation (`V_ds ≥ V_ov`). This is the validity
domain for the gain work; its upper endpoint 9/4 is the exact rational
root designed via the perfect-square discriminant. -/
theorem cs_amp_saturation {input output : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4)
    (hdc : CommonSourceDC csAmpInstance 5 input output) :
    input - 1 ≤ output := by
  have htransfer := cs_amp_transfer hlo hhi hdc
  nlinarith [htransfer, mul_nonneg
    (by linarith : (0 : ℝ) ≤ 5 - 4 * (input - 1))
    (by linarith : (0 : ℝ) ≤ 3 * (input - 1) + 5)]

/-- (d) Existence: for every input voltage the stage has a DC operating
point, by the intermediate value theorem over the branch-glued continuous
channel current. -/
theorem cs_amp_dc_exists (input : ℝ) :
    ∃ output, CommonSourceDC csAmpInstance 5 input output := by
  rw [csAmpInstance_eq]
  exact commonSource_dc_exists _ input (by norm_num) (by norm_num)
    (by norm_num)

/-- Realizability twin for the window theorems: for every input in
[3/2, 9/4] the derived transfer point is an actual operating point. -/
theorem cs_amp_transfer_realizable {input : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4) :
    CommonSourceDC csAmpInstance 5 input
      (5 - 12 / 5 * (input - 1) ^ 2) := by
  obtain ⟨output, hdc⟩ := cs_amp_dc_exists input
  have htransfer := cs_amp_transfer hlo hhi hdc
  rwa [htransfer] at hdc

/-- Uniqueness at every input: the strictly decreasing resistor load line
meets the monotone channel current exactly once. -/
theorem cs_amp_dc_unique {input output₁ output₂ : ℝ}
    (h₁ : CommonSourceDC csAmpInstance 5 input output₁)
    (h₂ : CommonSourceDC csAmpInstance 5 input output₂) :
    output₁ = output₂ := by
  rw [csAmpInstance_eq] at h₁ h₂
  exact commonSource_dc_determinate (by norm_num) (by norm_num) h₁ h₂

/-- Clipping: at or below threshold the stage is cut off and the drain
rails at the supply. -/
theorem cs_amp_cutoff {input output : ℝ}
    (hcut : input ≤ 1)
    (hdc : CommonSourceDC csAmpInstance 5 input output) :
    output = 5 := by
  rw [csAmpInstance_eq] at hdc
  exact commonSource_dc_cutoff (by norm_num) (by simpa using hcut) hdc

/-- Triode/clipping region: past the window endpoint 9/4 every DC state
drops strictly below the overdrive and sits at the exact clipped voltage
— the smaller root of the triode load-line quadratic, whose discriminant
is inherited (as a literal square) from the DC state itself. -/
theorem cs_amp_triode {input output : ℝ}
    (hdeep : 9 / 4 < input)
    (hdc : CommonSourceDC csAmpInstance 5 input output) :
    output < input - 1 ∧
    output =
      (24 / 5 * (input - 1) + 1 -
          Real.sqrt ((24 / 5 * (input - 1) + 1) ^ 2 - 48)) /
        (24 / 5) := by
  rw [csAmpInstance_eq] at hdc
  have hmem := commonSource_dc_triode_membership (by norm_num) (by norm_num)
    (by norm_num; linarith)
    (by
      norm_num
      nlinarith [mul_pos (by linarith : (0 : ℝ) < input - 9 / 4)
        (by linarith : (0 : ℝ) < input + 2 / 3)])
    hdc
  have hform := commonSource_dc_triode (by norm_num) (by norm_num)
    (by norm_num; linarith)
    (by
      norm_num
      nlinarith [mul_pos (by linarith : (0 : ℝ) < input - 9 / 4)
        (by linarith : (0 : ℝ) < input + 2 / 3)])
    hdc
  refine ⟨by simpa using hmem, ?_⟩
  rw [hform]
  norm_num

/-- Realizability twin for the clipping region at the designed deep-triode
probe `V_in = 7/2` (Vov = 5/2): the triode discriminant is the perfect
square 11² BY DESIGN, and the exactly rational clipped point 5/12 V is an
actual DC state. -/
theorem cs_amp_triode_realizable :
    CommonSourceDC csAmpInstance 5 (7 / 2) (5 / 12) := by
  rw [csAmpInstance_eq]
  refine ⟨by norm_num, ?_⟩
  norm_num [mos1ForwardCurrent]

/-- At the deep-triode probe the output is pinned at exactly 5/12 V
(≈ 0.417 V above the low rail): a fully clipped output, derived, and
exactly rational by the perfect-square discriminant design. -/
theorem cs_amp_triode_point {output : ℝ}
    (hdc : CommonSourceDC csAmpInstance 5 (7 / 2) output) :
    output = 5 / 12 :=
  cs_amp_dc_unique hdc cs_amp_triode_realizable

/-- The COMPLETE three-region DC characteristic, partitioning every real
input: cutoff rails at the supply, the square-law window gives the
quadratic transfer curve, and past 9/4 the stage clips onto the triode
root. Each branch is derived from the same physics-only relation. -/
theorem cs_amp_regions {input output : ℝ}
    (hdc : CommonSourceDC csAmpInstance 5 input output) :
    (input ≤ 1 → output = 5) ∧
    (1 < input → input ≤ 9 / 4 → output = 5 - 12 / 5 * (input - 1) ^ 2) ∧
    (9 / 4 < input →
      output =
        (24 / 5 * (input - 1) + 1 -
            Real.sqrt ((24 / 5 * (input - 1) + 1) ^ 2 - 48)) /
          (24 / 5)) := by
  refine ⟨fun hcut => cs_amp_cutoff hcut hdc, fun hon hhi => ?_,
    fun hdeep => (cs_amp_triode hdeep hdc).2⟩
  rw [csAmpInstance_eq] at hdc
  have hop := commonSource_dc_op (by norm_num) (by norm_num)
    (by norm_num; linarith)
    (by
      norm_num
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9 / 4 - input)
        (by linarith : (0 : ℝ) ≤ input + 2 / 3)])
    hdc
  rw [hop]
  norm_num

/-- Realizability twin for the three-region characteristic: every input
has an actual DC state, and it satisfies whichever region formula its
input selects. -/
theorem cs_amp_regions_realizable (input : ℝ) :
    ∃ output,
      CommonSourceDC csAmpInstance 5 input output ∧
      (input ≤ 1 → output = 5) ∧
      (1 < input → input ≤ 9 / 4 →
        output = 5 - 12 / 5 * (input - 1) ^ 2) ∧
      (9 / 4 < input →
        output =
          (24 / 5 * (input - 1) + 1 -
              Real.sqrt ((24 / 5 * (input - 1) + 1) ^ 2 - 48)) /
            (24 / 5)) := by
  obtain ⟨output, hdc⟩ := cs_amp_dc_exists input
  exact ⟨output, hdc, cs_amp_regions hdc⟩

/-- THE GAIN THEOREM, stated as a literal mathlib derivative with the
textbook value: ANY function solving the physics-only DC relation on the
saturation window has derivative `−KP·(V_in0 − V_TO)·R_D = −g_m·R_D` at
the designed bias. The behavior relation pins every solution family to
the derived transfer curve near the bias, so the derivative transfers. -/
theorem cs_amp_gain {vout : ℝ → ℝ}
    (hsol : ∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
      CommonSourceDC csAmpInstance 5 v (vout v)) :
    HasDerivAt vout (-(1 / 2500 * (2 - 1) * 12000)) 2 := by
  have h := commonSource_gain (fabricated := csAmpInstance) (supply := 5)
    (lo := 3 / 2) (hi := 9 / 4) (bias := 2)
    (by rw [csAmpInstance_eq]; norm_num) (by rw [csAmpInstance_eq]; norm_num)
    (by norm_num) (by norm_num)
    (by rw [csAmpInstance_eq]; norm_num) (by rw [csAmpInstance_eq]; norm_num)
    hsol
  exact h.congr_deriv (by rw [csAmpInstance_eq])

/-- The gain as a `deriv` value: −24/5 = −4.8, matching the ngspice AC
magnitude at low frequency. -/
theorem cs_amp_gain_deriv {vout : ℝ → ℝ}
    (hsol : ∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
      CommonSourceDC csAmpInstance 5 v (vout v)) :
    deriv vout 2 = -(24 / 5) := by
  rw [(cs_amp_gain hsol).deriv]
  norm_num

/-- Realizability twin for the gain theorem: a solution family satisfying
its hypothesis exists (the derived transfer curve), and it has the
literal derivative −24/5 at the bias. -/
theorem cs_amp_gain_realizable :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
        CommonSourceDC csAmpInstance 5 v (vout v)) ∧
      HasDerivAt vout (-(24 / 5)) 2 := by
  obtain ⟨vout, hsol, hderiv⟩ :=
    commonSource_gain_realizable (fabricated := csAmpInstance) (supply := 5)
      (lo := 3 / 2) (hi := 9 / 4) (bias := 2)
      (by rw [csAmpInstance_eq]; norm_num) (by rw [csAmpInstance_eq]; norm_num)
      (by norm_num) (by norm_num)
      (by rw [csAmpInstance_eq]; norm_num) (by rw [csAmpInstance_eq]; norm_num)
  exact ⟨vout, hsol, hderiv.congr_deriv (by rw [csAmpInstance_eq]; norm_num)⟩

/-- Exact second-order linearization identity: for any perturbation
`|d| ≤ 1/4` around the bias, the deviation of the true DC response from
the small-signal prediction `−g_m·R_D·d` is EXACTLY `−12/5·d²`. -/
theorem cs_amp_linearization {d out0 outd : ℝ}
    (hd : |d| ≤ 1 / 4)
    (h0 : CommonSourceDC csAmpInstance 5 2 out0)
    (hdd : CommonSourceDC csAmpInstance 5 (2 + d) outd) :
    outd - out0 + 24 / 5 * d = -(12 / 5) * d ^ 2 := by
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  rw [csAmpInstance_eq] at h0 hdd
  have hop0 := commonSource_dc_op (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h0
  have hopd := commonSource_dc_op (by norm_num) (by norm_num)
    (by norm_num; linarith)
    (by
      norm_num
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9 / 4 - (2 + d))
        (by linarith : (0 : ℝ) ≤ (2 + d) + 2 / 3)])
    hdd
  linear_combination hopd - hop0

/-- The linearity error in absolute value is an EQUALITY, not a bound:
`|Δv_out + g_m·R_D·d| = 12/5·d²` — stronger than any datasheet-style
linearity spec. -/
theorem cs_amp_linearization_bound {d out0 outd : ℝ}
    (hd : |d| ≤ 1 / 4)
    (h0 : CommonSourceDC csAmpInstance 5 2 out0)
    (hdd : CommonSourceDC csAmpInstance 5 (2 + d) outd) :
    |outd - out0 + 24 / 5 * d| = 12 / 5 * d ^ 2 := by
  rw [cs_amp_linearization hd h0 hdd, abs_mul, abs_neg,
    abs_of_nonneg (sq_nonneg d)]
  norm_num

/-- The datasheet-shaped corollary in the campaign's requested form:
`|v_out(V_in0 + d) − v_out(V_in0) + g_m·R_D·d| ≤ (R_D·KP/2)·d²`. -/
theorem cs_amp_linearization_le {d out0 outd : ℝ}
    (hd : |d| ≤ 1 / 4)
    (h0 : CommonSourceDC csAmpInstance 5 2 out0)
    (hdd : CommonSourceDC csAmpInstance 5 (2 + d) outd) :
    |outd - out0 + 24 / 5 * d| ≤ 12000 * (1 / 2500) / 2 * d ^ 2 := by
  rw [cs_amp_linearization_bound hd h0 hdd]
  norm_num

/-- Realizability twin for the linearization identity: both perturbed DC
states exist and exhibit the exact second-order deviation. -/
theorem cs_amp_linearization_realizable {d : ℝ} (hd : |d| ≤ 1 / 4) :
    ∃ out0 outd,
      CommonSourceDC csAmpInstance 5 2 out0 ∧
      CommonSourceDC csAmpInstance 5 (2 + d) outd ∧
      outd - out0 + 24 / 5 * d = -(12 / 5) * d ^ 2 := by
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  exact ⟨13 / 5, 5 - 12 / 5 * (2 + d - 1) ^ 2, cs_amp_op_realizable,
    cs_amp_transfer_realizable (by linarith) (by linarith), by ring⟩

/-- Output swing over the stated saturation window: every DC state stays
inside [5/4, 22/5] — 3.15 V of provable linear-region swing. -/
theorem cs_amp_swing {input output : ℝ}
    (hlo : 3 / 2 ≤ input) (hhi : input ≤ 9 / 4)
    (hdc : CommonSourceDC csAmpInstance 5 input output) :
    5 / 4 ≤ output ∧ output ≤ 22 / 5 := by
  have ht := cs_amp_transfer hlo hhi hdc
  constructor
  · rw [ht]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 5 / 4 - (input - 1))
      (by linarith : (0 : ℝ) ≤ (input - 1) + 5 / 4)]
  · rw [ht]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (input - 1) - 1 / 2)
      (by linarith : (0 : ℝ) ≤ (input - 1) + 1 / 2)]

/-- The swing maximum 22/5 V is attained (at the window's low edge), so
`cs_amp_swing`'s upper bound is tight. -/
theorem cs_amp_swing_max_realizable :
    CommonSourceDC csAmpInstance 5 (3 / 2) (22 / 5) := by
  have h := cs_amp_transfer_realizable (le_refl (3 / 2 : ℝ)) (by norm_num)
  norm_num at h
  exact h

/-- The swing minimum 5/4 V is attained (at the window's high edge, the
designed rational root of the edge-of-saturation quadratic), so
`cs_amp_swing`'s lower bound is tight. -/
theorem cs_amp_swing_min_realizable :
    CommonSourceDC csAmpInstance 5 (9 / 4) (5 / 4) := by
  have h := cs_amp_transfer_realizable (by norm_num) (le_refl (9 / 4 : ℝ))
  norm_num at h
  exact h

/-! ## Tolerance-box gain interval (the Monte-Carlo killer)

A fabricated part will not have `VTO = 1` and `KP = 400u` exactly. The
theorems below quantify over EVERY part in a ±10 % box around nominal —
`VTO ∈ [0.9, 1.1]`, `KP ∈ [360u, 440u]` — and pin the small-signal gain
at the 2 V bias inside an explicit closed interval while re-deriving the
per-part saturation window from one worst-corner check. Where Monte-Carlo
samples the box, the theorem covers it. -/

-- Corner arithmetic for the ±10 % box (kernel-decidable):
-- fastest corner (KP = 440u, VTO = 0.9): gain magnitude 726/125 = 5.808.
#guard (11 : Rat) / 25000 * (2 - 9 / 10) * 12000 == 726 / 125
-- slowest corner (KP = 360u, VTO = 1.1): gain magnitude 486/125 = 3.888.
#guard (9 : Rat) / 25000 * (2 - 11 / 10) * 12000 == 486 / 125
-- Nominal gain 24/5 lies inside the interval.
#guard (486 : Rat) / 125 ≤ 24 / 5 && (24 : Rat) / 5 ≤ 726 / 125
-- Worst-corner saturation window at the shrunken endpoint 41/20:
-- (11/25000)·12000/2·(41/20 − 9/10)² + (41/20 − 9/10) = 23207/5000 ≤ 5.
#guard (11 : Rat) / 25000 * 12000 / 2 * (41 / 20 - 9 / 10) ^ 2 +
  (41 / 20 - 9 / 10) == 23207 / 5000
#guard (23207 : Rat) / 5000 ≤ 5
-- The nominal window endpoint 9/4 does NOT survive the box (the corner
-- check fails there), which is why the box theorem uses 41/20:
#guard !((11 : Rat) / 25000 * 12000 / 2 * (9 / 4 - 9 / 10) ^ 2 +
  (9 / 4 - 9 / 10) ≤ 5)
-- Operating-point corners: output stays inside [2257/1250, 4063/1250].
#guard (5 : Rat) - 11 / 25000 * 12000 / 2 * (2 - 9 / 10) ^ 2 == 2257 / 1250
#guard (5 : Rat) - 9 / 25000 * 12000 / 2 * (2 - 11 / 10) ^ 2 == 4063 / 1250

/-- THE BENCH PREDICTION. For every fabricated part whose threshold and
transconductance lie within ±10 % of nominal (`VTO ∈ [0.9, 1.1]` V,
`KP ∈ [360µ, 440µ]` A/V²), any solution family of the physics-only DC
relation on the ±50 mV input window around the 2 V bias satisfies, at the
bias: (i) it has a literal derivative, the part's own gain
`−KP·(2 − VTO)·R_D`; (ii) that gain lies in the closed interval
`[−726/125, −486/125] = [−5.808, −3.888]`; (iii) the device is saturated
(`V_ds ≥ V_ov`), re-derived per-part from one worst-corner window check;
and (iv) the DC output lies in `[2257/1250, 4063/1250] =
[1.8056, 3.2504]` V. Bench measurement of gain and operating point must
land in these intervals or falsify the model envelope. -/
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
    vout 2 ∈ Set.Icc (2257 / 1250 : ℝ) (4063 / 1250) := by
  obtain ⟨hvtoLo, hvtoHi⟩ := hvto
  obtain ⟨hkpLo, hkpHi⟩ := hkp
  have hbeta : (0 : ℝ) < kp := lt_of_lt_of_le (by norm_num) hkpLo
  have hrd : (0 : ℝ) < (12000 : ℝ) := by norm_num
  have hon : vto < 2 := by linarith
  -- One worst-corner check gates the window for the whole box.
  have hwindow :
      kp * 12000 / 2 * (41 / 20 - vto) ^ 2 + (41 / 20 - vto) ≤ 5 :=
    commonSource_window_box
      (fabricated := ⟨vto, kp, 12000⟩)
      ⟨hvtoLo, hvtoHi⟩ ⟨hkpLo, hkpHi⟩ hrd (by norm_num)
      (by norm_num) (by norm_num)
  -- The per-part window also covers the bias itself.
  have hwindow2 :
      kp * 12000 / 2 * (2 - vto) ^ 2 + (2 - vto) ≤ 5 :=
    commonSource_window_mono (fabricated := ⟨vto, kp, 12000⟩)
      hbeta hrd hon (by norm_num) hwindow
  have hdc2 := hsol 2 (by constructor <;> norm_num)
  have hop := commonSource_dc_op (fabricated := ⟨vto, kp, 12000⟩)
    hbeta hrd hon hwindow2 hdc2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact commonSource_gain (fabricated := ⟨vto, kp, 12000⟩)
      hbeta hrd (by norm_num) (by norm_num) (by linarith) hwindow hsol
  · have hmem := commonSource_gain_box
      (fabricated := ⟨vto, kp, 12000⟩) (bias := 2)
      ⟨hvtoLo, hvtoHi⟩ ⟨hkpLo, hkpHi⟩ hrd.le (by norm_num) (by linarith)
    constructor
    · calc (-(726 / 125) : ℝ)
          = -(11 / 25000 * (2 - 9 / 10) * 12000) := by norm_num
        _ ≤ -(kp * (2 - vto) * 12000) := hmem.1
    · calc -(kp * (2 - vto) * 12000)
          ≤ -(9 / 25000 * (2 - 11 / 10) * 12000) := hmem.2
        _ = (-(486 / 125) : ℝ) := by norm_num
  · exact commonSource_dc_saturation (fabricated := ⟨vto, kp, 12000⟩)
      hbeta hrd hon hwindow2 hdc2
  · rw [hop]
    constructor
    · have h1 : (2 - vto) ^ 2 ≤ (11 / 10) ^ 2 := by nlinarith
      have h2 : kp * (2 - vto) ^ 2 ≤ 11 / 25000 * (11 / 10) ^ 2 := by
        nlinarith [sq_nonneg (2 - vto)]
      nlinarith [h2]
    · have h1 : ((9 : ℝ) / 10) ^ 2 ≤ (2 - vto) ^ 2 := by nlinarith
      have h2 : (9 : ℝ) / 25000 * (9 / 10) ^ 2 ≤ kp * (2 - vto) ^ 2 := by
        nlinarith
      nlinarith [h2]

/-- Realizability twin for the tolerance-box interval: EVERY part in the
box admits a solution family on the window (its own derived transfer
curve), with its own gain as the literal derivative at the bias. The
interval hypothesis is never vacuous anywhere in the box. -/
theorem cs_amp_gain_interval_realizable {vto kp : ℝ}
    (hvto : vto ∈ Set.Icc (9 / 10 : ℝ) (11 / 10))
    (hkp : kp ∈ Set.Icc (9 / 25000 : ℝ) (11 / 25000)) :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
        CommonSourceDC
          { threshold := vto, beta := kp, drainResistance := 12000 }
          5 v (vout v)) ∧
      HasDerivAt vout (-(kp * (2 - vto) * 12000)) 2 := by
  obtain ⟨hvtoLo, hvtoHi⟩ := hvto
  obtain ⟨hkpLo, hkpHi⟩ := hkp
  have hbeta : (0 : ℝ) < kp := lt_of_lt_of_le (by norm_num) hkpLo
  have hrd : (0 : ℝ) < (12000 : ℝ) := by norm_num
  exact commonSource_gain_realizable (fabricated := ⟨vto, kp, 12000⟩)
    hbeta hrd (by norm_num) (by norm_num) (by linarith)
    (commonSource_window_box (fabricated := ⟨vto, kp, 12000⟩)
      ⟨hvtoLo, hvtoHi⟩ ⟨hkpLo, hkpHi⟩ hrd (by norm_num)
      (by norm_num) (by norm_num))

/-- The interval's fast endpoint is attained: the corner part
`(VTO, KP) = (0.9, 440µ)` realizes gain exactly `−726/125 = −5.808`. -/
theorem cs_amp_gain_interval_tight_fast :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
        CommonSourceDC
          { threshold := 9 / 10, beta := 11 / 25000,
            drainResistance := 12000 }
          5 v (vout v)) ∧
      HasDerivAt vout (-(726 / 125)) 2 := by
  obtain ⟨vout, hsol, hderiv⟩ :=
    cs_amp_gain_interval_realizable (vto := 9 / 10) (kp := 11 / 25000)
      (by constructor <;> norm_num) (by constructor <;> norm_num)
  exact ⟨vout, hsol, hderiv.congr_deriv (by norm_num)⟩

/-- The interval's slow endpoint is attained: the corner part
`(VTO, KP) = (1.1, 360µ)` realizes gain exactly `−486/125 = −3.888`. -/
theorem cs_amp_gain_interval_tight_slow :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
        CommonSourceDC
          { threshold := 11 / 10, beta := 9 / 25000,
            drainResistance := 12000 }
          5 v (vout v)) ∧
      HasDerivAt vout (-(486 / 125)) 2 := by
  obtain ⟨vout, hsol, hderiv⟩ :=
    cs_amp_gain_interval_realizable (vto := 11 / 10) (kp := 9 / 25000)
      (by constructor <;> norm_num) (by constructor <;> norm_num)
  exact ⟨vout, hsol, hderiv.congr_deriv (by norm_num)⟩

end Examples.spice.cs_amp.proof
