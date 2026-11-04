import LeanModels.Spice.DiffPair
import LeanModels.Circuit.Surface

namespace Examples.spice.diff_pair.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit diffPair from "Examples/spice/diff_pair/diff_pair.cir"

/-! Concrete kernel-decidable checks of the deck-header design arithmetic. -/

-- I_TAIL/β = (1/2500)/(1/2500) = 1 V² is a perfect square BY DESIGN, so the
-- balanced overdrive √(I_TAIL/β) = 1 V is exactly rational.
#guard (1 : Rat) / 2500 / (1 / 2500) == 1
-- Balanced drain drop R_D·I_TAIL/2 = 2 V: both outputs at exactly 3 V.
#guard (10000 : Rat) * (1 / 2500) / 2 == 2
#guard (5 : Rat) - 10000 * (1 / 2500) / 2 == 3
-- Balance differential gain: g_m·R_D = β·√(I_TAIL/β)·R_D = 4 exactly.
#guard (10000 : Rat) * (1 / 2500) * 1 == 4
-- Balanced CM window: cm + R_D·I_TAIL/2 ≤ V_DD + V_TO, i.e. cm ≤ 4.
#guard (5 : Rat) + 1 - 10000 * (1 / 2500) / 2 == 4
-- The 3-4-5 probe (d = 6/5): 1 − (6/5)²/4 = 16/25 = (4/5)² is a perfect
-- square BY DESIGN, so the probe overdrive u = 4/5 is exactly rational.
#guard (1 : Rat) - (6 / 5) ^ 2 / 4 == (4 / 5) ^ 2
-- Probe outputs and tail (cm = 1/4): outp = 27/25, outn = 123/25,
-- tail = 1/4 − 1 − 4/5 = −31/20; vod = −96/25.
#guard (5 : Rat) - 10000 * (1 / 2500 / 2 * (4 / 5 + 6 / 5 / 2) ^ 2) == 27 / 25
#guard (5 : Rat) - 10000 * (1 / 2500 / 2 * (4 / 5 - 6 / 5 / 2) ^ 2) == 123 / 25
#guard (1 : Rat) / 4 - 1 - 4 / 5 == -(31 / 20)
#guard (27 : Rat) / 25 - 123 / 25 == -(96 / 25)
-- Probe saturation window: 1/4 + 3/5 + 2·(1 + 3/5)² = 597/100 ≤ 6.
#guard (1 : Rat) / 4 + 6 / 5 / 2 +
  10000 * (1 / 2500) / 2 * (1 + 6 / 5 / 2) ^ 2 == 597 / 100
#guard (597 : Rat) / 100 ≤ 5 + 1
-- Gain window at the balance bias cm = 5/2 with m = 1/2: 47/8 ≤ 6.
#guard (5 : Rat) / 2 + 1 / 4 + 10000 * (1 / 2500) / 2 * (1 + 1 / 4) ^ 2 == 47 / 8
-- CMRR window worst corner (|d| = 1/2 at cm = 21/8):
-- 21/8 + 1/4 + 2·(1 + 1/4)² = 6 exactly — the stated CM range is TIGHT.
#guard (21 : Rat) / 8 + 1 / 4 + 10000 * (1 / 2500) / 2 * (1 + 1 / 4) ^ 2 == 6
-- The deck adapter accepts the committed topology.
#guard diffPair.toDiffPairNominal matches .ok _

/-- The checked adapter is the only path from the source deck to these
nominal parameters. -/
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
        tailCurrent := 1 / 2500 } := by
  circuit_reduce

def diffPairNominal : DiffPairNominal :=
  match diffPair.toDiffPairNominal with
  | .ok nominal => nominal
  | .error _ => default

theorem diffPairNominal_eq :
    diffPairNominal =
      { inputPNode := ⟨5⟩
        inputNNode := ⟨6⟩
        outputPNode := ⟨1⟩
        outputNNode := ⟨2⟩
        supplyNode := ⟨0⟩
        tailNode := ⟨3⟩
        threshold := 1
        beta := 1 / 2500
        drainResistance := 10000
        tailCurrent := 1 / 2500 } := by
  unfold diffPairNominal
  rw [diff_pair_topology]

/-- Real-valued fabricated instance recovered from the deck through the
checked adapter. -/
noncomputable def diffPairInstance : DiffPairInstance :=
  diffPairNominal.instance

theorem diffPairInstance_eq :
    diffPairInstance =
      { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
        tailCurrent := 1 / 2500 } := by
  unfold diffPairInstance
  rw [diffPairNominal_eq]
  simp only [DiffPairNominal.instance, DiffPairInstance.mk.injEq]
  norm_num

/-- `I_TAIL/β = 1` is a perfect square BY DESIGN: the balanced overdrive is
exactly 1 V. -/
private theorem sqrt_ratio : Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) = 1 := by
  rw [show (1 : ℝ) / 2500 / (1 / 2500) = 1 by norm_num]
  exact Real.sqrt_one

/-! ## Balanced operating point and the common-mode range -/

/-- (a) THE BALANCED OPERATING POINT, derived from the device equations,
the drain KCLs, and the tail KCL: at zero differential drive, for every
common mode in the range `cm ≤ 4`, every DC state has BOTH outputs at
exactly 3 V and the tail node tracking the common mode at exactly
`cm − 2` (the fixed offset `V_TO + √(I_TAIL/β) = 2`). Exactly rational
because `I_TAIL/β = 1` is a perfect square BY DESIGN. -/
theorem diff_pair_balanced {cm outP outN tail : ℝ} (hcm : cm ≤ 4)
    (hdc : DiffPairDC diffPairInstance 5 cm cm outP outN tail) :
    outP = 3 ∧ outN = 3 ∧ tail = cm - 2 := by
  rw [diffPairInstance_eq] at hdc
  obtain ⟨hP, hN, hT⟩ := diffPair_dc_balanced (by norm_num) (by norm_num)
    (by norm_num) (by norm_num; linarith) hdc
  refine ⟨?_, ?_, ?_⟩
  · rw [hP]; norm_num
  · rw [hN]; norm_num
  · rw [hT]
    show cm - 1 - Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) = cm - 2
    rw [sqrt_ratio]; ring

/-- (b) Realizability twin for the balanced operating point: for every
common mode in the range, the derived balanced state IS a DC state. -/
theorem diff_pair_balanced_realizable {cm : ℝ} (hcm : cm ≤ 4) :
    DiffPairDC diffPairInstance 5 cm cm 3 3 (cm - 2) := by
  rw [diffPairInstance_eq]
  have h := diffPair_dc_balanced_realizable
    (fab := { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
              tailCurrent := 1 / 2500 }) (supply := 5) (cm := cm)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num; linarith)
  have e1 : (3 : ℝ) = 5 - 10000 * (1 / 2500) / 2 := by norm_num
  have e2 : cm - 2 = cm - 1 - Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) := by
    rw [sqrt_ratio]; ring
  rw [e1, e2]
  exact h

/-- (d) THE COMMON-MODE RANGE: everywhere on `cm ≤ 4` both devices stay
saturated, the outputs are pinned at the balanced value, and the tail node
tracks the common mode at the exact fixed offset 2 V. (No lower CM limit:
the IDEAL tail source has no compliance floor — see the idealization label
on `diff_pair_cmrr`.) -/
theorem diff_pair_cm_range (cm : ℝ) (hcm : cm ≤ 4) :
    ∃ outP outN tail,
      DiffPairDC diffPairInstance 5 cm cm outP outN tail ∧
      outP = 3 ∧ outN = 3 ∧ tail = cm - 2 :=
  ⟨3, 3, cm - 2, diff_pair_balanced_realizable hcm, rfl, rfl, rfl⟩

/-- Uniqueness of the pair's DC state at every drive: outputs and the tail
node. -/
theorem diff_pair_dc_unique {inputP inputN p₁ n₁ s₁ p₂ n₂ s₂ : ℝ}
    (h₁ : DiffPairDC diffPairInstance 5 inputP inputN p₁ n₁ s₁)
    (h₂ : DiffPairDC diffPairInstance 5 inputP inputN p₂ n₂ s₂) :
    p₁ = p₂ ∧ n₁ = n₂ ∧ s₁ = s₂ := by
  rw [diffPairInstance_eq] at h₁ h₂
  exact diffPair_dc_determinate (by norm_num) (by norm_num) (by norm_num)
    h₁ h₂

/-! ## Window helpers for the differential-drive theorems

`|d| ≤ 1/2` with `cm ≤ 21/8` is the committed differential window: the
worst corner lands the saturation check at exactly 6 = V_DD + V_TO
(tight, see the `#guard`s above). -/

private theorem window_conducting {d : ℝ} (hd : |d| ≤ 1 / 2) :
    DiffPairConducting
      { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
        tailCurrent := 1 / 2500 } d := by
  show d ^ 2 < 2 * (1 / 2500 / (1 / 2500))
  nlinarith [sq_abs d, abs_nonneg d, hd,
    mul_le_mul_of_nonneg_left hd (abs_nonneg d)]

private theorem window_saturation {cm d : ℝ} (hd : |d| ≤ 1 / 2)
    (hcm : cm ≤ 21 / 8) :
    DiffPairSaturationWindow
      { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
        tailCurrent := 1 / 2500 } 5 cm d := by
  show cm + |d| / 2 + 10000 * (1 / 2500) / 2 *
      (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) + |d| / 2) ^ 2 ≤ 5 + 1
  rw [sqrt_ratio]
  nlinarith [abs_nonneg d, hd, hcm,
    mul_le_mul_of_nonneg_left hd (abs_nonneg d)]

/-! ## Differential gain as a literal derivative -/

/-- (c) THE DIFFERENTIAL GAIN THEOREM. ANY solution family of the
physics-only DC relation in differential coordinates around balance
(`inputs 5/2 ± d/2`, `|d| < 1/2`) has a literal mathlib derivative of its
differential output at `d = 0`, and it is the textbook
`−g_m·R_D = −β·√(I_TAIL/β)·R_D = −4` exactly. -/
theorem diff_pair_gain {vop von vtail : ℝ → ℝ}
    (hsol : ∀ d ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
      DiffPairDC diffPairInstance 5 (5 / 2 + d / 2) (5 / 2 - d / 2)
        (vop d) (von d) (vtail d)) :
    HasDerivAt (fun d => vop d - von d) (-4) 0 := by
  simp only [diffPairInstance_eq] at hsol
  have h := LeanModels.Spice.diffPair_gain
    (fab := { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
              tailCurrent := 1 / 2500 })
    (supply := 5) (cm := 5 / 2) (m := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      show (5 : ℝ) / 2 + 1 / 2 / 2 + 10000 * (1 / 2500) / 2 *
          (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) + 1 / 2 / 2) ^ 2 ≤ 5 + 1
      rw [sqrt_ratio]; norm_num)
    hsol
  refine h.congr_deriv ?_
  show -(10000 * (1 / 2500) *
    Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500))) = -4
  rw [sqrt_ratio]; norm_num

/-- The differential gain as a `deriv` value: −4, matching the ngspice
central-difference probe across balance. -/
theorem diff_pair_gain_deriv {vop von vtail : ℝ → ℝ}
    (hsol : ∀ d ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
      DiffPairDC diffPairInstance 5 (5 / 2 + d / 2) (5 / 2 - d / 2)
        (vop d) (von d) (vtail d)) :
    deriv (fun d => vop d - von d) 0 = -4 :=
  (diff_pair_gain hsol).deriv

/-- Realizability twin for the differential gain theorem: a solution
family satisfying its hypothesis exists — the derived transfer curves —
with the same literal derivative at balance. -/
theorem diff_pair_gain_realizable :
    ∃ vop von vtail : ℝ → ℝ,
      (∀ d ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
        DiffPairDC diffPairInstance 5 (5 / 2 + d / 2) (5 / 2 - d / 2)
          (vop d) (von d) (vtail d)) ∧
      HasDerivAt (fun d => vop d - von d) (-4) 0 := by
  simp only [diffPairInstance_eq]
  obtain ⟨vop, von, vtail, hsol, hderiv⟩ :=
    LeanModels.Spice.diffPair_gain_realizable
      (fab := { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
                tailCurrent := 1 / 2500 })
      (supply := 5) (cm := 5 / 2) (m := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
      (by
        show (5 : ℝ) / 2 + 1 / 2 / 2 + 10000 * (1 / 2500) / 2 *
            (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) + 1 / 2 / 2) ^ 2 ≤ 5 + 1
        rw [sqrt_ratio]; norm_num)
  refine ⟨vop, von, vtail, hsol, hderiv.congr_deriv ?_⟩
  show -(10000 * (1 / 2500) *
    Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500))) = -4
  rw [sqrt_ratio]; norm_num

/-! ## Ideal-tail common-mode rejection -/

/-- IDEAL-TAIL COMMON-MODE REJECTION — an EXACT invariance theorem, and a
loudly-labeled idealization. Under `LAMBDA = 0` (saturated channel current
independent of `V_DS`) and the IDEAL tail source (exact `I_TAIL` at any
tail voltage, no compliance limit), shifting the common mode anywhere in
the stated range moves the tail node by EXACTLY the shift and moves
neither output at all: infinite CMRR. Real amplifiers only approximate
this — channel-length modulation and finite tail-source output resistance
each break one premise. This theorem states exactly WHAT ideal common-mode
rejection is, so later refinements can quantify the deviation from it. -/
theorem diff_pair_cmrr {cm cm' d : ℝ}
    {outP outN tail outP' outN' tail' : ℝ}
    (hd : |d| ≤ 1 / 2) (hcm : cm ≤ 21 / 8) (hcm' : cm' ≤ 21 / 8)
    (hdc : DiffPairDC diffPairInstance 5 (cm + d / 2) (cm - d / 2)
      outP outN tail)
    (hdc' : DiffPairDC diffPairInstance 5 (cm' + d / 2) (cm' - d / 2)
      outP' outN' tail') :
    outP' = outP ∧ outN' = outN ∧ tail' - tail = cm' - cm := by
  rw [diffPairInstance_eq] at hdc hdc'
  exact diffPair_cmrr_ideal (by norm_num) (by norm_num) (by norm_num)
    (window_conducting hd) (window_saturation hd hcm)
    (window_saturation hd hcm') hdc hdc'

/-- Realizability twin for the common-mode invariance: at both common
modes the DC states exist and exhibit the exact invariance. -/
theorem diff_pair_cmrr_realizable {cm cm' d : ℝ}
    (hd : |d| ≤ 1 / 2) (hcm : cm ≤ 21 / 8) (hcm' : cm' ≤ 21 / 8) :
    ∃ outP outN tail outP' outN' tail',
      DiffPairDC diffPairInstance 5 (cm + d / 2) (cm - d / 2)
        outP outN tail ∧
      DiffPairDC diffPairInstance 5 (cm' + d / 2) (cm' - d / 2)
        outP' outN' tail' ∧
      outP' = outP ∧ outN' = outN ∧ tail' - tail = cm' - cm := by
  simp only [diffPairInstance_eq]
  exact LeanModels.Spice.diffPair_cmrr_realizable
    (by norm_num) (by norm_num) (by norm_num)
    (window_conducting hd) (window_saturation hd hcm)
    (window_saturation hd hcm')

/-! ## Large-signal differential transfer -/

/-- The exact large-signal differential output on the committed window:
`v_outP − v_outN = −4·d·√(1 − d²/4)` — the textbook differential transfer
characteristic, derived from the physics relation. -/
theorem diff_pair_vod {d outP outN tail : ℝ} (hd : |d| ≤ 1 / 2)
    (hdc : DiffPairDC diffPairInstance 5 (5 / 2 + d / 2) (5 / 2 - d / 2)
      outP outN tail) :
    outP - outN = -(4 * d * Real.sqrt (1 - d ^ 2 / 4)) := by
  rw [diffPairInstance_eq] at hdc
  have h := diffPair_dc_diff_output (by norm_num) (by norm_num) (by norm_num)
    (window_conducting hd) (window_saturation hd (by norm_num)) hdc
  rw [h]
  show -(10000 * (1 / 2500) * d *
      Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - d ^ 2 / 4)) =
    -(4 * d * Real.sqrt (1 - d ^ 2 / 4))
  rw [show (1 : ℝ) / 2500 / (1 / 2500) - d ^ 2 / 4 = 1 - d ^ 2 / 4 by
    norm_num]
  ring

/-- Realizability twin for the differential transfer: the derived state IS
a DC state and exhibits the closed-form differential output. -/
theorem diff_pair_vod_realizable {d : ℝ} (hd : |d| ≤ 1 / 2) :
    ∃ outP outN tail,
      DiffPairDC diffPairInstance 5 (5 / 2 + d / 2) (5 / 2 - d / 2)
        outP outN tail ∧
      outP - outN = -(4 * d * Real.sqrt (1 - d ^ 2 / 4)) := by
  simp only [diffPairInstance_eq]
  refine ⟨_, _, _,
    diffPair_dc_transfer_realizable (by norm_num) (by norm_num) (by norm_num)
      (window_conducting hd) (window_saturation hd (by norm_num)), ?_⟩
  simp only [diffPairOutP, diffPairOutN, diffPairOverdrive]
  rw [show (1 : ℝ) / 2500 / (1 / 2500) - d ^ 2 / 4 = 1 - d ^ 2 / 4 by
    norm_num]
  ring

/-! ## The 3-4-5 large-signal probe -/

/-- The probe overdrive is exactly rational BY DESIGN: `d = 6/5` puts
`1 − d²/4 = 16/25` on the 3-4-5 triangle. -/
private theorem probe_sqrt :
    Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) = 4 / 5 := by
  rw [show (1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4 = (4 / 5) ^ 2 by
    norm_num]
  exact Real.sqrt_sq (by norm_num)

private theorem probe_conducting :
    DiffPairConducting
      { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
        tailCurrent := 1 / 2500 } (6 / 5) := by
  show (6 / 5 : ℝ) ^ 2 < 2 * (1 / 2500 / (1 / 2500))
  norm_num

private theorem probe_window :
    DiffPairSaturationWindow
      { threshold := 1, beta := 1 / 2500, drainResistance := 10000,
        tailCurrent := 1 / 2500 } 5 (1 / 4) (6 / 5) := by
  show (1 : ℝ) / 4 + |(6 : ℝ) / 5| / 2 + 10000 * (1 / 2500) / 2 *
      (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500)) + |(6 : ℝ) / 5| / 2) ^ 2 ≤
    5 + 1
  rw [sqrt_ratio, show |(6 : ℝ) / 5| = 6 / 5 from abs_of_pos (by norm_num)]
  norm_num

/-- The 3-4-5 large-signal probe, derived: at differential drive `d = 6/5`
around `cm = 1/4` (inputs 17/20 and −7/20) every DC state sits at exactly
`outP = 27/25`, `outN = 123/25`, `tail = −31/20` — a 3.84 V differential
output, exactly rational BY DESIGN. -/
theorem diff_pair_probe {outP outN tail : ℝ}
    (hdc : DiffPairDC diffPairInstance 5 (17 / 20) (-(7 / 20))
      outP outN tail) :
    outP = 27 / 25 ∧ outN = 123 / 25 ∧ tail = -(31 / 20) := by
  rw [diffPairInstance_eq,
    show (17 : ℝ) / 20 = 1 / 4 + 6 / 5 / 2 by norm_num,
    show (-(7 / 20) : ℝ) = 1 / 4 - 6 / 5 / 2 by norm_num] at hdc
  obtain ⟨hP, hN, hT⟩ := diffPair_dc_op (by norm_num) (by norm_num)
    (by norm_num) probe_conducting probe_window hdc
  refine ⟨?_, ?_, ?_⟩
  · rw [hP]
    show (5 : ℝ) - 10000 * (1 / 2500 / 2 *
        (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) +
          6 / 5 / 2) ^ 2) = 27 / 25
    rw [probe_sqrt]; norm_num
  · rw [hN]
    show (5 : ℝ) - 10000 * (1 / 2500 / 2 *
        (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) -
          6 / 5 / 2) ^ 2) = 123 / 25
    rw [probe_sqrt]; norm_num
  · rw [hT]
    show (1 : ℝ) / 4 - 1 -
        Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) =
      -(31 / 20)
    rw [probe_sqrt]; norm_num

/-- Realizability twin for the probe: the exactly-rational probe state IS
a DC state of the physics relation. -/
theorem diff_pair_probe_realizable :
    DiffPairDC diffPairInstance 5 (17 / 20) (-(7 / 20))
      (27 / 25) (123 / 25) (-(31 / 20)) := by
  rw [diffPairInstance_eq,
    show (17 : ℝ) / 20 = 1 / 4 + 6 / 5 / 2 by norm_num,
    show (-(7 / 20) : ℝ) = 1 / 4 - 6 / 5 / 2 by norm_num,
    show (27 : ℝ) / 25 = 5 - 10000 * (1 / 2500 / 2 *
      (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) +
        6 / 5 / 2) ^ 2) by rw [probe_sqrt]; norm_num,
    show (123 : ℝ) / 25 = 5 - 10000 * (1 / 2500 / 2 *
      (Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) -
        6 / 5 / 2) ^ 2) by rw [probe_sqrt]; norm_num,
    show (-(31 / 20) : ℝ) = 1 / 4 - 1 -
      Real.sqrt ((1 : ℝ) / 2500 / (1 / 2500) - (6 / 5) ^ 2 / 4) by
      rw [probe_sqrt]; norm_num]
  exact diffPair_dc_transfer_realizable (by norm_num) (by norm_num)
    (by norm_num) probe_conducting probe_window

/-- The probe's differential output is exactly −96/25 = −3.84 V. -/
theorem diff_pair_probe_vod {outP outN tail : ℝ}
    (hdc : DiffPairDC diffPairInstance 5 (17 / 20) (-(7 / 20))
      outP outN tail) :
    outP - outN = -(96 / 25) := by
  obtain ⟨hP, hN, -⟩ := diff_pair_probe hdc
  rw [hP, hN]; norm_num

end Examples.spice.diff_pair.proof
