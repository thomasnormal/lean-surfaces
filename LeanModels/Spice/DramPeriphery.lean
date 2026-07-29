import LeanModels.Spice.DramBankDeck
import LeanModels.Spice.Mos1Logic
import LeanModels.Spice.DramPrecharge

/-!
# Physical contracts for DRAM-bank peripherals

These endpoint contracts use the same MOS1 channel equation as the source
deck.  They expose the KCL equations needed by bank composition, prove their
observable behavior, and separately exhibit operating points.
-/

namespace LeanModels.Spice

/-! ## Row decoder -/

/-- The transistor-level AND decoder has an operating point for every rail
input.  Internal voltages are witnesses, not assumptions in the contract. -/
theorem dramDecoder_realizable (left right : Bool) :
    ∃ nand series output,
      Mos1AndEquations (logicVoltage left) (logicVoltage right)
        nand series output := by
  cases left <;> cases right
  · exact ⟨5, 0, 0, by
      norm_num [logicVoltage, Mos1AndEquations, Mos1InverterEquations,
        mos1NCurrent, mos1PCurrent, mos1ForwardCurrent]⟩
  · exact ⟨5, 0, 0, by
      norm_num [logicVoltage, Mos1AndEquations, Mos1InverterEquations,
        mos1NCurrent, mos1PCurrent, mos1ForwardCurrent]⟩
  · exact ⟨5, 5, 0, by
      norm_num [logicVoltage, Mos1AndEquations, Mos1InverterEquations,
        mos1NCurrent, mos1PCurrent, mos1ForwardCurrent]⟩
  · exact ⟨0, 0, 5, by
      norm_num [logicVoltage, Mos1AndEquations, Mos1InverterEquations,
        mos1NCurrent, mos1PCurrent, mos1ForwardCurrent]⟩

/-! ## Full-swing transmission gate -/

noncomputable def dramNmosParams : Mos1Params :=
  { polarity := .nmos, threshold := 1, beta := 1 / 10000, lambda := 0 }

noncomputable def dramPmosParams : Mos1Params :=
  { polarity := .pmos, threshold := 1, beta := 1 / 20000, lambda := 0 }

/-- KCL at the undriven terminal of an enabled complementary pass gate. -/
noncomputable def DramTransmissionGateEquations
    (left right : ℝ) : Prop :=
  (0 ≤ left ∧ left ≤ 5) ∧
  (0 ≤ right ∧ right ≤ 5) ∧
  mos1TerminalCurrent dramNmosParams 5 left right +
      mos1TerminalCurrent dramPmosParams 0 left right = 0

/-- An enabled transmission gate equilibrates its two terminals throughout
the supply envelope.  The proof uses KCL plus nonnegativity of both physical
channel currents; no ideal-switch law is assumed. -/
theorem dramTransmissionGate_correct
    {left right : ℝ}
    (hequations : DramTransmissionGateEquations left right) :
    right = left := by
  rcases hequations with ⟨bleft, bright, hkcl⟩
  rcases lt_trichotomy left right with hleftRight | hequal | hrightLeft
  · have hnotRightLeft : ¬ right ≤ left := not_le.mpr hleftRight
    have hleftRightLe : left ≤ right := hleftRight.le
    unfold dramNmosParams dramPmosParams mos1TerminalCurrent at hkcl
    simp [hnotRightLeft, hleftRightLe] at hkcl
    have hn : 0 ≤ mos1ForwardCurrent
        { polarity := .nmos, threshold := 1,
          beta := 1 / 10000, lambda := 0 }
        (5 - left) (right - left) :=
      mos1ForwardCurrent_nonneg .nmos 1 (1 / 10000)
        (5 - left) (right - left) (by norm_num) (by linarith)
    have hp : 0 ≤ mos1ForwardCurrent
        { polarity := .pmos, threshold := 1,
          beta := 1 / 20000, lambda := 0 }
        right (right - left) :=
      mos1ForwardCurrent_nonneg .pmos 1 (1 / 20000)
        right (right - left) (by norm_num) (by linarith)
    by_cases hlow : left < 4
    · have hnzero : mos1ForwardCurrent
          { polarity := .nmos, threshold := 1,
            beta := 1 / 10000, lambda := 0 }
          (5 - left) (right - left) = 0 := by
        linarith
      have hdrop := (mos1ForwardCurrent_eq_zero_iff .nmos 1
        (1 / 10000 : ℝ) (5 - left) (right - left)
        (by norm_num) (by linarith) (by linarith)).mp hnzero
      linarith
    · have hpzero : mos1ForwardCurrent
          { polarity := .pmos, threshold := 1,
            beta := 1 / 20000, lambda := 0 }
          right (right - left) = 0 := by
        linarith
      have hdrop := (mos1ForwardCurrent_eq_zero_iff .pmos 1
        (1 / 20000 : ℝ) right (right - left)
        (by norm_num) (by linarith) (by linarith)).mp hpzero
      linarith
  · exact hequal.symm
  · have hnotLeftRight : ¬ left ≤ right := not_le.mpr hrightLeft
    have hrightLeftLe : right ≤ left := hrightLeft.le
    unfold dramNmosParams dramPmosParams mos1TerminalCurrent at hkcl
    simp [hnotLeftRight, hrightLeftLe] at hkcl
    have hn : 0 ≤ mos1ForwardCurrent
        { polarity := .nmos, threshold := 1,
          beta := 1 / 10000, lambda := 0 }
        (5 - right) (left - right) :=
      mos1ForwardCurrent_nonneg .nmos 1 (1 / 10000)
        (5 - right) (left - right) (by norm_num) (by linarith)
    have hp : 0 ≤ mos1ForwardCurrent
        { polarity := .pmos, threshold := 1,
          beta := 1 / 20000, lambda := 0 }
        left (left - right) :=
      mos1ForwardCurrent_nonneg .pmos 1 (1 / 20000)
        left (left - right) (by norm_num) (by linarith)
    by_cases hlow : right < 4
    · have hnzero : mos1ForwardCurrent
          { polarity := .nmos, threshold := 1,
            beta := 1 / 10000, lambda := 0 }
          (5 - right) (left - right) = 0 := by
        linarith
      have hdrop := (mos1ForwardCurrent_eq_zero_iff .nmos 1
        (1 / 10000 : ℝ) (5 - right) (left - right)
        (by norm_num) (by linarith) (by linarith)).mp hnzero
      linarith
    · have hpzero : mos1ForwardCurrent
          { polarity := .pmos, threshold := 1,
            beta := 1 / 20000, lambda := 0 }
          left (left - right) = 0 := by
        linarith
      have hdrop := (mos1ForwardCurrent_eq_zero_iff .pmos 1
        (1 / 20000 : ℝ) left (left - right)
        (by norm_num) (by linarith) (by linarith)).mp hpzero
      linarith

theorem dramTransmissionGate_realizable
    {voltage : ℝ} (hzero : 0 ≤ voltage) (hsupply : voltage ≤ 5) :
    DramTransmissionGateEquations voltage voltage := by
  refine ⟨⟨hzero, hsupply⟩, ⟨hzero, hsupply⟩, ?_⟩
  simp [dramNmosParams, dramPmosParams, mos1TerminalCurrent,
    mos1ForwardCurrent_zero_drop]

/-! ## Matched two-inverter sense path -/

noncomputable def dramSenseNCurrent (vgs vds : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .nmos, threshold := 1,
      beta := 1 / 10000, lambda := 0 } vgs vds

noncomputable def dramSensePCurrent (vsg vsd : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .pmos, threshold := 1,
      beta := 1 / 10000, lambda := 0 } vsg vsd

def DramMatchedInverterEquations (input output : ℝ) : Prop :=
  (0 ≤ output ∧ output ≤ 5) ∧
    -dramSensePCurrent (5 - input) (5 - output) +
      dramSenseNCurrent input output = 0

def DramSensePathEquations
    (input intermediate output : ℝ) : Prop :=
  DramMatchedInverterEquations input intermediate ∧
    DramMatchedInverterEquations intermediate output

theorem dramMatchedInverter_readZeroBand
    {output : ℝ}
    (hequations : DramMatchedInverterEquations (25 / 11) output) :
    4 ≤ output := by
  rcases hequations with ⟨bbound, hkcl⟩
  unfold dramSenseNCurrent dramSensePCurrent mos1ForwardCurrent at hkcl
  norm_num at hkcl
  by_cases hn : output ≤ 14 / 11 <;>
    by_cases hp : 5 ≤ 19 / 11 + output
  all_goals simp [hn, hp] at hkcl
  all_goals nlinarith

theorem dramMatchedInverter_readOneBand
    {output : ℝ}
    (hequations : DramMatchedInverterEquations (29 / 11) output) :
    output ≤ 1 := by
  rcases hequations with ⟨bbound, hkcl⟩
  unfold dramSenseNCurrent dramSensePCurrent mos1ForwardCurrent at hkcl
  norm_num at hkcl
  by_cases hn : output ≤ 18 / 11 <;>
    by_cases hp : 5 ≤ 15 / 11 + output
  all_goals simp [hn, hp] at hkcl
  all_goals nlinarith

theorem dramMatchedInverter_lowInput
    {input output : ℝ} (hinput : input ≤ 1)
    (hequations : DramMatchedInverterEquations input output) :
    output = 5 := by
  rcases hequations with ⟨bbound, hkcl⟩
  have hnzero : dramSenseNCurrent input output = 0 := by
    unfold dramSenseNCurrent mos1ForwardCurrent
    simp [hinput]
  rw [hnzero] at hkcl
  have hpzero : dramSensePCurrent (5 - input) (5 - output) = 0 := by
    linarith
  change mos1ForwardCurrent
    { polarity := .pmos, threshold := 1,
      beta := 1 / 10000, lambda := 0 }
    (5 - input) (5 - output) = 0 at hpzero
  have hdrop := (mos1ForwardCurrent_eq_zero_iff .pmos 1
    (1 / 10000) (5 - input) (5 - output)
    (by norm_num) (by linarith) (by linarith)).mp hpzero
  linarith

theorem dramMatchedInverter_highInput
    {input output : ℝ} (hinput : 4 ≤ input)
    (hequations : DramMatchedInverterEquations input output) :
    output = 0 := by
  rcases hequations with ⟨bbound, hkcl⟩
  have hpzero : dramSensePCurrent (5 - input) (5 - output) = 0 := by
    unfold dramSensePCurrent mos1ForwardCurrent
    simp [show 5 - input ≤ (1 : ℝ) by linarith]
  rw [hpzero] at hkcl
  have hnzero : dramSenseNCurrent input output = 0 := by
    linarith
  change mos1ForwardCurrent
    { polarity := .nmos, threshold := 1,
      beta := 1 / 10000, lambda := 0 }
    input output = 0 at hnzero
  exact (mos1ForwardCurrent_eq_zero_iff .nmos 1
    (1 / 10000) input output
    (by norm_num) (by linarith) bbound.1).mp hnzero

/-- A conservative low-side decision band.  Unlike the historical exact
`25/11` lemma, this consumes the interval delivered by finite-time
precharge and charge sharing. -/
theorem dramMatchedInverter_lowDecisionBand
    {input output : ℝ}
    (hinput0 : 0 ≤ input) (hinput : input ≤ 12 / 5)
    (hequations : DramMatchedInverterEquations input output) :
    4 ≤ output := by
  by_cases hcutoff : input ≤ 1
  · rw [dramMatchedInverter_lowInput hcutoff hequations]
    norm_num
  rcases hequations with ⟨houtput, hkcl⟩
  have hnOn : ¬ input ≤ (1 : ℝ) := hcutoff
  have hpOn : ¬ 5 - input ≤ (1 : ℝ) := by
    linarith
  unfold dramSenseNCurrent dramSensePCurrent mos1ForwardCurrent at hkcl
  simp only [hnOn, hpOn, if_false] at hkcl
  by_cases hnTriode : output ≤ input - 1 <;>
    by_cases hpTriode : 5 - output ≤ 5 - input - 1
  all_goals simp [hnTriode, hpTriode] at hkcl
  all_goals nlinarith

/-- Symmetric conservative high-side decision band. -/
theorem dramMatchedInverter_highDecisionBand
    {input output : ℝ}
    (hinput : 13 / 5 ≤ input) (hinput5 : input ≤ 5)
    (hequations : DramMatchedInverterEquations input output) :
    output ≤ 1 := by
  by_cases hcutoff : 4 ≤ input
  · rw [dramMatchedInverter_highInput hcutoff hequations]
    norm_num
  rcases hequations with ⟨houtput, hkcl⟩
  have hnOn : ¬ input ≤ (1 : ℝ) := by
    linarith
  have hpOn : ¬ 5 - input ≤ (1 : ℝ) := by
    linarith
  unfold dramSenseNCurrent dramSensePCurrent mos1ForwardCurrent at hkcl
  simp only [hnOn, hpOn, if_false] at hkcl
  by_cases hnTriode : output ≤ input - 1 <;>
    by_cases hpTriode : 5 - output ≤ 5 - input - 1
  all_goals simp [hnTriode, hpTriode] at hkcl
  all_goals nlinarith

theorem dramSensePath_readZero
    {intermediate output : ℝ}
    (hequations : DramSensePathEquations
      (25 / 11) intermediate output) :
    output = logicVoltage false :=
  by
    simp only [logicVoltage]
    exact dramMatchedInverter_highInput
      (dramMatchedInverter_readZeroBand hequations.1) hequations.2

theorem dramSensePath_readOne
    {intermediate output : ℝ}
    (hequations : DramSensePathEquations
      (29 / 11) intermediate output) :
    output = logicVoltage true :=
  by
    simp only [logicVoltage]
    exact dramMatchedInverter_lowInput
      (dramMatchedInverter_readOneBand hequations.1) hequations.2

/-- Finite-time precharge need not land at the exact nominal `5/2`.  Any
charge-sharing result in the proved low decision band is still sensed as
logical zero. -/
theorem dramSensePath_readZero_of_input_le
    {input intermediate output : ℝ}
    (hinput0 : 0 ≤ input) (hinput : input ≤ 12 / 5)
    (hequations : DramSensePathEquations input intermediate output) :
    output = logicVoltage false := by
  simp only [logicVoltage]
  exact dramMatchedInverter_highInput
    (dramMatchedInverter_lowDecisionBand hinput0 hinput hequations.1)
    hequations.2

/-- Symmetric high decision band for a stored one. -/
theorem dramSensePath_readOne_of_input_ge
    {input intermediate output : ℝ}
    (hinput : 13 / 5 ≤ input) (hinput5 : input ≤ 5)
    (hequations : DramSensePathEquations input intermediate output) :
    output = logicVoltage true := by
  simp only [logicVoltage]
  exact dramMatchedInverter_lowInput
    (dramMatchedInverter_highDecisionBand hinput hinput5 hequations.1)
    hequations.2

noncomputable def dramSenseReadZeroIntermediate : ℝ :=
  (36 + Real.sqrt 165) / 11

noncomputable def dramSenseReadOneIntermediate : ℝ :=
  (18 - Real.sqrt 99) / 11

theorem dramMatchedInverter_readZero_realizable :
    DramMatchedInverterEquations
      (25 / 11) dramSenseReadZeroIntermediate := by
  have hsquare : (Real.sqrt 165) ^ 2 = 165 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt 165 := Real.sqrt_nonneg _
  constructor
  · constructor <;>
      unfold dramSenseReadZeroIntermediate <;> nlinarith
  unfold dramSenseNCurrent dramSensePCurrent
    dramSenseReadZeroIntermediate mos1ForwardCurrent
  norm_num
  have hn : ¬ (36 + Real.sqrt 165) / 11 ≤ 14 / 11 := by
    nlinarith
  have hp : 5 ≤ 19 / 11 + (36 + Real.sqrt 165) / 11 := by
    nlinarith
  simp [hn, hp]
  nlinarith

theorem dramMatchedInverter_readOne_realizable :
    DramMatchedInverterEquations
      (29 / 11) dramSenseReadOneIntermediate := by
  have hsquare : (Real.sqrt 99) ^ 2 = 99 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt 99 := Real.sqrt_nonneg _
  constructor
  · constructor <;>
      unfold dramSenseReadOneIntermediate <;> nlinarith
  unfold dramSenseNCurrent dramSensePCurrent
    dramSenseReadOneIntermediate mos1ForwardCurrent
  norm_num
  have hn : (18 - Real.sqrt 99) / 11 ≤ 18 / 11 := by
    nlinarith
  have hp : ¬ 5 ≤ 15 / 11 + (18 - Real.sqrt 99) / 11 := by
    nlinarith
  simp [hn, hp]
  nlinarith

theorem dramMatchedInverter_zero_realizable
    {input : ℝ} (hinput : 4 ≤ input) (hsupply : input ≤ 5) :
    DramMatchedInverterEquations input 0 := by
  constructor
  · norm_num
  unfold dramSenseNCurrent dramSensePCurrent mos1ForwardCurrent
  have hp : 5 - input ≤ (1 : ℝ) := by linarith
  have hn : ¬ input ≤ (1 : ℝ) := by linarith
  have htriode : 0 ≤ input - 1 := by linarith
  simp [hp, hn, htriode]

theorem dramMatchedInverter_five_realizable
    {input : ℝ} (hzero : 0 ≤ input) (hinput : input ≤ 1) :
    DramMatchedInverterEquations input 5 := by
  constructor
  · norm_num
  unfold dramSenseNCurrent dramSensePCurrent mos1ForwardCurrent
  have hp : ¬ 5 - input ≤ (1 : ℝ) := by linarith
  have htriode : 0 ≤ 5 - input - 1 := by linarith
  simp [hinput, hp, htriode]

theorem dramSensePath_readZero_realizable :
    ∃ intermediate output,
      DramSensePathEquations (25 / 11) intermediate output := by
  refine ⟨dramSenseReadZeroIntermediate, 0,
    dramMatchedInverter_readZero_realizable, ?_⟩
  exact dramMatchedInverter_zero_realizable
    (dramMatchedInverter_readZeroBand
      dramMatchedInverter_readZero_realizable)
    dramMatchedInverter_readZero_realizable.1.2

theorem dramSensePath_readOne_realizable :
    ∃ intermediate output,
      DramSensePathEquations (29 / 11) intermediate output := by
  refine ⟨dramSenseReadOneIntermediate, 5,
    dramMatchedInverter_readOne_realizable, ?_⟩
  exact dramMatchedInverter_five_realizable
    dramMatchedInverter_readOne_realizable.1.1
    (dramMatchedInverter_readOneBand
      dramMatchedInverter_readOne_realizable)

/-- The static matched-inverter equations are inhabited for every rail-valid
input.  This is the non-vacuity result used when a transient phase supplies an
interval rather than one hard-coded voltage. -/
theorem dramMatchedInverter_realizable
    {input : ℝ} (hinput0 : 0 ≤ input) (hinput5 : input ≤ 5) :
    ∃ output, DramMatchedInverterEquations input output := by
  let fabricated : LoadedInverterInstance :=
    { nThreshold := 1
      pThreshold := 1
      nBeta := 1 / 10000
      pBeta := 1 / 10000
      loadCapacitance := 1 }
  obtain ⟨output, houtput⟩ :=
    loadedInverter_dc_exists fabricated
      (supply := 5) (input := input)
      (by norm_num) hinput0 hinput5 (by norm_num) (by norm_num)
  dsimp [fabricated, LoadedInverterDC] at houtput
  refine ⟨output, ?_⟩
  rcases houtput with ⟨houtput0, houtput5, hkcl⟩
  refine ⟨⟨houtput0, houtput5⟩, ?_⟩
  simp only [dramSenseNCurrent, dramSensePCurrent]
  change
    -mos1ForwardCurrent
        { polarity := .pmos, threshold := 1,
          beta := 1 / 10000, lambda := 0 }
        (5 - input) (5 - output) +
      mos1ForwardCurrent
        { polarity := .nmos, threshold := 1,
          beta := 1 / 10000, lambda := 0 }
        input output = 0
  linarith

/-- The complete two-inverter sense path is realizable for every rail-valid
input, independently of whether the input lies in a decision band. -/
theorem dramSensePath_realizable
    {input : ℝ} (hinput0 : 0 ≤ input) (hinput5 : input ≤ 5) :
    ∃ intermediate output,
      DramSensePathEquations input intermediate output := by
  obtain ⟨intermediate, hfirst⟩ :=
    dramMatchedInverter_realizable hinput0 hinput5
  obtain ⟨output, hsecond⟩ :=
    dramMatchedInverter_realizable hfirst.1.1 hfirst.1.2
  exact ⟨intermediate, output, hfirst, hsecond⟩

end LeanModels.Spice
