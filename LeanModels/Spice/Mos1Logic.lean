import LeanModels.Spice.Mos1

/-!
# Static-CMOS logic derived from MOS1

These lemmas contain no netlist-specific assumptions. They prove Boolean
rail behavior from the Level-1 channel equation, KCL equations for standard
CMOS topologies, and an explicit 0--5 V operating envelope. Extracted examples
instantiate the equation predicates from their literal cards.
-/

namespace LeanModels.Spice

/-- NMOS current for the exact model used by the example decks. -/
noncomputable def mos1NCurrent (vgs vds : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .nmos, threshold := 1, beta := 1 / 10000, lambda := 0 }
    vgs vds

/-- PMOS current magnitude for the exact model used by the example decks. -/
noncomputable def mos1PCurrent (vsg vsd : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .pmos, threshold := 1, beta := 1 / 20000, lambda := 0 }
    vsg vsd

theorem mos1NCurrent_off {vgs vds : ℝ} (hoff : vgs ≤ 1) :
    mos1NCurrent vgs vds = 0 := by
  simp [mos1NCurrent, mos1ForwardCurrent, hoff]

theorem mos1PCurrent_off {vsg vsd : ℝ} (hoff : vsg ≤ 1) :
    mos1PCurrent vsg vsd = 0 := by
  simp [mos1PCurrent, mos1ForwardCurrent, hoff]

theorem mos1NCurrent_zero {vds : ℝ} (hvds : 0 ≤ vds) :
    mos1NCurrent 5 vds = 0 ↔ vds = 0 := by
  exact mos1ForwardCurrent_eq_zero_iff .nmos 1 (1 / 10000) 5 vds
    (by norm_num) (by norm_num) hvds

theorem mos1PCurrent_zero {vds : ℝ} (hvds : 0 ≤ vds) :
    mos1PCurrent 5 vds = 0 ↔ vds = 0 := by
  exact mos1ForwardCurrent_eq_zero_iff .pmos 1 (1 / 20000) 5 vds
    (by norm_num) (by norm_num) hvds

/-- The bounded output and KCL equation of a CMOS inverter. -/
def Mos1InverterEquations (input output : ℝ) : Prop :=
  (0 ≤ output ∧ output ≤ 5) ∧
  -mos1PCurrent (5 - input) (5 - output) +
      mos1NCurrent input output = 0

theorem mos1_inverter_from_equations {input output : ℝ} {bit : Bool}
    (hinput : input = logicVoltage bit)
    (hequations : Mos1InverterEquations input output) :
    output = logicVoltage (!bit) := by
  rcases hequations with ⟨houtput, hkcl⟩
  rcases bit with _ | _
  · simp [logicVoltage] at hinput ⊢
    subst input
    have hnoff : mos1NCurrent 0 output = 0 :=
      mos1NCurrent_off (by norm_num)
    rw [hnoff] at hkcl
    have hneg : -mos1PCurrent 5 (5 - output) = 0 := by
      simpa using hkcl
    have hpzero : mos1PCurrent 5 (5 - output) = 0 :=
      neg_eq_zero.mp hneg
    have hdrop :=
      (mos1PCurrent_zero (show 0 ≤ 5 - output by linarith)).mp hpzero
    linarith
  · simp [logicVoltage] at hinput ⊢
    subst input
    norm_num at hkcl
    have hpoff : mos1PCurrent 0 (5 - output) = 0 :=
      mos1PCurrent_off (by norm_num)
    rw [hpoff] at hkcl
    exact (mos1NCurrent_zero houtput.1).mp (by simpa using hkcl)

/-- Bounded internal nodes and KCL equations for a two-input CMOS NAND
followed by an inverter. -/
def Mos1AndEquations
    (left right nand series output : ℝ) : Prop :=
  (0 ≤ nand ∧ nand ≤ 5) ∧
  (0 ≤ series ∧ series ≤ 5) ∧
  Mos1InverterEquations nand output ∧
  (-mos1PCurrent (5 - left) (5 - nand) +
      -mos1PCurrent (5 - right) (5 - nand) +
      mos1NCurrent (left - series) (nand - series) = 0) ∧
  (-mos1NCurrent (left - series) (nand - series) +
      mos1NCurrent right series = 0)

theorem mos1_and_from_equations
    {left right : Bool} {nand series output : ℝ}
    (hequations :
      Mos1AndEquations (logicVoltage left) (logicVoltage right)
        nand series output) :
    output = logicVoltage (left && right) := by
  rcases hequations with
    ⟨bnand, bseries, hinverter, hnand, hseries⟩
  rcases left with _ | _ <;> rcases right with _ | _
  · simp [logicVoltage] at hnand hseries ⊢
    have hnoff : mos1NCurrent (-series) (nand - series) = 0 :=
      mos1NCurrent_off (by linarith [bseries.1])
    rw [hnoff] at hnand
    have hpzero : mos1PCurrent 5 (5 - nand) = 0 := by
      linear_combination (-1 / 2 : ℝ) * hnand
    have hnand5 : nand = 5 := by
      have hdrop :=
        (mos1PCurrent_zero (show 0 ≤ 5 - nand by linarith)).mp hpzero
      linarith
    exact mos1_inverter_from_equations (bit := true)
      (by simpa [logicVoltage] using hnand5) hinverter
  · simp [logicVoltage] at hnand hseries ⊢
    have hnoff : mos1NCurrent (-series) (nand - series) = 0 :=
      mos1NCurrent_off (by linarith [bseries.1])
    have hpoff : mos1PCurrent 0 (5 - nand) = 0 :=
      mos1PCurrent_off (by norm_num)
    rw [hnoff, hpoff] at hnand
    have hpzero : mos1PCurrent 5 (5 - nand) = 0 := by
      linear_combination -hnand
    have hnand5 : nand = 5 := by
      have hdrop :=
        (mos1PCurrent_zero (show 0 ≤ 5 - nand by linarith)).mp hpzero
      linarith
    exact mos1_inverter_from_equations (bit := true)
      (by simpa [logicVoltage] using hnand5) hinverter
  · simp [logicVoltage] at hnand hseries ⊢
    have hnbOff : mos1NCurrent 0 series = 0 :=
      mos1NCurrent_off (by norm_num)
    rw [hnbOff] at hseries
    have hnzero : mos1NCurrent (5 - series) (nand - series) = 0 := by
      linarith
    have hpoff : mos1PCurrent 0 (5 - nand) = 0 :=
      mos1PCurrent_off (by norm_num)
    rw [hpoff, hnzero] at hnand
    have hpzero : mos1PCurrent 5 (5 - nand) = 0 := by
      linear_combination -hnand
    have hnand5 : nand = 5 := by
      have hdrop :=
        (mos1PCurrent_zero (show 0 ≤ 5 - nand by linarith)).mp hpzero
      linarith
    exact mos1_inverter_from_equations (bit := true)
      (by simpa [logicVoltage] using hnand5) hinverter
  · simp [logicVoltage] at hnand hseries ⊢
    have hpoff : mos1PCurrent 0 (5 - nand) = 0 :=
      mos1PCurrent_off (by norm_num)
    rw [hpoff] at hnand
    have hnzero : mos1NCurrent (5 - series) (nand - series) = 0 := by
      linarith
    rw [hnzero] at hseries
    have hseries0 : series = 0 :=
      (mos1NCurrent_zero bseries.1).mp (by simpa using hseries)
    rw [hseries0] at hnzero
    have hnand0 : nand = 0 :=
      (mos1NCurrent_zero bnand.1).mp (by simpa using hnzero)
    exact mos1_inverter_from_equations (bit := false)
      (by simpa [logicVoltage] using hnand0) hinverter

/-- Bounded internal nodes and KCL equations for a two-input CMOS NOR
followed by an inverter. -/
def Mos1OrEquations
    (left right series nor output : ℝ) : Prop :=
  (0 ≤ series ∧ series ≤ 5) ∧
  (0 ≤ nor ∧ nor ≤ 5) ∧
  Mos1InverterEquations nor output ∧
  (-mos1PCurrent (5 - left) (5 - series) +
      mos1PCurrent (series - right) (series - nor) = 0) ∧
  (-mos1PCurrent (series - right) (series - nor) +
      mos1NCurrent left nor + mos1NCurrent right nor = 0)

theorem mos1_or_from_equations
    {left right : Bool} {series nor output : ℝ}
    (hequations :
      Mos1OrEquations (logicVoltage left) (logicVoltage right)
        series nor output) :
    output = logicVoltage (left || right) := by
  rcases hequations with
    ⟨bseries, bnor, hinverter, hseries, hnor⟩
  rcases left with _ | _ <;> rcases right with _ | _
  · simp [logicVoltage] at hseries hnor ⊢
    have hnOff : mos1NCurrent 0 nor = 0 :=
      mos1NCurrent_off (by norm_num)
    rw [hnOff] at hnor
    have hpbZero : mos1PCurrent series (series - nor) = 0 := by
      linear_combination -hnor
    rw [hpbZero] at hseries
    have hpaZero : mos1PCurrent 5 (5 - series) = 0 := by
      linear_combination -hseries
    have hseries5 : series = 5 := by
      have hdrop :=
        (mos1PCurrent_zero (show 0 ≤ 5 - series by linarith)).mp hpaZero
      linarith
    rw [hseries5] at hpbZero
    have hnor5 : nor = 5 := by
      have hdrop :=
        (mos1PCurrent_zero (show 0 ≤ 5 - nor by linarith)).mp
          (by simpa using hpbZero)
      linarith
    exact mos1_inverter_from_equations (bit := true)
      (by simpa [logicVoltage] using hnor5) hinverter
  · simp [logicVoltage] at hseries hnor ⊢
    have hpaOff : mos1PCurrent (series - 5) (series - nor) = 0 :=
      mos1PCurrent_off (by linarith [bseries.2])
    have hnOff : mos1NCurrent 0 nor = 0 :=
      mos1NCurrent_off (by norm_num)
    rw [hpaOff, hnOff] at hnor
    have hnZero : mos1NCurrent 5 nor = 0 := by linarith
    have hnor0 : nor = 0 := (mos1NCurrent_zero bnor.1).mp hnZero
    exact mos1_inverter_from_equations (bit := false)
      (by simpa [logicVoltage] using hnor0) hinverter
  · simp [logicVoltage] at hseries hnor ⊢
    have hpaOff : mos1PCurrent 0 (5 - series) = 0 :=
      mos1PCurrent_off (by norm_num)
    rw [hpaOff] at hseries
    have hpbZero : mos1PCurrent series (series - nor) = 0 := by
      linarith
    rw [hpbZero] at hnor
    have hnOff : mos1NCurrent 0 nor = 0 :=
      mos1NCurrent_off (by norm_num)
    rw [hnOff] at hnor
    have hnZero : mos1NCurrent 5 nor = 0 := by linarith
    have hnor0 : nor = 0 := (mos1NCurrent_zero bnor.1).mp hnZero
    exact mos1_inverter_from_equations (bit := false)
      (by simpa [logicVoltage] using hnor0) hinverter
  · simp [logicVoltage] at hseries hnor ⊢
    have hpaOff : mos1PCurrent 0 (5 - series) = 0 :=
      mos1PCurrent_off (by norm_num)
    have hpbOff : mos1PCurrent (series - 5) (series - nor) = 0 :=
      mos1PCurrent_off (by linarith [bseries.2])
    rw [hpbOff] at hnor
    have hnZero : mos1NCurrent 5 nor = 0 := by
      linear_combination (1 / 2 : ℝ) * hnor
    have hnor0 : nor = 0 := (mos1NCurrent_zero bnor.1).mp hnZero
    exact mos1_inverter_from_equations (bit := false)
      (by simpa [logicVoltage] using hnor0) hinverter

end LeanModels.Spice
