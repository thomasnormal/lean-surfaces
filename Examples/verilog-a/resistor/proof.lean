import LeanModels.VerilogA.Surface
import Mathlib.Tactic

namespace Examples.«verilog-a».resistor.proof

open LeanModels.Circuit
open LeanModels.VerilogA

load_veriloga resistorModel from
  "Examples/verilog-a/resistor/resistor.va"

noncomputable def resistorPoint (positive negative : ℝ) : AnalogPoint :=
  { potential := fun port =>
      if port == va_port! resistorModel "p" then positive else negative
    potentialRate := fun _port => 0
    flow := fun _branch => (positive - negative) / 1000
    parameter := fun _parameter => 1000 }

/-- The elaborated contribution is the expected oriented Ohm-law equation,
with all source names resolved to typed IDs. -/
theorem resistor_lowering :
    resistorModel.contributions = #[
      { target := .flow (va_branch! resistorModel "p" "n")
        expression :=
          .div (.potential (va_branch! resistorModel "p" "n"))
            (.parameter (va_parameter! resistorModel "resistance")) }] := by
  rfl

/-- For every pair of terminal potentials, the corresponding Ohm-law current
is a genuine behavior of the imported Verilog-A component. -/
theorem resistor_ohm (positive negative : ℝ) :
    resistorModel.Satisfies (resistorPoint positive negative) := by
  constructor
  · exact resistorModel_valid
  · intro contribution hcontribution
    rw [resistor_lowering] at hcontribution
    simp only [Array.mem_singleton] at hcontribution
    subst contribution
    simp only [ContributionModel.sumFor]
    rw [resistor_lowering]
    simp (disch := decide) [ContributionTarget.value, ContributionExpr.evaluate,
      AnalogPoint.branchPotential, resistorPoint]
    · have hflow :
          ((ContributionTarget.flow
              { positive := PortId.mk 0, negative := PortId.mk 1 } ==
            ContributionTarget.flow
              { positive := PortId.mk 0, negative := PortId.mk 1 }) =
            true) := by decide
      have hpositive : ((PortId.mk 0 == PortId.mk 0) = true) := by
        decide
      have hnegative : ((PortId.mk 1 == PortId.mk 0) = false) := by
        decide
      rw [hflow, hpositive, hnegative]
      simp

#print axioms resistor_lowering
#print axioms resistor_ohm

end Examples.«verilog-a».resistor.proof
