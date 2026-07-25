import LeanModels.Python.Surface
import Examples.«verilog-a».resistor.proof

open LeanModels.Circuit
open LeanModels.VerilogA

load_veriloga resistorModel from
  "Examples/verilog-a/resistor/resistor.va"

/-- The source contribution lowers to one typed oriented current equation. -/
theorem resistor_lowering :
    resistorModel.contributions = #[
      { target := .flow (va_branch! resistorModel "p" "n")
        expression :=
          .div (.potential (va_branch! resistorModel "p" "n"))
            (.parameter (va_parameter! resistorModel "resistance")) }] :=
  by proofs

/-- The imported model realizes Ohm's law for arbitrary real terminal
potentials, not merely the nominal simulator vectors. -/
theorem resistor_ohm (positive negative : ℝ) :
    resistorModel.Satisfies
      (Examples.«verilog-a».resistor.proof.resistorPoint
        positive negative) := by proofs

#print axioms resistor_lowering
#print axioms resistor_ohm
