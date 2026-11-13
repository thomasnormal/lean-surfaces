import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcTactic

namespace Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 ordinaryStorageGate from
  "Examples/system-verilog/sem2/parameterized_unpacked_storage_ordinary_e/parameterized_unpacked_storage_ordinary_e.sv.json"

/-! The ordinary loaded family is checked directly as `CoreMemDesign`; no
scalar `Design2` lowering or array-cell expansion is involved. -/
def loadedStructure : Bool :=
  match ordinaryStorageGate.e 2 with
  | .ok d => decide (CoreMemDesign.Structure d)
  | _ => false

def loadedEquation : Bool :=
  match ordinaryStorageGate.e 2 with
  | .ok d => decide (CoreMemDesign.EquationGate d)
  | _ => false

#guard loadedStructure
#guard loadedEquation

end Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e
