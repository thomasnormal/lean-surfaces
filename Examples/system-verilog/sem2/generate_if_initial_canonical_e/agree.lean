import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generate_if_initial_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 generateIfInitial from
  "Examples/system-verilog/sem2/generate_if_initial_canonical_e/generate_if_initial_canonical_e.sv.json"

def outputAt (n : Int) : Res String := do
  let d ← PDesign.instantiateCoreMem generateIfInitial.pdesign [n]
  let s ← d.initialState
  .ok (SvState.showSignal (CoreMemState.view d s) "q")

#guard outputAt 1 == .ok "0"
#guard outputAt 0 == .ok "1"
#print axioms outputAt
end Examples.«system-verilog».sem2.generate_if_initial_canonical_e
