import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.explicit_cast_two_state_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 explicitCastTwoStateE from "Examples/system-verilog/sem2/explicit_cast_two_state_e/explicit_cast_two_state_e.sv.json"
def rows (n : Int) : List String :=
  match MemEDesign.ofPDesign explicitCastTwoStateE.pdesign [n] with
  | .ok d => [0, 10, 15].map fun x => match d.step d.init [("x", LVec.ofNat 4 x)] with | .ok s => SvState.showSignal s.scalar "y" | .error e => "ERROR:" ++ e
  | _ => ["ERROR"]
#guard (rows 8).length == 3
#guard (rows 2).length == 3
#eval rows 8 ++ rows 2
end Examples.«system-verilog».sem2.explicit_cast_two_state_e
