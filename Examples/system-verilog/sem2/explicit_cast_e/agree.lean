import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.explicit_cast_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 explicitCastE from "Examples/system-verilog/sem2/explicit_cast_e/explicit_cast_e.sv.json"
def design8 : Res MemEDesign := MemEDesign.ofPDesign explicitCastE.pdesign [8]
def design2 : Res MemEDesign := MemEDesign.ofPDesign explicitCastE.pdesign [2]
def run (d : MemEDesign) (s : MemEState) (x : LVec) : String := match d.step s [("x",x)] with | .ok s' => SvState.showSignal s'.scalar "y" | .error e => "ERROR:" ++ e
def rows (d : MemEDesign) : List String := [run d d.init (.ofNat 4 0), run d d.init (.ofNat 4 10), run d d.init (.lit "xxxx")]
#guard match design8 with | .ok d => d.processes.length == 1 | _ => false
#guard match design2 with | .ok d => d.processes.length == 1 | _ => false
#eval match design8, design2 with | .ok a, .ok b => rows a ++ rows b | _, _ => ["ERROR"]
end Examples.«system-verilog».sem2.explicit_cast_e
