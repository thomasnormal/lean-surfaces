import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.explicit_cast_signed_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 castE from "Examples/system-verilog/sem2/explicit_cast_signed_e/explicit_cast_signed_e.sv.json"
def d8 : Res MemEDesign := MemEDesign.ofPDesign castE.pdesign [8]
def d2 : Res MemEDesign := MemEDesign.ofPDesign castE.pdesign [2]
def run (d : MemEDesign) (x b : LVec) : String × String := match d.step d.init [("x",x),("b",b)] with | .ok s => (SvState.showSignal s.scalar "ys", SvState.showSignal s.scalar "yb") | .error e => ("ERROR:"++e,"ERROR:"++e)
def rows (d : MemEDesign) := [run d (.ofNat 4 0xf) (.ofNat 4 0xf), run d (.ofNat 4 1) (.ofNat 4 1), run d (.lit "xxxx") (.ofNat 4 3)]
#guard match d8 with | .ok _ => true | _ => false
#guard match d2 with | .ok _ => true | _ => false
#eval match d8,d2 with | .ok a,.ok b => rows a ++ rows b | _,_ => []
end Examples.«system-verilog».sem2.explicit_cast_signed_e
