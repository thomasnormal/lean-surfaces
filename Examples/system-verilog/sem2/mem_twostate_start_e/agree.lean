import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.mem_twostate_start_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 d from "Examples/system-verilog/sem2/mem_twostate_start_e/mem_twostate_start_e.sv.json"
def design : Res MemEDesign := MemEDesign.ofPDesign d.pdesign []
#guard match design with | .ok d => d.init.scalar.lookup "s[0]" == some (.ofNat 8 0) | _ => false
end Examples.«system-verilog».sem2.mem_twostate_start_e
