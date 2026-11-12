import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! Source-shape receipt for an out-of-order continuous-driver chain beside
memory.  This item records the risk for the general lane; it does not change
MemE or claim that the current one-pass profile has solved the ordering. -/
namespace Examples.«system-verilog».sem2.mem_order_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 orderE
  from "Examples/system-verilog/sem2/mem_order_e/mem_order_e.sv.json"

#guard match MemEDesign.ofPDesign orderE.pdesign [] with
  | .unsupported msg => msg.startsWith "Schedule:comb-source-order"
  | _ => false

end Examples.«system-verilog».sem2.mem_order_e
