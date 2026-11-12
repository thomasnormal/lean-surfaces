import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! E admission guard for an `always_comb` process beside unpacked memory.
The current memory profile does not execute this process kind, so it refuses it
at admission rather than skipping the process. -/
namespace Examples.«system-verilog».sem2.mem_always_comb_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 combE
  from "Examples/system-verilog/sem2/mem_always_comb_e/mem_always_comb_e.sv.json"

#guard match MemEDesign.ofPDesign combE.pdesign [] with
  | .unsupported msg => msg == "E memory route does not yet admit always_comb processes"
  | _ => false

end Examples.«system-verilog».sem2.mem_always_comb_e
