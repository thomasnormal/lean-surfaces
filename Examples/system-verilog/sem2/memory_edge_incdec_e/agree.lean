import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.memory_edge_incdec_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 memoryEdgeIncdecE from
  "Examples/system-verilog/sem2/memory_edge_incdec_e/memory_edge_incdec_e.sv.json"
#guard match MemEDesign.ofPDesign memoryEdgeIncdecE.pdesign [8,4] with
  | .ok d => d.memDecls.length == 1 && d.processes.length == 2
  | _ => false
end Examples.«system-verilog».sem2.memory_edge_incdec_e
