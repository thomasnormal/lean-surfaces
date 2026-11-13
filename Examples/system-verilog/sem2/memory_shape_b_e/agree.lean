import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.memory_shape_b_e
open LeanModels.Sv
load_design_sv2 memoryShapeB from
  "Examples/system-verilog/sem2/memory_shape_b_e/memory_shape_b_e.sv.json"
#guard match memoryShapeB.pdesign.instantiate2 [4, 3] with
  | .ok d => d.processes.toList.any (fun p =>
      match p with | .unsupported k _ => k == "Instance" | _ => false)
  | _ => false
end Examples.«system-verilog».sem2.memory_shape_b_e
