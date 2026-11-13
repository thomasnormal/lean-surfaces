import LeanModels.Sv.Ingest2
open LeanModels.Sv
open LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.memory_shape_a_canonical_e
load_design_sv2 memoryShapeAOrdinary
  from "Examples/system-verilog/sem2/memory_shape_a_canonical_e/memory_shape_a_canonical_e.sv.json"

/-! This is the ordinary user-facing route.  The result is canonical E
memory, so scalar `Design2.lowerComb` cannot be applied to it accidentally. -/
#check memoryShapeAOrdinary.sem
#guard match memoryShapeAOrdinary.sem 4 3 with
  | .ok d => d.memories.size == 1 && d.processes.size == 3
  | _ => false
end Examples.«system-verilog».sem2.memory_shape_a_canonical_e
