import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.memory_implicit_event_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 memoryImplicit from
  "Examples/system-verilog/sem2/memory_implicit_event_canonical_e/memory_implicit_event_canonical_e.sv.json"
#guard match PDesign.instantiateCoreMem memoryImplicit.pdesign [4,2] with
  | .ok d => d.processes.toList.any (fun p => match p with | .unsupported k _ => k == "ProceduralBlockSymbol:Always" | _ => false)
  | _ => false
end Examples.«system-verilog».sem2.memory_implicit_event_canonical_e
