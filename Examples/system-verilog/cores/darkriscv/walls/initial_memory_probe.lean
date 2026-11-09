import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

set_option maxRecDepth 100000 in
load_design_sv2 initial_memory_wall
  from "Examples/system-verilog/cores/darkriscv/walls/initial_memory.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def d : MemDesign2 :=
  initial_memory_wall.pdesign.instantiateMemD2 [8, 2]

-- The parser's Initial node is retained in the memory route and runs once at
-- time zero (§9.2.1), before the first sampled input.
#guard match d.processes with
  | [.initial (.block [.blockingAssignL (.arrayElem "mem" [.int 0]) (.lit _)]),
      .assign "q" (.arrayElem "mem" [.int 0])] => true
  | _ => false

#guard match runMem2 d 32 [[("clk", LVec.lit "0")]] with
  | .ok [st] => SvState.lookup st "q" == some (LVec.lit "00111100")
  | _ => false

#print axioms LeanModels.Sv.Kernel.runMem2
