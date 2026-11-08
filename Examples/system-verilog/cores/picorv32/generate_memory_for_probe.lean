import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

set_option maxRecDepth 100000 in
load_design_sv2 picorv32_generate_memory_for
  from "Examples/system-verilog/cores/picorv32/generate_memory_for.sv.json"

def memoryRoute :=
  picorv32_generate_memory_for.pdesign.instantiateMemD2 [4]

#eval memoryRoute.processes

#guard match memoryRoute.processes with
  | [.assign "q" (.arrayElem "tap" [.int 0]),
     .assignL (.arrayElem "tap" [.int 0]) (.arrayElem "mem" [.int 0]),
     .assignL (.arrayElem "tap" [.int 1]) (.arrayElem "mem" [.int 1]),
     .assignL (.arrayElem "tap" [.int 2]) (.arrayElem "mem" [.int 2]),
     .assignL (.arrayElem "tap" [.int 3]) (.arrayElem "mem" [.int 3])] => true
  | _ => false
