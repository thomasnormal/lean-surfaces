import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

set_option maxRecDepth 100000 in
load_design_sv2 picorv32_generate_memory_for
  from "Examples/system-verilog/cores/picorv32/generate_memory_for.sv.json"

def memoryRoute :=
  picorv32_generate_memory_for.pdesign.instantiateMemD2 [4]

#eval memoryRoute.processes

example :
    memoryRoute.processes =
      [.unsupported "Instantiate" "memory cycle route does not yet admit generate members"] := by
  rfl
