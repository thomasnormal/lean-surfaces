import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

namespace Examples.«system-verilog».sem2.unpacked_memory_netz.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 memoryNetz from
  "Examples/system-verilog/sem2/unpacked_memory_netz/unpacked_memory_netz.sv.json"

private def memD : MemDesign2 := memoryNetz.pdesign.instantiateMemD2 [4]

#guard memD.memDecls.length == 1
#guard (memD.decls.find? (·.name == "pcpi_mul_wr")).map (·.isNet) == some true
#guard (memD.initState.scalar.find? (·.1 == "pcpi_mul_wr")).map (·.2.toBinString) == some "z"

end Examples.«system-verilog».sem2.unpacked_memory_netz.agree
