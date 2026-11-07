import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

namespace Examples.«system-verilog».sem2.unpacked_memory_netz.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 memoryNetz from
  "Examples/system-verilog/sem2/unpacked_memory_netz/unpacked_memory_netz.sv.json"

#guard memoryNetz.pdesign.others == [("NetSymbol:net-z", "pcpi_mul_wr")]
private def memD : MemDesign2 := memoryNetz.pdesign.instantiateMemD2 [4]
#guard match memD.processes with
  | [.unsupported "Instantiate"
      "memory cycle route does not yet admit unsupported module members"] => true
  | _ => false

end Examples.«system-verilog».sem2.unpacked_memory_netz.agree
