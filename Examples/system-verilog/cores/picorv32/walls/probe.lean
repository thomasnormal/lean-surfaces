import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

set_option maxRecDepth 100000 in
load_design_sv2 unpacked_cpuregs_wall
  from "Examples/system-verilog/cores/picorv32/walls/unpacked_cpuregs.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 net_z_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/net_z_memory.sv.json"

#guard match (unpacked_cpuregs_wall.sem 32).processes with
  | #[.unsupported "Instantiate"
      "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"] => true
  | _ => false

#guard match (net_z_memory_wall.pdesign.instantiateMemD2 [4]).processes with
  | [.unsupported "Instantiate"
      "memory cycle route does not yet admit unsupported module members"] => true
  | _ => false

#guard net_z_memory_wall.pdesign.others == [("NetSymbol:net-z", "pcpi_mul_wr")]
