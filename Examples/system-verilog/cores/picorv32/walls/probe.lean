import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

set_option maxRecDepth 100000 in
load_design_sv2 unpacked_cpuregs_wall
  from "Examples/system-verilog/cores/picorv32/walls/unpacked_cpuregs.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 net_z_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/net_z_memory.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 task_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/task_memory.sv.json"

#guard match (unpacked_cpuregs_wall.sem 32).processes with
  | #[.unsupported "Instantiate"
      "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"] => true
  | _ => false

private def cpuregsMem : LeanModels.Sv.Kernel.MemDesign2 :=
  unpacked_cpuregs_wall.pdesign.instantiateMemD2 [32]

#guard cpuregsMem.memDecls.length == 1
#guard cpuregsMem.processes.length == 2

#guard match (net_z_memory_wall.pdesign.instantiateMemD2 [4]).processes with
  | [.unsupported "Instantiate"
      "memory cycle route does not yet admit unsupported module members"] => true
  | _ => false

#guard net_z_memory_wall.pdesign.others == [("NetSymbol:net-z", "pcpi_mul_wr")]

#guard task_memory_wall.pdesign.others ==
  [("SubroutineSymbol:empty-task", "task empty_statement;\n    begin end\n  endtask")]

-- The memory adapter's admission is keyed to the extractor's exact empty-task
-- marker.  A general task marker remains a loud unsupported module member.
#guard LeanModels.Sv.Kernel.memAllowedOther
  ("SubroutineSymbol:empty-task", "task empty_statement;\n    begin end\n  endtask")
#guard !LeanModels.Sv.Kernel.memAllowedOther
  ("SubroutineSymbol:Subroutine", "task nonempty; begin q = 1; endtask")

private def taskMem : LeanModels.Sv.Kernel.MemDesign2 :=
  task_memory_wall.pdesign.instantiateMemD2 [4]

#guard match taskMem.processes with
  | .alwaysFF "clk" (.block [.block []]) :: .assign "q" (.arrayElem "mem" [.int 0]) :: _ => true
  | _ => false
