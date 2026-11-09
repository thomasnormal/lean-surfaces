import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle
import LeanModels.Sv.HierarchyNode2

set_option maxRecDepth 100000 in
load_design_sv2 unpacked_cpuregs_wall
  from "Examples/system-verilog/cores/picorv32/walls/unpacked_cpuregs.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 net_z_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/net_z_memory.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 task_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/task_memory.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 task_memory_comments_wall
  from "Examples/system-verilog/cores/picorv32/walls/task_memory_comments.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 xz_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/xz_memory.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 nonliteral_initializer_wall
  from "Examples/system-verilog/cores/picorv32/walls/nonliteral_initializer.sv.json"

set_option maxRecDepth 100000 in
load_design_sv2 xz_conversion_memory_wall
  from "Examples/system-verilog/cores/picorv32/walls/xz_conversion_memory.sv.json"

#guard match (unpacked_cpuregs_wall.sem 32).processes with
  | #[.unsupported "Instantiate"
      "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"] => true
  | _ => false

private def cpuregsMem : LeanModels.Sv.Kernel.MemDesign2 :=
  unpacked_cpuregs_wall.pdesign.instantiateMemD2 [32]

#guard cpuregsMem.memDecls.length == 1
#guard cpuregsMem.processes.length == 2

#guard match (net_z_memory_wall.pdesign.instantiateMemD2 [4]).processes with
  | [.assign "q" (.arrayElem "mem" [.int 0])] => true
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

#guard task_memory_comments_wall.pdesign.others ==
  [("SubroutineSymbol:Subroutine",
    "task empty_statement;\n    // This task is used by the `assert directive in non-formal mode to\n    // avoid empty statement (which are unsupported by plain Verilog syntax).\n    begin end\n  endtask")]

#guard match (task_memory_comments_wall.pdesign.instantiateMemD2 [4]).processes with
  | [.unsupported "Instantiate"
      "memory cycle route does not yet admit unsupported module members"] => true
  | _ => false

#guard xz_memory_wall.pdesign.others ==
  [("IntegerLiteral:unsized-xz-parametric", "'bx")]

#guard match (xz_memory_wall.sem 32).processes with
  | #[.unsupported "Instantiate"
      "decl 'mem': unpacked array storage outside E (UnpackedDecl:memory)"] => true
  | _ => false

#guard match (xz_memory_wall.pdesign.instantiateMemD2 [4]).processes with
  | [.assign "q" (.arrayElem "mem" [.int 0]),
      .assignL (.arrayElem "mem" [.int 0]) (.lit _)] => true
  | _ => false

-- The admitted unsized `'bx` remains an x-valued memory cell and therefore
-- produces x on the continuous read; it is never turned into a convenient 0.
#guard match LeanModels.Sv.Kernel.runMem2 (xz_memory_wall.pdesign.instantiateMemD2 [4]) 32
    [[("clk", LeanModels.Sv.LVec.lit "0")]] with
  | .ok [st] => LeanModels.Sv.SvState.lookup st "q" == some (LeanModels.Sv.LVec.xVec 32)
  | _ => false

-- The ordinary flat family remains loud at this declaration boundary, while
-- the source-shaped memory route retains and executes the initializer once
-- before its first input sample.
#guard match nonliteral_initializer_wall.sem.processes with
  | #[.unsupported "Instantiate" _] => true
  | _ => false

#guard match (nonliteral_initializer_wall.pdesign.instantiateMemD2 []).initializers with
  | [("t", .resize 2 (.ident "a"))] => true
  | _ => false

#guard match LeanModels.Sv.Kernel.runMem2
    (nonliteral_initializer_wall.pdesign.instantiateMemD2 []) 32
    [[("a", LeanModels.Sv.LVec.lit "11")]] with
  | .ok [st] => LeanModels.Sv.SvState.lookup st "q" == some (LeanModels.Sv.LVec.lit "0x")
  | _ => false

#guard xz_conversion_memory_wall.pdesign.others ==
  [("ConversionExpression:xz-literal-parametric", "'bx"),
   ("IntegerLiteral:unsized-xz-parametric", "'bx")]

#guard (xz_conversion_memory_wall.sem 8).processes.toList.any fun p =>
  match p with
  | .unsupported "ConversionExpression:xz-literal-parametric" _ => true
  | _ => false

-- The conversion marker widens the unsized x site at the instantiated target
-- width, so the memory route remains all-x when N differs from the default.
#guard match (xz_conversion_memory_wall.pdesign.instantiateMemD2 [16]).processes with
  | [.assign "q" (.ident "mem[0]"), .assign "mem[0]" (.lit _)] => true
  | _ => false

#guard match LeanModels.Sv.Kernel.runMem2
    (xz_conversion_memory_wall.pdesign.instantiateMemD2 [16]) 32
    [[("clk", LeanModels.Sv.LVec.lit "0")]] with
  | .ok [st] => LeanModels.Sv.SvState.lookup st "q" == some (LeanModels.Sv.LVec.xVec 16)
  | _ => false
