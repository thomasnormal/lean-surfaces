import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.packed_enum_package.proof

open LeanModels.Sv

load_design_sv2 packedEnum from
  "Examples/system-verilog/sem2/packed_enum_package/packed_enum_package.sv.json"

#guard packedEnum.sem.decls.size == 2
#guard packedEnum.sem.decls[0]?.map (·.name) == some "mode"
#guard packedEnum.sem.decls[0]?.map (·.width) == some 2
#guard packedEnum.sem.decls[1]?.map (·.name) == some "y"
#guard packedEnum.sem.decls[1]?.map (·.width) == some 1
#guard packedEnum.sem.processes.size == 1
#guard match packedEnum.sem.processes[0]? with
  | some (Process2.assign (.ident "y") (Expr2.binary .eq (.ident "mode") (Expr2.lit v))) => v == LVec.ofNat 2 1
  | _ => false

end Examples.«system-verilog».sem2.packed_enum_package.proof
