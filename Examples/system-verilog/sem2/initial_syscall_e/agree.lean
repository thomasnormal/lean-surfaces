import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.initial_syscall_e
open LeanModels.Sv
load_design_sv2 initialSyscallE from
  "Examples/system-verilog/sem2/initial_syscall_e/initial_syscall_e.sv.json"
#guard initialSyscallE.pdesign.others == []
#guard match initialSyscallE.pdesign.processes with
  | [.assign "y" (.ident "x"), .initial _] => true
  | _ => false
#guard match initialSyscallE.sem.processes.toList with
  | [.assign (.ident "y") (.ident "x"), .unsupported "T2:Initial" _] => true
  | _ => false
end Examples.«system-verilog».sem2.initial_syscall_e
