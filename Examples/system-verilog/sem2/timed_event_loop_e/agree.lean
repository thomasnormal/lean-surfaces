import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.timed_event_loop_e
open LeanModels.Sv
load_design_sv2 timedEventLoopE from
  "Examples/system-verilog/sem2/timed_event_loop_e/timed_event_loop_e.sv.json"
#guard timedEventLoopE.pdesign.others == []
#guard match timedEventLoopE.sem.processes.toList with
  | [.alwaysComb (.block #[.blockingAssign (.ident "y") _, .block arms])] => arms.size == 8
  | _ => false
end Examples.«system-verilog».sem2.timed_event_loop_e
