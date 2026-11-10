import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.reset_event_iff

open LeanModels.Sv

load_design_sv2 resetEventIff
  from "Examples/system-verilog/sem2/reset_event_iff/reset_event_iff.sv.json"

-- Both reset polarities retain a named unsupported process; the two controls
-- without iff remain the existing asynchronous reset nodes.
#guard match resetEventIff.pdesign.processes with
  | [.unsupported "AlwaysPosedge:reset-iff" _,
     .unsupported "AlwaysPosedge:reset-iff" _,
     .alwaysFFR "clk" "rn" _ false,
     .alwaysFFR "clk" "rp" _ true] => true
  | _ => false
#guard resetEventIff.sem.hasUnsupported

end Examples.«system-verilog».sem2.reset_event_iff
