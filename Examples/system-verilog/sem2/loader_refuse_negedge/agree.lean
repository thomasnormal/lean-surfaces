/- Clean-room loudness fixture: Ingest2 must refuse the retained event field
   instead of dropping it and assigning plain alwaysFF semantics. -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.loader_refuse_negedge.agree
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 loader_refuse_negedge from
  "Examples/system-verilog/sem2/loader_refuse_negedge/loader_refuse_negedge.sv.json"
end Examples.«system-verilog».sem2.loader_refuse_negedge.agree
