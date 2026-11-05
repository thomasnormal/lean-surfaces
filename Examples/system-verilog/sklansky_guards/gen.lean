import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary
namespace Examples.«system-verilog».sklansky_guards.gen
open LeanModels.Sv LeanModels.Sv.CombView
load_design_sv2 guarded from "Examples/system-verilog/sklansky_guards/guard.sv.json"
#guard guarded.pdesign.summary.toOption.isNone
#guard guarded.pdesign.generates.length == 1
end Examples.«system-verilog».sklansky_guards.gen
