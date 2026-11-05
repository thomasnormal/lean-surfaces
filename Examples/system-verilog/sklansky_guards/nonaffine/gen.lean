import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary
namespace Examples.«system-verilog».sklansky_guards.nonaffine.gen
open LeanModels.Sv LeanModels.Sv.CombView
load_design_sv2 nonaffine from "Examples/system-verilog/sklansky_guards/nonaffine/nonaffine.sv.json"
#guard nonaffine.pdesign.summary.toOption.isNone
end Examples.«system-verilog».sklansky_guards.nonaffine.gen
