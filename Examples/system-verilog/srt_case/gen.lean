import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary
namespace Examples.«system-verilog».srt_case.gen
open LeanModels.Sv LeanModels.Sv.CombView
load_design_sv2 srt_case from "Examples/system-verilog/srt_case/srt_case.sv.json"
load_design_sv2 shift_param from "Examples/system-verilog/srt_case/shift_param.sv.json"
#guard srt_case.pdesign.summaryP.toOption.isSome
#guard srt_case.pdesign.summary.toOption.isNone
#guard (srt_case.sem 1).lowerComb.isSome
#guard shift_param.pdesign.summary.toOption.isSome
#guard (shift_param.sem 8).lowerComb.isSome
end Examples.«system-verilog».srt_case.gen
