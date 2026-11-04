/-
A typed packed parameter default `'0` is an assignment-context fill.  The
constant evaluator applies the declared width at each point.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.unsized_param_literal.agree

open LeanModels.Sv

load_design_sv2 unsized_param_literal from
  "Examples/system-verilog/sem2/unsized_param_literal/unsized_param_literal.sv.json"

#guard !(unsized_param_literal.sem 4 0).hasUnsupported
#guard !(unsized_param_literal.sem 8 0).hasUnsupported
#guard !(unsized_param_literal.sem 12 0).hasUnsupported

end Examples.«system-verilog».sem2.unsized_param_literal.agree
