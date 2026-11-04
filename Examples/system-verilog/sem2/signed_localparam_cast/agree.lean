/-
`DOUBLE_BIAS` is a signed packed localparam whose initializer is an
INT-class expression (`2 * BIAS`) narrowed by the assignment-like target.
The extractor keeps that source tree; Param2 evaluates it through `evalAssign`
at the declared 12-bit width for each parameter point.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.signed_localparam_cast.agree

open LeanModels.Sv

load_design_sv2 signed_localparam_cast from
  "Examples/system-verilog/sem2/signed_localparam_cast/signed_localparam_cast.sv.json"

#guard !(signed_localparam_cast.sem 4).hasUnsupported
#guard !(signed_localparam_cast.sem 8).hasUnsupported
#guard !(signed_localparam_cast.sem 12).hasUnsupported

end Examples.«system-verilog».sem2.signed_localparam_cast.agree
