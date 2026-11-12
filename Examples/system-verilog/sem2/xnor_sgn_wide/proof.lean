import LeanModels.Sv.Ingest2

/-! The signed widening wall is represented by parser-shaped `SignedResize`
nodes around each `$signed` operand.  The E differential runner supplies the
cycle receipt against both pinned simulators. -/

namespace Examples.«system-verilog».sem2.xnor_sgn_wide

open LeanModels.Sv

load_design_sv2 xnorSgnWide
  from "Examples/system-verilog/sem2/xnor_sgn_wide/xnor_sgn_wide.sv.json"

#guard match xnorSgnWide.pdesign.processes with
  | [.assign "w" (.unary (.m0 .bnot) (.binary (.m0 .xor)
      (.signedResize _ (.cast true (.ident "ua")))
      (.signedResize _ (.cast true (.ident "ub")))))] => true
  | _ => false

end Examples.«system-verilog».sem2.xnor_sgn_wide
