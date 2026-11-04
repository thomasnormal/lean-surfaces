/-
Examples/system-verilog/sem2/xnor_sgn_wide — LOUD (WP-L2, 2026-10-30, `~^` / `^~`): a signed operand pair assigned to a WIDER target needs sign extension, which the tier does not have: the extractor leaves `ConversionExpression:width` (the same refusal as for `^`), the envelope loads, and the instantiated design carries the loud node.

  xnor_sgn_wide.sv      — the SystemVerilog source
  xnor_sgn_wide.sv.json — generated envelope (extractors/sv/extract.py --top xnor_sgn_wide)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_sgn_wide.agree

open LeanModels.Sv

load_design_sv2 xnor_sgn_wide from "Examples/system-verilog/sem2/xnor_sgn_wide/xnor_sgn_wide.sv.json"

#guard (xnor_sgn_wide.sem 4).hasUnsupported
#guard match (xnor_sgn_wide.sem 4).firstLoud with
  | some (k, _) => k == "ConversionExpression:width"
  | none => false

end Examples.«system-verilog».sem2.xnor_sgn_wide.agree
