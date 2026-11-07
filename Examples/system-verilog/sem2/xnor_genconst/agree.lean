/-
Examples/system-verilog/sem2/xnor_genconst — LOUD (WP-L2, 2026-10-30, `~^` / `^~`): `~^` in a generate condition is a symbolic-CONSTANT position and is not lowered; the envelope loads and `name.sem` is the loud error design (message pinned verbatim). Since 86ef9f787 ("make generate guards signed-int exact") the refusal comes from the generate integer-guard evaluator, so the pinned message is that evaluator's, not the old `BinaryExpression:BinaryXnor` node message the `.sv` header still quotes.

  xnor_genconst.sv      — the SystemVerilog source
  xnor_genconst.sv.json — generated envelope (extractors/sv/extract.py --top xnor_genconst)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_genconst.agree

open LeanModels.Sv

load_design_sv2 xnor_genconst from "Examples/system-verilog/sem2/xnor_genconst/xnor_genconst.sv.json"

#guard (xnor_genconst.sem 4).hasUnsupported
#guard match (xnor_genconst.sem 4).processes.toList with
  | [Process2.unsupported "Instantiate" msg] =>
      msg == "generate if: expression outside generate integer guards"
  | _ => false

end Examples.«system-verilog».sem2.xnor_genconst.agree
