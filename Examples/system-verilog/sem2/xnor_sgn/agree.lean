/-
Examples/system-verilog/sem2/xnor_sgn — ACCEPTED (WP-L2, 2026-10-30, `~^` / `^~`): `~^` over signed operands: a signed pair at its own width, and a mixed pair (unsigned: the signed side is zero-extended). A signed pair into a WIDER target is the loud xnor_sgn_wide.

  xnor_sgn.sv      — the SystemVerilog source
  xnor_sgn.sv.json — generated envelope (extractors/sv/extract.py --top xnor_sgn)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_sgn.agree

open LeanModels.Sv

load_design_sv2 xnor_sgn from "Examples/system-verilog/sem2/xnor_sgn/xnor_sgn.sv.json"

#guard !(xnor_sgn.sem 4).hasUnsupported
#guard !(xnor_sgn.sem 8).hasUnsupported

end Examples.«system-verilog».sem2.xnor_sgn.agree
