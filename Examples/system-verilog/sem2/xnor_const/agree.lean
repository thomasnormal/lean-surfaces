/-
Examples/system-verilog/sem2/xnor_const — REFUSED (WP-L2, 2026-10-30, `~^` / `^~`): `~^` in a parameter default and in a localparam is a symbolic-CONSTANT position and is not lowered; `load_design_sv2` refuses at the defaults (message pinned verbatim).

  xnor_const.sv      — the SystemVerilog source
  xnor_const.sv.json — generated envelope (extractors/sv/extract.py --top xnor_const)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_const.agree

open LeanModels.Sv

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/xnor_const/xnor_const.sv.json' REFUSED — our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):
  defaults: parameter 'Q' default: unsupported node 'BinaryExpression:BinaryXnor' in a constant context
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 xnor_const from "Examples/system-verilog/sem2/xnor_const/xnor_const.sv.json"

end Examples.«system-verilog».sem2.xnor_const.agree
