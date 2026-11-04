/-
Examples/system-verilog/sem2/xnor_red — ACCEPTED (WP-L2, 2026-10-30, `~^` / `^~`): the reduction XNOR `~^a` / `^~a` (already admitted by the extractor; this directory pins it with rows `xnor_red*`, including x and z bits).

  xnor_red.sv      — the SystemVerilog source
  xnor_red.sv.json — generated envelope (extractors/sv/extract.py --top xnor_red)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_red.agree

open LeanModels.Sv

load_design_sv2 xnor_red from "Examples/system-verilog/sem2/xnor_red/xnor_red.sv.json"

#guard !(xnor_red.sem 4).hasUnsupported
#guard !(xnor_red.sem 8).hasUnsupported
-- both spellings are the one reduction node
#guard match (xnor_red.sem 4).processes.toList with
  | Process2.assign (.ident "r1") e1 :: Process2.assign (.ident "r2") e2 :: _ =>
      e1 == e2 && e1 == Expr2.reduce .xnor (.ident "a")
  | _ => false

end Examples.«system-verilog».sem2.xnor_red.agree
