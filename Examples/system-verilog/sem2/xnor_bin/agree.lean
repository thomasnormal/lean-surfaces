/-
Examples/system-verilog/sem2/xnor_bin — ACCEPTED (WP-L2, 2026-10-30, `~^` / `^~`): the binary XNOR in its spellings `~^` and `^~`, on one-bit and vector operands, a wider target, an expression operand and a chain. The extractor lowers it to `~(a ^ b)`; the cases2.json rows `xnor_bin*` run it against Icarus 12 and the pinned Xcelium traces.

  xnor_bin.sv      — the SystemVerilog source
  xnor_bin.sv.json — generated envelope (extractors/sv/extract.py --top xnor_bin)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_bin.agree

open LeanModels.Sv

load_design_sv2 xnor_bin from "Examples/system-verilog/sem2/xnor_bin/xnor_bin.sv.json"

-- the design holds no loud process at several widths and passes the clock discipline (no edge process)
#guard !(xnor_bin.sem 1).hasUnsupported
#guard !(xnor_bin.sem 4).hasUnsupported
#guard !(xnor_bin.sem 8).hasUnsupported
#guard (xnor_bin.sem 4).clockAdmits

-- both spellings are ONE node: the processes of `y1 = a ~^ b` and `y2 = a ^~ b` carry equal expressions,
-- and they are `~(a ^ b)`
#guard match (xnor_bin.sem 4).processes.toList with
  | Process2.assign (.ident "y1") e1 :: Process2.assign (.ident "y2") e2 :: _ =>
      e1 == e2 && e1 == Expr2.unary .bnot (.binary .xor (.ident "a") (.ident "b"))
  | _ => false

-- the wider target extends the operands BEFORE the operator (`w = ~(resize a ^ resize b)`), so the
-- extension bits are `0 ~^ 0 = 1`
#guard match (xnor_bin.sem 4).processes.toList.find? (fun p => match p with
    | Process2.assign (.ident "w") _ => true | _ => false) with
  | some (Process2.assign _ (Expr2.unary .bnot (Expr2.binary .xor (Expr2.resize 8 _) (Expr2.resize 8 _)))) => true
  | _ => false

end Examples.«system-verilog».sem2.xnor_bin.agree
