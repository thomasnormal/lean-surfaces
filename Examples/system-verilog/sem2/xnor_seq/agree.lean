/-
Examples/system-verilog/sem2/xnor_seq — ACCEPTED (WP-L2, 2026-10-30, `~^` / `^~`): `~^` in an `always_ff` body (NBA) and an `always_comb` body; the one input-port clock satisfies the WP-Q0 clock discipline.

  xnor_seq.sv      — the SystemVerilog source
  xnor_seq.sv.json — generated envelope (extractors/sv/extract.py --top xnor_seq)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.ClockGuard2

namespace Examples.«system-verilog».sem2.xnor_seq.agree

open LeanModels.Sv

load_design_sv2 xnor_seq from "Examples/system-verilog/sem2/xnor_seq/xnor_seq.sv.json"

#guard !(xnor_seq.sem 4).hasUnsupported
#guard (xnor_seq.sem 4).clockAdmits

end Examples.«system-verilog».sem2.xnor_seq.agree
