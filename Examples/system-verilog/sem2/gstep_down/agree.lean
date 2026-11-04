/-
Examples/system-verilog/sem2/gstep_down — ACCEPTED (WP-L1, 2026-10-30): decreasing generate loops written `i = i - 1` and `j -= 1`; each lowers to the step node of `i--`.
`load_design_sv2` loads it and `name.sem` holds no loud process at the widths below. The
`harness/sv/cases2.json` rows named `gstep_down*` run it against Icarus 12 and the pinned Xcelium trace.

  gstep_down.sv      — the SystemVerilog source
  gstep_down.sv.json — generated envelope (extractors/sv/extract.py --top gstep_down)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.gstep_down.agree

open LeanModels.Sv

load_design_sv2 gstep_down from "Examples/system-verilog/sem2/gstep_down/gstep_down.sv.json"

#guard !(gstep_down.sem 1).hasUnsupported
#guard (gstep_down.sem 1).processes.size == 2
#guard !(gstep_down.sem 4).hasUnsupported
#guard (gstep_down.sem 4).processes.size == 8
#guard !(gstep_down.sem 6).hasUnsupported
#guard (gstep_down.sem 6).processes.size == 12

end Examples.«system-verilog».sem2.gstep_down.agree
