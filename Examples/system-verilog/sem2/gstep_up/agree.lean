/-
Examples/system-verilog/sem2/gstep_up — ACCEPTED (WP-L1, 2026-10-30): four generate loops whose step is written `i = i + 1`, `i += 1`, `i = 1 + i` and `k = (k + 1)` (an outer genvar); each lowers to the step node of `i++`.
`load_design_sv2` loads it and `name.sem` holds no loud process at the widths below. The
`harness/sv/cases2.json` rows named `gstep_up*` run it against Icarus 12 and the pinned Xcelium trace.

  gstep_up.sv      — the SystemVerilog source
  gstep_up.sv.json — generated envelope (extractors/sv/extract.py --top gstep_up)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.gstep_up.agree

open LeanModels.Sv

load_design_sv2 gstep_up from "Examples/system-verilog/sem2/gstep_up/gstep_up.sv.json"

#guard !(gstep_up.sem 1).hasUnsupported
#guard (gstep_up.sem 1).processes.size == 4
#guard !(gstep_up.sem 4).hasUnsupported
#guard (gstep_up.sem 4).processes.size == 16
#guard !(gstep_up.sem 7).hasUnsupported
#guard (gstep_up.sem 7).processes.size == 28

end Examples.«system-verilog».sem2.gstep_up.agree
