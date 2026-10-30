/-
Examples/system-verilog/sem2/gstep_nest — ACCEPTED (WP-L1, 2026-10-30): nested generate loops with assignment steps (`i = i + 1` outside, `j += 1` inside), N x M AND matrix.
`load_design_sv2` loads it and `name.sem` holds no loud process at the widths below. The
`harness/sv/cases2.json` rows named `gstep_nest*` run it against Icarus 12 and the pinned Xcelium trace.

  gstep_nest.sv      — the SystemVerilog source
  gstep_nest.sv.json — generated envelope (extractors/sv/extract.py --top gstep_nest)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.gstep_nest.agree

open LeanModels.Sv

load_design_sv2 gstep_nest from "Examples/system-verilog/sem2/gstep_nest/gstep_nest.sv.json"

#guard !(gstep_nest.sem 1 1).hasUnsupported
#guard (gstep_nest.sem 1 1).processes.size == 1

end Examples.«system-verilog».sem2.gstep_nest.agree
