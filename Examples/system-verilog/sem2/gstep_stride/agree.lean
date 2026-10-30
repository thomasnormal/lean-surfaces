/-
Examples/system-verilog/sem2/gstep_stride — REFUSED (loud, WP-L1, 2026-10-30): a stride-2 genvar step (`i += 2`) is not a plus-or-minus-1 step.
The extractor leaves the step as the `GenerateFor:step` Unsupported node (the cases2.json row `gstep_stride`
is a loud-refusal row of that kind), and `load_design_sv2` refuses the envelope: the genvar sequence
cannot be computed (`stepDelta`: the step is outside the plus-or-minus-1 tier). Refusal pinned below.

  gstep_stride.sv      — the SystemVerilog source
  gstep_stride.sv.json — generated envelope (extractors/sv/extract.py --top gstep_stride)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.gstep_stride.agree

/-! The loader's message ends in the text `++` slash `--` tier, which a Lean doc comment cannot hold
(a slash-dash opens a nested comment), so the refusal is pinned two ways instead of verbatim: the
`error` is dropped, and the constant is then required to be ABSENT (`#check` of a defined constant
prints an `info`, which the second `#guard_msgs` rejects). The step node's own text is pinned
in `extractors/sv/test_generate_steps.py`. -/

#guard_msgs (drop error) in
load_design_sv2 gstep_stride from "Examples/system-verilog/sem2/gstep_stride/gstep_stride.sv.json"

/-- error: Unknown identifier `gstep_stride` -/
#guard_msgs (whitespace := lax) in
#check gstep_stride

end Examples.«system-verilog».sem2.gstep_stride.agree
