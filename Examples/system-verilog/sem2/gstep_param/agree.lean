/-
Examples/system-verilog/sem2/gstep_param — REFUSED (loud, WP-L1, 2026-10-30): a parameter amount (`i = i + S`) is never read as `i++`, even where S is 1 at the defaults.
The extractor leaves the step as the `GenerateFor:step` Unsupported node (the cases2.json row `gstep_param`
is a loud-refusal row of that kind), and `load_design_sv2` refuses the envelope: the genvar sequence
cannot be computed (`stepDelta`: the step is outside the plus-or-minus-1 tier). Refusal pinned below.

  gstep_param.sv      — the SystemVerilog source
  gstep_param.sv.json — generated envelope (extractors/sv/extract.py --top gstep_param)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.gstep_param.agree

/-! The loader's message ends in the text `++` slash `--` tier, which a Lean doc comment cannot hold
(a slash-dash opens a nested comment), so the refusal is pinned two ways instead of verbatim: the
`error` is dropped, and the constant is then required to be ABSENT (`#check` of a defined constant
prints an `info`, which the second `#guard_msgs` rejects). The step node's own text is pinned
in `extractors/sv/test_generate_steps.py`. -/

#guard_msgs (drop error) in
load_design_sv2 gstep_param from "Examples/system-verilog/sem2/gstep_param/gstep_param.sv.json"

/-- error: Unknown identifier `gstep_param` -/
#guard_msgs (whitespace := lax) in
#check gstep_param

end Examples.«system-verilog».sem2.gstep_param.agree
