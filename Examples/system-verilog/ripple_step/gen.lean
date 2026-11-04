import LeanModels.Sv.Ingest2
import Examples.«system-verilog».ripple_add.gen

/-!
# `ripple_step` — the genvar step written as an assignment (WP-L1, 2026-10-30)

`ripple_step.sv` is `ripple_add.sv` with `for (i = 0; i < N; i = i + 1)` where `ripple_add` writes
`i++`. The extractor lowers the assignment spellings of the plus-or-minus-1 step (`g = g + 1`, `g = 1 + g`,
`g += 1`, `g = g - 1`, `g -= 1`) to the SAME step node as `g++` / `g--`
(`extractors/sv/extract.py`, `_genstep`), so the loaded `PDesign` carries exactly the generate items
of `ripple_add` — which is what the semantic tier (`stepDelta`), the family lemmas and the proof
tactics read. This file pins that, once, as `#guard`s on the two literal designs; `comb_proof.lean`
then proves the adder for every `N ≥ 1` with the unchanged tactics.
-/

namespace Examples.«system-verilog».ripple_step.gen

open LeanModels.Sv

load_design_sv2 ripple_step from "Examples/system-verilog/ripple_step/ripple_step.sv.json"

-- The assignment spelling and `i++` load the same design: same generate items, same declarations,
-- same processes (only the module name differs).
#guard ripple_step.pdesign.generates == Examples.«system-verilog».ripple_add.gen.ripple_add.pdesign.generates
#guard ripple_step.pdesign.decls == Examples.«system-verilog».ripple_add.gen.ripple_add.pdesign.decls
#guard { ripple_step.pdesign with name := "ripple_add" } == Examples.«system-verilog».ripple_add.gen.ripple_add.pdesign

-- … so the instantiations agree at every width we can afford to decide.
#guard (List.range 9).all fun n =>
  toString (repr (ripple_step.sem n).processes) ==
    toString (repr (Examples.«system-verilog».ripple_add.gen.ripple_add.sem n).processes)

end Examples.«system-verilog».ripple_step.gen
