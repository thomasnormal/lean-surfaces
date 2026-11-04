import Examples.«system-verilog».ripple_fa.gen
import LeanModels.Sv.CombProcTactic

/-!
# The `sv_comb` tactics refuse a design with module instances, and say so (WP-I step I0)

`ripple_fa.sv` instantiates `full_adder` once per bit. The loader (`load_design_sv2` builds
`ripple_fa.sem N := PDesign.instantiateHD2 …`), the scorer (it flattens) and the post-synthesis
check all accept it, and `gen.lean` proves its structure by hand for every `N`. The `sv_comb`
tactics have no summary for an instance yet (the design note `svgolf/design/hierarchy/WP-I-NOTE.md`
prices it): before this step the message was "cannot read a `load_design_sv2` family … off the
design", which does not mention instances. Both elaborators of `sv_structure` (the generic one and
the `always_comb` one), `sv_interface` and `sv_equations` now answer with the reason and the way out.

Build: `lake build Examples.«system-verilog».ripple_fa.comb_errors`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».ripple_fa.gen

namespace Examples.«system-verilog».ripple_fa.comb_errors

/--
error: sv_structure: this design instantiates modules, and the `sv_comb` tactics cannot summarize module instances yet. The loader, the scorer and the post-synthesis check accept such a design; the tactics do not. Flatten the design in the source (inline the instances into one module), or prove the structure by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof of a hierarchical adder)
-/
#guard_msgs (whitespace := lax) in
theorem fa_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_fa.sem N) := by
  sv_structure

/--
error: sv_structure: this design instantiates modules, and the `sv_comb` tactics cannot summarize module instances yet. The loader, the scorer and the post-synthesis check accept such a design; the tactics do not. Flatten the design in the source (inline the instances into one module), or prove the structure by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof of a hierarchical adder)
-/
#guard_msgs (whitespace := lax) in
theorem fa_both (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_fa.sem N) ∧ Acyclic (ripple_fa.sem N) := by
  sv_structure

/--
error: sv_equations: this design instantiates modules, and the `sv_comb` tactics cannot summarize module instances yet. The loader, the scorer and the post-synthesis check accept such a design; the tactics do not. Flatten the design in the source (inline the instances into one module), or prove the structure by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof of a hierarchical adder)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState) (heqs : CombEqs (ripple_fa.sem N) st)
    (hsh : StateShape (ripple_fa.sem N) st) (hc : CombDesign (ripple_fa.sem N))
    (ha : Acyclic (ripple_fa.sem N)) : True := by
  sv_equations
  trivial

end Examples.«system-verilog».ripple_fa.comb_errors
