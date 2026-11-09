import Examples.«system-verilog».ripple_fa.gen
import LeanModels.Sv.CombProcTactic

/-!
# The `sv_comb` tactics refuse an instance inside a generate loop, and say why (WP-I step I0; hierarchy summary v1)

`ripple_fa.sv` instantiates `full_adder` once per bit, inside a generate loop. The loader (`load_design_sv2` builds
`ripple_fa.sem N := PDesign.instantiateHD2 …`), the scorer (it flattens) and the post-synthesis check all accept it, and
`gen.lean` proves its structure by hand for every `N`. Since the hierarchy summary (`CombHier.lean`) `sv_structure` and
`sv_equations` read a design whose instances are all at module level through its flat twin (`Examples/system-verilog/comb_hier`);
an instance inside a generate loop is outside v1, and both tactics answer with that reason (before WP-I step I0 the message
was "cannot read a `load_design_sv2` family … off the design", which does not mention instances).

Build: `lake build Examples.«system-verilog».ripple_fa.comb_errors`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».ripple_fa.gen

namespace Examples.«system-verilog».ripple_fa.comb_errors

/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g_bit` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
theorem fa_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_fa.sem N) := by
  sv_structure

/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g_bit` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
theorem fa_both (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_fa.sem N) ∧ Acyclic (ripple_fa.sem N) := by
  sv_structure

/--
error: sv_equations: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g_bit` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (st : SvState) (heqs : CombEqs (ripple_fa.sem N) st)
    (hsh : StateShape (ripple_fa.sem N) st) (hc : CombDesign (ripple_fa.sem N))
    (ha : Acyclic (ripple_fa.sem N)) : True := by
  sv_equations
  trivial

end Examples.«system-verilog».ripple_fa.comb_errors
