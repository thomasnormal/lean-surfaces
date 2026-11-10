import Examples.«system-verilog».comb_hier.gen
import LeanModels.Sv.CombProcTactic

/-!
# Module instances the hierarchy summary does not read, and why

The tactics read a design whose instances are all at module level through its flat twin (`comb_proof.lean`). The shapes
v1 does not read are refused, each with its reason:

* `neg/gen_loop.sv`: an instance inside a generate loop (one instance per iteration would make the child's sites a generate
  family whose names carry the loop index, which the summary does not build yet);
* `neg/odd_split.sv`: the halves at an odd width, the low half `(W+1)/2` bits wide. The bounds read a quotient of a SUM,
  `(W+1)/2`; the affine forms the summary reads hold a quotient of ONE named constant by a positive literal (`W/2`,
  `hier_param.sv`), so the connection's window is refused. (The halves with `wire` ports, pinned here before, are now read:
  `wire_out.sv`, `hier_param.sv`.)
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_hier.comb_errors

load_design_sv2 gen_loop from "Examples/system-verilog/comb_hier/neg/gen_loop.sv.json"
load_design_sv2 odd_split from "Examples/system-verilog/comb_hier/neg/odd_split.sv.json"

/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (gen_loop.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a bound of `a[hi:lo]` is not affine (dynamic or nonlinear) (in the flat twin of this design: instance `lo`, the connection of port `a`)
-/
#guard_msgs (whitespace := lax) in
example (K : Nat) (hK : 1 ≤ K) (hR : (2 * K + 1 : Int) < 2147483648) : CombDesign (odd_split.sem (2 * K + 1)) := by
  sv_structure

end Examples.«system-verilog».comb_hier.comb_errors
