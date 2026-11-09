import Examples.«system-verilog».comb_hier.gen
import LeanModels.Sv.CombProcTactic

/-!
# Module instances the hierarchy summary does not read, and why

The tactics read a design whose instances are all at module level through its flat twin (`comb_proof.lean`). The shapes
v1 does not read are refused, each with its reason:

* `neg/gen_loop.sv`: an instance inside a generate loop (one instance per iteration would make the child's sites a generate
  family whose names carry the loop index, which the summary does not build yet);
* `neg/wire_out.sv`: the halves of `halves.sv` with `wire` ports. The parent's output `y` is then a net driven by the
  instances' output ports; the extractor keeps that as a loud member (`PortSymbol:net-z`) and the instantiation refuses the
  connection (`PortConn:target`), so the design is refused below the tactics until the loader reads such a net. What is
  pinned is what the tactic says today.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_hier.comb_errors

load_design_sv2 gen_loop from "Examples/system-verilog/comb_hier/neg/gen_loop.sv.json"
load_design_sv2 wire_out from "Examples/system-verilog/comb_hier/neg/wire_out.sv.json"

/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: an instance sits inside the generate loop `g` (genvar `i`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (gen_loop.sem W) := by
  sv_structure

/--
error: sv_structure: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: the module has a member outside the semantic tier (`PortSymbol:net-z`: y), which the instantiation keeps as a loud process
-/
#guard_msgs (whitespace := lax) in
example (K : Nat) (hK : 1 ≤ K) (hR : (2 * K : Int) < 2147483648) : CombDesign (wire_out.sem (2 * K)) := by
  sv_structure

end Examples.«system-verilog».comb_hier.comb_errors
