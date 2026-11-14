import Examples.«system-verilog».gen_deep.gen
import LeanModels.Sv.CombViewTactic

/-!
# Two blocks with one label at one depth (`Examples/system-verilog/gen_deep/neg`)

`gen_deep_dup`: the blocks `g_x[0].g_b` and `g_y[0].g_b` are distinct scopes in SystemVerilog, but the summary names a
site by the label of its innermost block, its position there and its depth (`LSite.key`), so their sites would share
an identity; the structural check refuses the design, naming the two sites.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_deep.gen

namespace Examples.«system-verilog».gen_deep.comb_errors

/--
error: sv_structure: structural check failed:
  two sites share the identity (`g_b#0[i, j]` and `g_b#0[i, j]`): generate blocks need distinct labels
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (gen_deep_dup.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_deep.comb_errors
