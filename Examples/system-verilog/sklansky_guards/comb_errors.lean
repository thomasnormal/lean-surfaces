import Examples.«system-verilog».sklansky_guards.gen
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».sklansky_guards.gen
namespace Examples.«system-verilog».sklansky_guards.comb_errors
/-- The guarded generate (`if (i == 0)` inside the loop over `i`) is read: the condition is a guard (`==` of a genvar and
a literal), each arm's site is owed its obligations where its guard selects it, and the instantiation's value of the
condition is the guard's at every reached index (`guard_eval`, under the 32-bit range of `i`, from `hR`). The design was
refused here before the comb tactics read conditional generate constructs. -/
theorem guarded_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (guarded.sem N) := by
  sv_structure
  all_goals (intros; omega)
end Examples.«system-verilog».sklansky_guards.comb_errors
