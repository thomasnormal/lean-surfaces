import Examples.«system-verilog».comb_case.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_structure` on a `case` (WP-G S3a)

The lowered design of a `case` is the one assign it computes, so `sv_structure` returns the same obligations
as for an `if` tree. The rank is the player's: each design here has one site that reads only inputs.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_case.gen

namespace Examples.«system-verilog».comb_case.comb_view

/-- The structure theorem of `case_mux` (a fixed-size design). -/
theorem case_mux_struct : ∃ d', case_mux.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- … and of `case_multi`, a design with a comma list and a repeated pattern. -/
theorem case_multi_struct : ∃ d', case_multi.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- The structure theorem of `case_gen`, for every `N ≥ 1`. -/
theorem case_gen_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (case_gen.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/--
info: sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  s
  output y [N - 1 : 0]
plain sites (module-level assigns):
family `g_bit`: for i in [0, N):
  g_bit#0[i] : drives y[i]   reads [s, a[i], b[i], b[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (case_gen.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure?
  all_goals sorry

end Examples.«system-verilog».comb_case.comb_view
