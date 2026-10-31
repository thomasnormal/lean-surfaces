import Examples.«system-verilog».comb_ops.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_structure` on designs with the new operators (WP-G S2)

The operators of the second fragment change nothing in the structural stage: a site's reads are the
accesses of its right-hand side in textual order (a conditional's condition, then its two arms), and the
rank is chosen the same way (a write strictly before every read of it). `sv_structure?` prints the reads;
`ops_flat` is a flat netlist, so its obligations are decided and `sv_structure` returns no goal.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_ops.gen

namespace Examples.«system-verilog».comb_ops.comb_view

/-- The adder with `~` and `?:`: the same rank as `ripple_add`'s (the propagate cell `e[i]` ranks with the
carry-in, the carry cell and the sum cell of bit `i` rank `i + 1`, the carry-out `N + 1`). -/
theorem add_mux_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (add_mux.sem N) ∧ Acyclic (add_mux.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

/-- Every site of `ops_gen` reads inputs only: one rank for all. -/
theorem ops_gen_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (ops_gen.sem N) ∧ Acyclic (ops_gen.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- A flat netlist: the obligations are decided, nothing is returned. -/
theorem ops_flat_struct : CombDesign ops_flat.sem ∧ Acyclic ops_flat.sem := by
  sv_structure (rank := rippleRank (fun p => [0, 0, 1, 0, 2, 0, 1, 1].getD p 0) (fun _ _ _ => 0))

/-- The `always_comb` design, in the lowered shape. -/
theorem ops_proc_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (ops_proc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => [0, 1, 1, 0].getD p 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/--
info: sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  cin
  output s [N - 1 : 0]
  output cout
         c [N : 0]
         e [N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives c[0]   reads [cin]
  plain#1 : drives cout   reads [c[N]]
family `g_bit`: for i in [0, N):
  g_bit#0[i] : drives e[i]   reads [a[i], b[i]]
  g_bit#1[i] : drives c[i + 1]   reads [e[i], a[i], c[i]]
  g_bit#2[i] : drives s[i]   reads [e[i], c[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[N]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[N]; g_bit#1[i'] drives c[i' + 1]]
  rank(g_bit#0[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads e[i]; g_bit#0[i'] drives e[i']]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
  rank(g_bit#0[i']) < rank(g_bit#2[i])   [g_bit#2[i] reads e[i]; g_bit#0[i'] drives e[i']]
  rank(plain#0) < rank(g_bit#2[i])   [g_bit#2[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#2[i])   [g_bit#2[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
-/
#guard_msgs (info, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (add_mux.sem N) ∧ Acyclic (add_mux.sem N) := by
  sv_structure?
  exact add_mux_struct N hN

/--
info: sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  s
  output y_not [N - 1 : 0]
  output y_mux [N - 1 : 0]
  output y_xnor [N - 1 : 0]
  output y_nest [N - 1 : 0]
  output r_or
  output r_and
  output r_xor
  output r_nor
  output r_nand
  output r_xnor
  output z_lnot
  output q_land
  output q_lor
  output q_eq
  output q_ne
  output q_cond
plain sites (module-level assigns):
  plain#0 : drives y_not   reads [a]
  plain#1 : drives y_mux   reads [s, a, b]
  plain#2 : drives y_xnor   reads [a, b]
  plain#3 : drives y_nest   reads [s, a, a[0], b, a]
  plain#4 : drives r_or   reads [a]
  plain#5 : drives r_and   reads [b]
  plain#6 : drives r_xor   reads [a]
  plain#7 : drives r_nor   reads [b]
  plain#8 : drives r_nand   reads [a]
  plain#9 : drives r_xnor   reads [b]
  plain#10 : drives z_lnot   reads [b]
  plain#11 : drives q_land   reads [s, a[0]]
  plain#12 : drives q_lor   reads [a[0], b[0]]
  plain#13 : drives q_eq   reads [a, b]
  plain#14 : drives q_ne   reads [a[0], b[0]]
  plain#15 : drives q_cond   reads [a[0], b[0], a, b]
families: none
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
-/
#guard_msgs (info, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (ops_gen.sem N) ∧ Acyclic (ops_gen.sem N) := by
  sv_structure?
  exact ops_gen_struct N hN

/--
info: sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  v [N - 1 : 0]
  output y [N - 1 : 0]
  output z [N - 1 : 0]
  output w
         p [N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives p   reads [a, b]
  plain#1 : drives z   reads [p]
  plain#2 : drives y   reads [p[0], a[0], b[0], a, v, b, a, b, a, v]
  plain#3 : drives w   reads [a[0], b[0], v, a[0], b[0], v[0]]
families: none
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads p; plain#0 drives p]
  rank(plain#0) < rank(plain#2)   [plain#2 reads p[0]; plain#0 drives p]
-/
#guard_msgs (info, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (ops_proc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure?
  exact ops_proc_struct N hN

end Examples.«system-verilog».comb_ops.comb_view
