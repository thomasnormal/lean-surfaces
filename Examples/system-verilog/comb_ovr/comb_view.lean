import Examples.«system-verilog».comb_ovr.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_structure` on default-then-override bodies (WP-G S3b)

The lowered design of a default-then-override body is the one assign it computes, so `sv_structure` returns the
same obligations as for an `if/else` tree. The adder's structure theorem is the same one as `add_proc`'s, for every
`N ≥ 1`; the cell now reads `[a[i], p[i], c[i]]` (the statements in source order: the default first).
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_ovr.gen

namespace Examples.«system-verilog».comb_ovr.comb_view

/-- The structure theorem of the lowered adder, every `N ≥ 1`. -/
theorem add_ovr_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_ovr.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

/-- … and of the priority encoder (one site, reading only inputs). -/
theorem prio_enc_struct : ∃ d', prio_enc.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
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
         p [N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives c[0]   reads [cin]
  plain#1 : drives cout   reads [c[N]]
family `g_bit`: for i in [0, N):
  g_bit#0[i] : drives p[i]   reads [a[i], b[i]]
  g_bit#1[i] : drives c[i + 1]   reads [a[i], p[i], c[i]]
  g_bit#2[i] : drives s[i]   reads [p[i], c[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[N]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[N]; g_bit#1[i'] drives c[i' + 1]]
  rank(g_bit#0[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads p[i]; g_bit#0[i'] drives p[i']]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
  rank(g_bit#0[i']) < rank(g_bit#2[i])   [g_bit#2[i] reads p[i]; g_bit#0[i'] drives p[i']]
  rank(plain#0) < rank(g_bit#2[i])   [g_bit#2[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#2[i])   [g_bit#2[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_ovr.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure?
  all_goals sorry

end Examples.«system-verilog».comb_ovr.comb_view
