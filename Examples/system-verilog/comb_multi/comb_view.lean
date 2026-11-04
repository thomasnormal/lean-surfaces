import Examples.«system-verilog».comb_multi.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_structure` on an `always_comb` body that writes SEVERAL windows (WP-G S1b, gate c)

The summary reads such a body as ONE site: the head window is the first target, the others (`TSite.more`) follow in
source order, the reads are those of all of them. The lowered design is the one assign of all its windows, so the
obligations are the usual ones with one change: every window counts (in range, one driver per bit against every
other window AND within the body, no read of ANY window of the body, the rank is the site's).

* `add_proc_m` (the whole carry/sum cell in one body): the structure theorem for every `N ≥ 1`, with the same
  rank as `add_proc`'s (the cell is ranked by its bit);
* `multi_flat` (no generate loop): a default with an override for `y`, and `z`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_multi.gen

namespace Examples.«system-verilog».comb_multi.comb_view

/-- The structure theorem of the lowered adder whose cell is ONE two-window body, every `N ≥ 1`. -/
theorem add_proc_m_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_proc_m.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

/-- … and the flat two-window body (one site reading only inputs). -/
theorem multi_flat_struct :
    ∃ d', multi_flat.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
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
  g_bit#1[i] : drives c[i + 1] and s[i]   reads [p[i], c[i], a[i], p[i], c[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[N]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[N]; g_bit#1[i'] drives c[i' + 1]]
  rank(g_bit#0[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads p[i]; g_bit#0[i'] drives p[i']]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
  rank(g_bit#0[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads p[i]; g_bit#0[i'] drives p[i']]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]

-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_proc_m.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure?
  exact add_proc_m_struct N hN

end Examples.«system-verilog».comb_multi.comb_view
