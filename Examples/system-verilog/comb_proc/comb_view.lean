import Examples.«system-verilog».comb_proc.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_structure` on a design with an `always_comb` (WP-G, G2.2)

For every `N ≥ 1`: `∃ d', (add_proc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'` from
`sv_structure` plus a rank over site identities plus one-line `omega` goals — the same tactic, the same rank
syntax and the same closers as `ripple_add/comb_view.lean`, with ONE extra obligation, `noSelfRead` (no read
of the carry cell's body overlaps the window it writes). `sv_structure?` prints the sites (the carry cell
reads `p[i]`, `c[i]`, `a[i]` and drives `c[i + 1]`) and the rank relation.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_proc.gen

namespace Examples.«system-verilog».comb_proc.comb_view

/-- The structure theorem of the lowered design, every `N ≥ 1`. -/
theorem add_proc_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_proc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

/-- … and with a lexicographic key (the carry cell ranked by `(i + 1, 0, 0)`). -/
theorem add_proc_struct_lex (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_proc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (lexRank := fun
    | .plain 0 => (0, 0, 0)
    | .plain _ => (N + 1, 0, 0)
    | .fam _ 0 [_] => (0, 0, 0)
    | .fam _ _ [i] => (i.toNat + 1, 0, 0)
    | .fam _ _ _ => (0, 0, 0))
  all_goals (intros; omega)

/-- The comb profile alone (no rank). -/
theorem add_proc_comb (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (add_proc.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure
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
  g_bit#1[i] : drives c[i + 1]   reads [p[i], c[i], a[i]]
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
    ∃ d', (add_proc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure?
  exact add_proc_struct N hN

end Examples.«system-verilog».comb_proc.comb_view
