import Examples.«system-verilog».lp_add.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on a ripple-carry adder with LOCALPARAMS (`Examples/system-verilog/lp_add`)

`lp_add.sv` defines `M = N - 1`, `H = (N + 1) / 2`, `R = N % 2`, `T = 2 * H - R` as `localparam
integer`s and uses them in a declaration (`logic [T:0] c`), a generate bound (`i < T`) and an index
(`c[M + 1]`). A localparam is one more named constant of the summary (`Summary.params` lists it after
the module parameters, `Summary.lps` keeps its definition): the obligations below are closed
statements over `Int` in which the definitions are inlined, `/` and `%` by a literal as `omega` reads
them, and the usual `intros; omega` closes every one (it needs `T = N`, which it derives from the
definitions). Pinned: the hint with its `localparams:` block, and the axioms.

Build: `lake build Examples.«system-verilog».lp_add.comb_view`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_add.gen

namespace Examples.«system-verilog».lp_add.comb_view

theorem lp_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_add.sem N) := by
  sv_structure
  all_goals (intros; omega)

theorem lp_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (lp_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)

/-- With the comb profile in hand the one-driver goals are not asked again. -/
theorem lp_acyclic_using (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (lp_add.sem N)) :
    Acyclic (lp_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    using hc
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».lp_add.comb_view.lp_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_comb

/-- info: 'Examples.«system-verilog».lp_add.comb_view.lp_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_acyclic

/-- info: 'Examples.«system-verilog».lp_add.comb_view.lp_acyclic_using' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_acyclic_using

-- The hint mode: the localparams, the declarations (`c` is `[T : 0]`), the families and the rank
-- relation.
/--
info: sv_structure: parameters [N]
localparams:
  M = N - 1
  H = (N + 1) / 2
  R = N % 2
  T = 2 * H - R
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  cin
  output s [N - 1 : 0]
  output cout
         c [T : 0]
plain sites (module-level assigns):
  plain#0 : drives c[0]   reads [cin]
  plain#1 : drives cout   reads [c[M + 1]]
family `g_bit`: for i in [0, T):
  g_bit#0[i] : drives s[i]   reads [a[i], b[i], c[i]]
  g_bit#1[i] : drives c[i + 1]   reads [a[i], b[i], c[i], a[i], b[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[M + 1]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[M + 1]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_add.sem N) := by
  sv_structure?
  exact lp_comb N hN

/-! ## Negative tests: the samples evaluate the localparams too -/

/-- `T` is one too large (`T = 2 * H - R + 1 = N + 1`): the loop writes `s[N]`, past the end. -/
def badLp : PDesign :=
  { lp_add.pdesign with localParams := lp_add.pdesign.localParams.map fun lp =>
      if lp.name = "T" then { lp with expr := .binary (.m0 .add) lp.expr (.int 1) } else lp }

/--
error: sv_structure: in-range obligation fails — `g_bit#0[1]` drives s[1], outside `s` which is only 1 bit(s) wide (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_lp (N : Nat) (hN : 1 ≤ N) : CombDesign (badLp.instantiateGD2 [(N : Int)]) := by
  sv_structure
  all_goals (intros; omega)

/--
error: sv_structure: the rank does not decrease along a read: `plain#1` (rank 0) reads a window of `c` driven by `g_bit#1[0]` (rank 0, window c[1]); a driver must have a SMALLER rank than its reader (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_rank (N : Nat) (hN : 1 ≤ N) : Acyclic (lp_add.sem N) := by
  sv_structure (rank := fun _ => 0)
  all_goals (intros; omega)

end Examples.«system-verilog».lp_add.comb_view
