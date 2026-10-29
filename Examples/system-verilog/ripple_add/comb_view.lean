import Examples.«system-verilog».ripple_add.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on the N-bit ripple-carry adder (`Examples/system-verilog/ripple_add`)

Acceptance test of the structural stage (`docs/sv-comb-design.md` §7 steps 4 and 5): for EVERY
`N ≥ 1`, `CombDesign (ripple_add.sem N)` and `Acyclic (ripple_add.sem N)` come from
`sv_structure` plus a rank over site identities plus one-line `omega` goals — instead of the
~520 hand lines (`gen.lean`'s process-list/one-driver half + `proof.lean`'s structural half).

The design constant is the one `Examples/system-verilog/ripple_add/gen.lean` already loaded
(`load_design_sv2` is not repeated); only its `.olean` is imported, nothing of `svgolf/`.

Build: `lake build Examples.«system-verilog».ripple_add.comb_view`.

Moved here from `LeanModels/Sv/CombViewExample.lean`: `LeanModels` must not import `Examples`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».ripple_add.gen

namespace Examples.«system-verilog».ripple_add.comb_view

/-! ## Positive: the ripple-carry adder, every `N ≥ 1` -/

/-- `sv_structure` leaves only compact goals: the declared-range goals and the one-driver goals
(carry-in against carry cell, sum cell against sum cell, carry cell against carry cell); each is
one `omega`. -/
theorem ripple_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) := by
  sv_structure
  all_goals (intros; omega)

/-- … and two more for the rank (the rank is the player's: carry-in 0, bit `i`'s two cells
`i + 1`, carry-out `N + 1`, as a function of the SITE IDENTITY). -/
theorem ripple_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)

/-- With the comb profile in hand the one-driver goals are not asked again. -/
theorem ripple_acyclic_using (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (ripple_add.sem N)) :
    Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    using hc
  all_goals (intros; omega)

/-- … and the lexicographic rank works on one-index families too (key `(index, 0, phase)`). -/
example (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  sv_structure (lexRank := fun
    | .plain 0 => (0, 0, 0)
    | .plain _ => (N + 1, 0, 0)
    | .fam _ _ [i] => (i.toNat + 1, 0, 0)
    | .fam _ _ _ => (0, 0, 0))
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».ripple_add.comb_view.ripple_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_comb

/-- info: 'Examples.«system-verilog».ripple_add.comb_view.ripple_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_acyclic

/-- info: 'Examples.«system-verilog».ripple_add.comb_view.ripple_acyclic_using' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_acyclic_using

/-- info: 'LeanModels.Sv.CombView.Summary.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.Summary.sound

-- The hint mode: families, site identities, windows, and the rank relation.
/--
info: sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  cin
  output s [N - 1 : 0]
  output cout
         c [N : 0]
plain sites (module-level assigns):
  plain#0 : drives c[0]   reads [cin]
  plain#1 : drives cout   reads [c[N]]
family `g_bit`: for i in [0, N):
  g_bit#0[i] : drives s[i]   reads [a[i], b[i], c[i]]
  g_bit#1[i] : drives c[i + 1]   reads [a[i], b[i], c[i], a[i], b[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[N]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[N]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) := by
  sv_structure?
  exact ripple_comb N hN

/-! ## Negative tests: each must be REJECTED, with the mathematical content that is wrong -/

/-- Two copies of the sum template: both drive `s[i]` (overlapping writers). -/
def badOverlap : PDesign :=
  { ripple_add.pdesign with generates :=
    [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) (some 4) ([sumT, sumT, carryT].map GenItem.process)] }

/--
error: sv_structure: the one-driver rule fails: `g_bit#0[0]` drives s[0] and `g_bit#1[0]` drives s[0], which share a bit (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_overlap (N : Nat) (hN : 1 ≤ N) :
    CombDesign (badOverlap.instantiateGD2 [(N : Int)]) := by
  sv_structure
  all_goals (intros; omega)

/-- The carry cell drives `c[i+2]`: the last window is outside `c` (an in-range violation). -/
def carryT2 : PProcess :=
  match carryT with
  | .assignL _ r => .assignL (.bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 2))) r
  | p => p

def badRange : PDesign :=
  { ripple_add.pdesign with generates :=
    [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) (some 4) ([sumT, carryT2].map GenItem.process)] }

/--
error: sv_structure: in-range obligation fails — `g_bit#1[0]` drives c[2], outside `c` which is only 2 bit(s) wide (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_range (N : Nat) (hN : 1 ≤ N) :
    CombDesign (badRange.instantiateGD2 [(N : Int)]) := by
  sv_structure
  all_goals (intros; omega)

/-- A dynamic write `s[b]`: the driven window is not determined by the template. -/
def sumDyn : PProcess :=
  match sumT with
  | .assignL _ r => .assignL (.bitSel "s" (.ident "b")) r
  | p => p

def badDyn : PDesign :=
  { ripple_add.pdesign with generates :=
    [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) (some 4) ([sumDyn, carryT].map GenItem.process)] }

/--
error: sv_structure: outside the supported fragment — site `g_bit#0`: write to `s[…]` has a non-affine (dynamic) index: the driven window cannot be determined
-/
#guard_msgs (whitespace := lax) in
theorem bad_dyn (N : Nat) (hN : 1 ≤ N) :
    CombDesign (badDyn.instantiateGD2 [(N : Int)]) := by
  sv_structure
  all_goals (intros; omega)

-- A rank that does not decrease.
/--
error: sv_structure: the rank does not decrease along a read: `plain#1` (rank 0) reads a window of `c` driven by `g_bit#1[0]` (rank 0, window c[1]); a driver must have a SMALLER rank than its reader (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_rank (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  sv_structure (rank := fun _ => 0)
  all_goals (intros; omega)

end Examples.«system-verilog».ripple_add.comb_view
