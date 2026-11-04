import Examples.«system-verilog».mul_array.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on the N x N -> 2N array multiplier (`Examples/system-verilog/mul_array`)

Acceptance test of the multi-loop, nested-loop, 2-D-array extension of the structural stage
(`docs/sv-comb-design.md` §7 step 8): for EVERY `N ≥ 1`, `CombDesign (mul_n.sem N)` and
`Acyclic (mul_n.sem N)` come from `sv_structure`, a LEXICOGRAPHIC rank over site identities
(row, column, phase), and one closing line,

    all_goals (intros; sv_rowmajor; omega)

instead of the ~1370 structural lines of `svgolf/tasks/mul/reference/mul_n.lean`.

The design has four module-level assigns (a whole-row fill, `c[0] = '0`, `t[0] = '0`, a concatenation
`s[0] = {1'b0, pp[0]}`, the output part select `p[2*N-1:N] = s[N-1][N:1]`), a nested pair of loops
over `pp[i][j]` (row stride `N`), a loop whose body holds an assign, an inner loop of three assigns
and another assign (`c[i][0]`, then `t/s/c[i][j]` with reads `s[i-1][j+1]`, then `s[i][N]`; row stride
`N + 1`), and the output loop. The one nonlinear fact — row-major order is lexicographic order —
is the library lemma `rmN_lt_iff`/`rmN_le_iff` (`CombViewArith.lean`); `sv_rowmajor` is the
player's explicit call that rewrites every row-major comparison with it (side conditions by
`omega`). Build: `lake build Examples.«system-verilog».mul_array.comb_view`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».mul_array.gen

namespace Examples.«system-verilog».mul_array.comb_view

/-! ## Positive: the multiplier, every `N ≥ 1` -/

theorem mul_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (mul_n.sem N) := by
  sv_structure
  all_goals (intros; sv_rowmajor; omega)

/-- The rank: a lexicographic key `(row, column, phase)` of each site identity. Partial products and
the zero rows come first; within a row, column by column: the propagate `t`, the carry `c`, then the
sum `s`; the row's top bit after its last column; the outputs last. -/
def mulKey (N : Nat) : SiteId → Key
  | .plain 0 => (0, 0, 1)                 -- s[0] = {1'b0, pp[0]}
  | .plain 1 => (0, 0, 0)                 -- c[0] = '0
  | .plain 2 => (0, 0, 0)                 -- t[0] = '0
  | .plain _ => (N, 0, 1)                 -- p[2*N-1:N] = s[N-1][N:1]
  | .fam "g_pp_j" _ _ => (0, 0, 0)        -- pp[i][j] = a[j] & b[i]
  | .fam "g_row" 0 [i] => (i.toNat, 0, 0) -- c[i][0] = 1'b0
  | .fam "g_row" _ [i] => (i.toNat, N, 0) -- s[i][N] = c[i][N]
  | .fam "g_bit" 0 [i, j] => (i.toNat, j.toNat, 1)   -- t[i][j]
  | .fam "g_bit" 1 [i, j] => (i.toNat, j.toNat, 3)   -- s[i][j]
  | .fam "g_bit" _ [i, j] => (i.toNat, j.toNat, 2)   -- c[i][j+1]
  | .fam _ _ _ => (N, 0, 0)               -- p[i] = s[i][0]

set_option maxHeartbeats 400000 in
theorem mul_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (mul_n.sem N) := by
  sv_structure (lexRank := mulKey N)
  all_goals (intros; sv_rowmajor; omega)

set_option maxHeartbeats 400000 in
/-- The same, the key written inline (the form the proof-golf players will use). -/
example (N : Nat) (hN : 1 ≤ N) : Acyclic (mul_n.sem N) := by
  sv_structure (lexRank := fun
    | .plain 0 => (0, 0, 1)
    | .plain 1 => (0, 0, 0)
    | .plain 2 => (0, 0, 0)
    | .plain _ => (N, 0, 1)
    | .fam "g_pp_j" _ _ => (0, 0, 0)
    | .fam "g_row" 0 [i] => (i.toNat, 0, 0)
    | .fam "g_row" _ [i] => (i.toNat, N, 0)
    | .fam "g_bit" 0 [i, j] => (i.toNat, j.toNat, 1)
    | .fam "g_bit" 1 [i, j] => (i.toNat, j.toNat, 3)
    | .fam "g_bit" _ [i, j] => (i.toNat, j.toNat, 2)
    | .fam _ _ _ => (N, 0, 0))
  all_goals (intros; sv_rowmajor; omega)

set_option maxHeartbeats 400000 in
/-- With the comb profile in hand (`using hc`) the one-driver obligation is not asked again. -/
theorem mul_acyclic_using (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (mul_n.sem N)) :
    Acyclic (mul_n.sem N) := by
  sv_structure (lexRank := mulKey N) using hc
  all_goals (intros; sv_rowmajor; omega)


/-- info: 'Examples.«system-verilog».mul_array.comb_view.mul_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_comb

/-- info: 'Examples.«system-verilog».mul_array.comb_view.mul_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_acyclic

/-- info: 'Examples.«system-verilog».mul_array.comb_view.mul_acyclic_using' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_acyclic_using

/-- info: 'LeanModels.Sv.CombView.Summary.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.Summary.sound

/-! ## The library lemma, used by hand

`sv_rowmajor` is a convenience; the nonlinear fact behind two-dimensional disjointness is the
library lemma `rmN_inj` (and its order versions `rmN_lt_iff`/`rmN_le_iff`), usable in one line. -/

/-- Two distinct cells of a row-major array are disjoint one-bit windows. -/
example (W i j i' j' : Int) (hi : 0 ≤ i) (hi' : 0 ≤ i') (hj : 0 ≤ j) (hjW : j < W) (hj' : 0 ≤ j')
    (hjW' : j' < W) (hne : ¬ (i = i' ∧ j = j')) :
    rmN W i j + 1 ≤ rmN W i' j' ∨ rmN W i' j' + 1 ≤ rmN W i j := by
  have := rmN_inj hi hi' hj hjW hj' hjW'
  have h1 := rmN_lt_iff hi hi' hj hjW (b := i') (d := j') hj' (by omega)
  have h2 := rmN_lt_iff hi' hi hj' hjW' (b := i) (d := j) hj (by omega)
  omega

/-- info: 'LeanModels.Sv.CombView.rmN_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.rmN_inj

/-- info: 'LeanModels.Sv.CombView.countRank_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.countRank_lt

/-- info: 'LeanModels.Sv.CombView.acyclic_of_lex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.acyclic_of_lex

/-- info: 'LeanModels.Sv.CombView.acyclic_using' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.acyclic_using

/-! ## The hint mode: loops (nested), site identities, windows, and the rank relation -/

/--
info: sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  output p [2*N - 1 : 0]
         pp [N - 1 : 0] [N - 1 : 0]
         s [N - 1 : 0] [N : 0]
         c [N - 1 : 0] [N : 0]
         t [N - 1 : 0] [N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives s[0]   reads [pp[0]]
  plain#1 : drives c[0]   reads []
  plain#2 : drives t[0]   reads []
  plain#3 : drives p[2*N - 1:N]   reads [s[N - 1][N:1]]
family `g_pp`: for i in [0, N):
  inner family `g_pp_j`: for j in [0, N):
    g_pp_j#0[i, j] : drives pp[i][j]   reads [a[j], b[i]]
family `g_row`: for i in [1, N):
  g_row#0[i] : drives c[i][0]   reads []
  inner family `g_bit`: for j in [0, N):
    g_bit#0[i, j] : drives t[i][j]   reads [s[i - 1][j + 1], pp[i][j]]
    g_bit#1[i, j] : drives s[i][j]   reads [t[i][j], c[i][j]]
    g_bit#2[i, j] : drives c[i][j + 1]   reads [s[i - 1][j + 1], pp[i][j], c[i][j], t[i][j]]
  g_row#2[i] : drives s[i][N]   reads [c[i][N]]
family `g_out`: for i in [0, N):
  g_out#0[i] : drives p[i]   reads [s[i][0]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(g_pp_j#0[i', j']) < rank(plain#0)   [plain#0 reads pp[0]; g_pp_j#0[i', j'] drives pp[i'][j']]
  rank(plain#0) < rank(plain#3)   [plain#3 reads s[N - 1][N:1]; plain#0 drives s[0]]
  rank(g_bit#1[i', j']) < rank(plain#3)   [plain#3 reads s[N - 1][N:1]; g_bit#1[i', j'] drives s[i'][j']]
  rank(g_row#2[i']) < rank(plain#3)   [plain#3 reads s[N - 1][N:1]; g_row#2[i'] drives s[i'][N]]
  rank(plain#0) < rank(g_bit#0[i, j])   [g_bit#0[i, j] reads s[i - 1][j + 1]; plain#0 drives s[0]]
  rank(g_bit#1[i', j']) < rank(g_bit#0[i, j])   [g_bit#0[i, j] reads s[i - 1][j + 1]; g_bit#1[i', j'] drives s[i'][j']]
  rank(g_row#2[i']) < rank(g_bit#0[i, j])   [g_bit#0[i, j] reads s[i - 1][j + 1]; g_row#2[i'] drives s[i'][N]]
  rank(g_pp_j#0[i', j']) < rank(g_bit#0[i, j])   [g_bit#0[i, j] reads pp[i][j]; g_pp_j#0[i', j'] drives pp[i'][j']]
  rank(plain#2) < rank(g_bit#1[i, j])   [g_bit#1[i, j] reads t[i][j]; plain#2 drives t[0]]
  rank(g_bit#0[i', j']) < rank(g_bit#1[i, j])   [g_bit#1[i, j] reads t[i][j]; g_bit#0[i', j'] drives t[i'][j']]
  rank(plain#1) < rank(g_bit#1[i, j])   [g_bit#1[i, j] reads c[i][j]; plain#1 drives c[0]]
  rank(g_row#0[i']) < rank(g_bit#1[i, j])   [g_bit#1[i, j] reads c[i][j]; g_row#0[i'] drives c[i'][0]]
  rank(g_bit#2[i', j']) < rank(g_bit#1[i, j])   [g_bit#1[i, j] reads c[i][j]; g_bit#2[i', j'] drives c[i'][j' + 1]]
  rank(plain#0) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads s[i - 1][j + 1]; plain#0 drives s[0]]
  rank(g_bit#1[i', j']) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads s[i - 1][j + 1]; g_bit#1[i', j'] drives s[i'][j']]
  rank(g_row#2[i']) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads s[i - 1][j + 1]; g_row#2[i'] drives s[i'][N]]
  rank(g_pp_j#0[i', j']) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads pp[i][j]; g_pp_j#0[i', j'] drives pp[i'][j']]
  rank(plain#1) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads c[i][j]; plain#1 drives c[0]]
  rank(g_row#0[i']) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads c[i][j]; g_row#0[i'] drives c[i'][0]]
  rank(g_bit#2[i', j']) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads c[i][j]; g_bit#2[i', j'] drives c[i'][j' + 1]]
  rank(plain#2) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads t[i][j]; plain#2 drives t[0]]
  rank(g_bit#0[i', j']) < rank(g_bit#2[i, j])   [g_bit#2[i, j] reads t[i][j]; g_bit#0[i', j'] drives t[i'][j']]
  rank(plain#1) < rank(g_row#2[i])   [g_row#2[i] reads c[i][N]; plain#1 drives c[0]]
  rank(g_row#0[i']) < rank(g_row#2[i])   [g_row#2[i] reads c[i][N]; g_row#0[i'] drives c[i'][0]]
  rank(g_bit#2[i', j']) < rank(g_row#2[i])   [g_row#2[i] reads c[i][N]; g_bit#2[i', j'] drives c[i'][j' + 1]]
  rank(plain#0) < rank(g_out#0[i])   [g_out#0[i] reads s[i][0]; plain#0 drives s[0]]
  rank(g_bit#1[i', j']) < rank(g_out#0[i])   [g_out#0[i] reads s[i][0]; g_bit#1[i', j'] drives s[i'][j']]
  rank(g_row#2[i']) < rank(g_out#0[i])   [g_out#0[i] reads s[i][0]; g_row#2[i'] drives s[i'][N]]
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (mul_n.sem N) := by
  sv_structure?
  exact mul_comb N hN

/-! ## Negative tests: each must be REJECTED, with the mathematical content that is wrong -/

/-- `N - 1` as a symbolic bound. -/
def nM1 : PExpr := .binary (.m0 .sub) (.paramRef "N" none) (.int 1)

/-- The loop header `for (g = c0; g < N; g++)`. -/
def loopTo (lbl : String) (g : String) (c0 : Int) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int c0) (.binary .slt (.genvarRef g) (.paramRef "N" none))
    (.unary .inc (.genvarRef g)) (some rc) body

/-- Every row writes `pp[0][j]`: rows `0` and `1` drive the same cell. -/
def ppSameCell : GenItem :=
  loopTo "g_pp" "i" 0 16 [loopTo "g_pp_j" "j" 0 16 [.process
    (.assignL (.arrayElem "pp" [.int 0, .genvarRef "j"])
      (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "j"))
        (.bitSel (.ident "b") (.genvarRef "i"))))]]

def badSameCell : PDesign :=
  { mul_n.pdesign with generates := ppSameCell :: mul_n.pdesign.generates.tail }

/--
error: sv_structure: the one-driver rule fails: `g_pp_j#0[0, 0]` drives pp[0] and `g_pp_j#0[1, 0]` drives pp[0], which share a bit (sampled at [N] = [2]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_same_cell (N : Nat) (hN : 1 ≤ N) :
    CombDesign (badSameCell.instantiateGD2 [(N : Int)]) := by
  sv_structure
  all_goals (intros; sv_rowmajor; omega)

/-- `c` declared with rows of `N` bits instead of `N + 1`: the carry cell `c[i][j+1]` of the last
column leaves its row (the row stride is wrong). -/
def badStride : PDesign :=
  { mul_n.pdesign with decls := mul_n.pdesign.decls.map fun d =>
      if d.name == "c" then
        { d with type := .packed [⟨nM1, .int 0⟩, ⟨nM1, .int 0⟩] (some 256) }
      else d }

/--
error: sv_structure: in-range obligation fails — `g_bit#2[1, 1]` accesses c[1][2], outside `c` which is declared [1:0][1:0] (sampled at [N] = [2]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem bad_stride (N : Nat) (hN : 1 ≤ N) :
    CombDesign (badStride.instantiateGD2 [(N : Int)]) := by
  sv_structure
  all_goals (intros; sv_rowmajor; omega)

/-- The propagate cell reads row `i + 1` instead of `i - 1`; `s` has `N + 1` rows so the read is in
range, but the row it reads is computed AFTER the cell. -/
def rowGenLater : GenItem :=
  loopTo "g_row" "i" 1 15
    [ .process (.assignL (.arrayElem "c" [.genvarRef "i", .int 0]) (.lit { bits := #[.l0] })),
      loopTo "g_bit" "j" 0 16
        [ .process (.assignL (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])
            (.binary (.m0 .xor)
              (.arrayElem "s" [.binary (.m0 .add) (.genvarRef "i") (.int 1),
                .binary (.m0 .add) (.genvarRef "j") (.int 1)])
              (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))),
          .process (.assignL (.arrayElem "s" [.genvarRef "i", .genvarRef "j"])
            (.binary (.m0 .xor) (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])
              (.arrayElem "c" [.genvarRef "i", .genvarRef "j"]))),
          .process (.assignL
            (.arrayElem "c" [.genvarRef "i", .binary (.m0 .add) (.genvarRef "j") (.int 1)])
            (.binary (.m0 .or)
              (.binary (.m0 .and)
                (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
                  .binary (.m0 .add) (.genvarRef "j") (.int 1)])
                (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))
              (.binary (.m0 .and) (.arrayElem "c" [.genvarRef "i", .genvarRef "j"])
                (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])))) ],
      .process (.assignL (.arrayElem "s" [.genvarRef "i", .paramRef "N" none])
        (.arrayElem "c" [.genvarRef "i", .paramRef "N" none])) ]

def badLaterRow : PDesign :=
  { mul_n.pdesign with
    decls := mul_n.pdesign.decls.map fun d =>
      if d.name == "s" then
        { d with type := .packed [⟨.paramRef "N" none, .int 0⟩, ⟨.paramRef "N" none, .int 0⟩] (some 272) }
      else d
    generates := [mul_n.pdesign.generates[0]!, rowGenLater, mul_n.pdesign.generates[2]!] }

/--
error: sv_structure: the rank does not decrease along a read: `g_bit#0[1, 0]` (rank (1, 0, 1)) reads a window of `s` driven by `g_bit#1[2, 1]` (rank (2, 1, 3), window s[9]); a driver must have a SMALLER rank than its reader (sampled at [N] = [3]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
  the read that forms the edge: `s[2][1]` of `g_bit#0[1, 0]`, written by `g_bit#1[2, 1]` (window s[9])
-/
#guard_msgs (whitespace := lax) in
theorem bad_later_row (N : Nat) (hN : 1 ≤ N) : Acyclic (badLaterRow.instantiateGD2 [(N : Int)]) := by
  sv_structure (lexRank := mulKey N)
  all_goals (intros; sv_rowmajor; omega)

/-- A key that ranks the sum cell BEFORE the propagate cell it reads. -/
def swappedKey (N : Nat) : SiteId → Key
  | .fam "g_bit" 1 [i, j] => (i.toNat, j.toNat, 0)
  | s => mulKey N s

/--
error: sv_structure: the rank does not decrease along a read: `g_bit#1[1, 0]` (rank (1, 0, 0)) reads a window of `c` driven by `g_row#0[1]` (rank (1, 0, 0), window c[3]); a driver must have a SMALLER rank than its reader (sampled at [N] = [2]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
  the read that forms the edge: `c[1][0]` of `g_bit#1[1, 0]`, written by `g_row#0[1]` (window c[3])
-/
#guard_msgs (whitespace := lax) in
theorem bad_key (N : Nat) (hN : 1 ≤ N) : Acyclic (mul_n.sem N) := by
  sv_structure (lexRank := swappedKey N)
  all_goals (intros; sv_rowmajor; omega)

end Examples.«system-verilog».mul_array.comb_view
