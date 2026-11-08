import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_structure` on the word-level designs (WP-B2)

`+` and `-` change nothing in the structural stage: a site's reads are the accesses of its right-hand side in
textual order (an operand under a `Resize` marker is read like a bare one), and the rank is chosen the same way
(a write strictly before every read of it). `addw` writes `t` once and reads it twice: `t` ranks 0, `s` and `cout`
rank 1.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_word.gen

namespace Examples.«system-verilog».comb_word.comb_view

/-- Every site reads inputs only: one rank for all. -/
theorem add_same_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (add_same.sem N) ∧ Acyclic (add_same.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

theorem add_wide_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (add_wide.sem N) ∧ Acyclic (add_wide.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

theorem sub_wide_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (sub_wide.sem N) ∧ Acyclic (sub_wide.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

theorem addw_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (addw.sem N) ∧ Acyclic (addw.sem N) := by
  sv_structure (rank := rippleRank (fun p => [0, 1, 1].getD p 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **A sum in the leaves of an `always_comb` tree** (WP-B2 gate 2): the structure is the one of any single-window
body, every read is an input. -/
theorem addp_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    ∃ d', (addp.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-! ## Rows and part selects (WP-B2 gate 4a) -/

/-- **A chain of rows of a two-dimensional packed array** (`r[i + 1] = ~r[i]`, parameter dimensions): the extractor's
legacy `BitSel` over a two-dimensional base is a whole row, and the row-major offset is nonlinear in the stride, so the
structure goals close with `sv_rowmajor; omega` (the library lemma `rmN_lt_iff`), as in `mul_array`. -/
theorem row_chain_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (row_chain.sem N) ∧ Acyclic (row_chain.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; sv_rowmajor; omega)

/-- … over localparam dimensions, rows `2N` wide, … -/
theorem row_chain_lp_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648)
    (hRC : 2 * (N : Int) < 2147483648) :
    CombDesign (row_chain_lp.sem N) ∧ Acyclic (row_chain_lp.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; sv_rowmajor; omega)

/-- … and over literal dimensions (every label is a legacy `BitSel`, `r[0]` and `r[3]` included). -/
theorem row_chain_lit_struct :
    CombDesign (row_chain_lit.sem) ∧ Acyclic (row_chain_lit.sem) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else 4) (fun _ _ i => i.toNat + 1))
  all_goals (intros; sv_rowmajor; omega)

/-- **Literal-bound part selects**, read (in the parts of a concatenation, as a field) and written (a byte swap): one
rank, every read is an input. -/
theorem ps_rot_struct : CombDesign (ps_rot.sem) ∧ Acyclic (ps_rot.sem) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **Part selects whose bounds are affine in a genvar**: the four-bit windows `y[4*i+3:4*i]` of a generate loop. -/
theorem ps_gen_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (ps_gen.sem N) ∧ Acyclic (ps_gen.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_view.row_chain_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_chain_struct

/-- info: 'Examples.«system-verilog».comb_word.comb_view.row_chain_lp_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_chain_lp_struct

/-- info: 'Examples.«system-verilog».comb_word.comb_view.ps_rot_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ps_rot_struct

-- The hint mode: a row is printed as `r[i + 1]`, a part select as its window `x[hi:lo]`.
/--
info: sv_structure: parameters [N]
declarations:
  input  x [N - 1 : 0]
  output y [N - 1 : 0]
         r [N : 0] [N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives r[0]   reads [x]
  plain#1 : drives y   reads [r[N]]
family `g`: for i in [0, N):
  g#0[i] : drives r[i + 1]   reads [r[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads r[N]; plain#0 drives r[0]]
  rank(g#0[i']) < rank(plain#1)   [plain#1 reads r[N]; g#0[i'] drives r[i' + 1]]
  rank(plain#0) < rank(g#0[i])   [g#0[i] reads r[i]; plain#0 drives r[0]]
  rank(g#0[i']) < rank(g#0[i])   [g#0[i] reads r[i]; g#0[i'] drives r[i' + 1]]
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (row_chain.sem N) := by
  sv_structure?
  all_goals sorry

/--
info: sv_structure: parameters []
declarations:
  input  x [15 : 0]
  output r [15 : 0]
  output sw [15 : 0]
  output e [4 : 0]
plain sites (module-level assigns):
  plain#0 : drives r   reads [x[8:0], x[15:9]]
  plain#1 : drives sw[7:0]   reads [x[15:8]]
  plain#2 : drives sw[15:8]   reads [x[7:0]]
  plain#3 : drives e   reads [x[14:10]]
families: none
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example : CombDesign (ps_rot.sem) := by
  sv_structure?
  all_goals sorry

/-! ## A genvar as the amount of a shift (WP-B2 gate 4b) -/

/-- **`pp[i] = aw << i`**: the shift amount is a constant of the instance, so it is read like an unsized constant but
names the genvar, which the structural obligation checks is a loop variable in scope. -/
theorem shl_gen_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (shl_gen.sem N) ∧ Acyclic (shl_gen.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; sv_rowmajor; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_view.shl_gen_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shl_gen_struct

/-! ## Replication (WP-B2 gate 4c) -/

/-- **Zero padding `{ {K{1'b0}}, x }`**: the count is a parameter, a constant of the instance (its name is checked in
scope, its value non-negative: the new `InRangeObl` conjunct). -/
theorem repl_pad_struct (N K : Nat) (hN : 1 ≤ N) (hRN : (N : Int) < 2147483648) (hRK : (K : Int) < 2147483648) :
    CombDesign (repl_pad.sem N K) ∧ Acyclic (repl_pad.sem N K) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **The AND mask `a & {N{b[i]}}`** in a generate loop: one row of `pp` per `i`, every read is an input. -/
theorem repl_mask_struct (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (repl_mask.sem N) ∧ Acyclic (repl_mask.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; sv_rowmajor; omega)

/-- **Literal counts**: a replicated part select as a whole right-hand side, a replicated literal in a concatenation. -/
theorem repl_bits_struct : CombDesign (repl_bits.sem) ∧ Acyclic (repl_bits.sem) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_view.repl_pad_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repl_pad_struct

/-- info: 'Examples.«system-verilog».comb_word.comb_view.repl_mask_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repl_mask_struct

/-- info: 'Examples.«system-verilog».comb_word.comb_view.repl_bits_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repl_bits_struct

end Examples.«system-verilog».comb_word.comb_view
