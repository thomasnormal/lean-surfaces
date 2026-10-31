import LeanModels.Sv.CombEqTactic

/-!
# `sv_cover`, the 2-D rule (WP-P4)

Synthetic coverage goals of the shapes `sv_equations` produces for a 2-D array: the read is a cell
`rmN W R C` (here `s[i][0]`, `T[r][c]`), the writers are windows `rmN W r c₀ ≤ X ∧ X < rmN W r c₀ + wd`
of a plain assign (the packed row 0) and of generate loops (`∃ a b, …`). The rule solves the loop
indices from the read (`a := i.toNat`, `a := (r - N - 1) / 2` with the parity left to `omega`), states
the writer's condition, and walks the disjunction.

Pinned: a cell read with a plain row window and a loop writer, a read whose writer index needs a
division (the parity of the row), the error for a cell that no writer covers (it names the read and the
condition each writer would need), and the `#print axioms` of the proofs.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_bridge.cover

/-- The packed row 0 (a plain assign) or a cell of the row loop (`a ≥ 1`). -/
theorem cover_cell (N : Nat) (hN : 1 ≤ N) : ∀ (i : Int), 0 ≤ i → i < ↑N →
    (rmN ((N : Int) + 1) 0 0 ≤ rmN ((N : Int) + 1) i 0 ∧
        rmN ((N : Int) + 1) i 0 < rmN ((N : Int) + 1) 0 0 + (N + 1)) ∨
      ∃ a : Nat, 1 ≤ (a : Int) ∧ a < N ∧ ∃ b : Nat, b < N ∧
        rmN ((N : Int) + 1) a b ≤ rmN ((N : Int) + 1) i 0 ∧
          rmN ((N : Int) + 1) i 0 < rmN ((N : Int) + 1) a b + 1 := by
  sv_cover

/-- A tape: the sum rows `N + 2g + 1` or the carry rows `N + 2g + 2` of a generate loop over `g`. -/
theorem cover_parity (N : Nat) (r : Int) (hr : (N : Int) + 1 ≤ r) (hr2 : r < 3 * (N : Int) + -1)
    (c : Int) (hc0 : 0 ≤ c) (hc : c < 2 * (N : Int)) :
    (∃ g : Nat, (g : Int) < (N : Int) + -1 ∧ ∃ k : Nat, (k : Int) < 2 * (N : Int) ∧
        rmN (2 * (N : Int)) ((N : Int) + 2 * (g : Int) + 1) k ≤ rmN (2 * (N : Int)) r c ∧
          rmN (2 * (N : Int)) r c < rmN (2 * (N : Int)) ((N : Int) + 2 * (g : Int) + 1) k + 1) ∨
      ∃ g : Nat, (g : Int) < (N : Int) + -1 ∧ ∃ k : Nat, (k : Int) < 2 * (N : Int) ∧
        rmN (2 * (N : Int)) ((N : Int) + 2 * (g : Int) + 2) k ≤ rmN (2 * (N : Int)) r c ∧
          rmN (2 * (N : Int)) r c < rmN (2 * (N : Int)) ((N : Int) + 2 * (g : Int) + 2) k + 1 := by
  sv_cover

-- Row 0 is not written by anything (the plain window is missing): the error names the read.
/--
error: sv_cover: the cell is not covered
  rmN (↑N + 1) i✝ 0
needs, for one of its writers (witnesses solved from the read's index), one of:
  (1) 1 ≤ ↑i✝.toNat ∧
  i✝.toNat < N ∧ Int.toNat 0 < N ∧ ↑i✝.toNat = i✝ ∧ 0 ≤ 0 ∧ ↑(Int.toNat 0) ≤ 0 ∧ 0 < ↑(Int.toNat 0) + 1
and none of them follows from the hypotheses
-/
#guard_msgs (whitespace := lax) in
theorem cover_missing (N : Nat) (hN : 1 ≤ N) : ∀ (i : Int), 0 ≤ i → i < ↑N →
      ∃ a : Nat, 1 ≤ (a : Int) ∧ a < N ∧ ∃ b : Nat, b < N ∧
        rmN ((N : Int) + 1) a b ≤ rmN ((N : Int) + 1) i 0 ∧
          rmN ((N : Int) + 1) i 0 < rmN ((N : Int) + 1) a b + 1 := by
  sv_cover

/-- info: 'Examples.«system-verilog».comb_bridge.cover.cover_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cover_cell

/-- info: 'Examples.«system-verilog».comb_bridge.cover.cover_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cover_parity

end Examples.«system-verilog».comb_bridge.cover
