import LeanModels.Sv.CombEqTactic

/-!
# `sv_bridge`: the printed equations of `sv_equations` to Nat-indexed facts (WP-P3)

A synthetic stand-in for an `eq_*` hypothesis of `sv_equations` (the same index forms: `Int` affine
expressions of cast loop variables, 1-D reads through `Int.toNat`, 2-D reads through `rmN`), and the
Nat-indexed statement an arithmetic lemma would ask for. `sv_bridge e` introduces the binders of the goal,
instantiates `e` (premises by `omega`), and closes the goal by congruence along the Boolean structure with
`omega` on every index that differs.

Pinned: the five shapes the multiplier references use (a cast premise and a 2-D index, a 1-D `toNat`
read, a column window `rmN W r c0 + k`, the `with` clause, an explicit-argument instance) and the failure
message for a wrong index.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_bridge.bridge

/-- Casts, a premise, a 1-D read through `toNat` and a 2-D row `2 * k + 1`. -/
theorem bridge_casts (st : SvState) (N : Nat)
    (e : ∀ k : Nat, (k : Int) < (N : Int) + -1 → ∀ c : Nat, (c : Int) < 2 * (N : Int) →
      st.boolAt "S" (rmN (2 * (N : Int)) (2 * (k : Int) + 1) (c : Int)) =
        (st.boolAt "th" (2 * (k : Int) + 1).toNat &&
          st.boolAt "S" (rmN (2 * (N : Int)) ((k : Int) + 2) ((c : Int) + 1)))) :
    ∀ k, k < N - 1 → ∀ c, c < 2 * N →
      st.cell "S" (2 * (N : Int)) (2 * k + 1) c =
        (st.boolAt "th" (2 * k + 1) && st.cell "S" (2 * (N : Int)) (k + 2) (c + 1)) := by
  sv_bridge e

/-- A column window: `s[r][c0 +: n]` is read as `rmN W r c0 + k`. -/
theorem bridge_window (st : SvState) (N : Nat) (hN : 1 ≤ N)
    (e : ∀ k : Nat, k < N → st.boolAt "p" (N + k) =
      st.boolAt "S" (rmN ((N : Int) + 1) ((N : Int) + -1) 1 + k)) :
    ∀ j, j < N → st.boolAt "p" (N + j) = st.cell "S" ((N : Int) + 1) (N - 1) (j + 1) := by
  sv_bridge e

/-- The `with` clause: an input bit becomes the bit of the `BitVec`, and a packed `if` is resolved. -/
theorem bridge_with (st : SvState) (N : Nat) (x : BitVec N)
    (ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i)
    (e : ∀ k : Nat, k < N + 1 → st.boolAt "s" k = if k < N then st.boolAt "a" k else false) :
    ∀ j, j < N → st.cell "s" ((N : Int) + 1) 0 j = x.getLsbD j := by
  sv_bridge e with ba, if_pos

/-- An instance the goal does not bind: given explicitly. -/
theorem bridge_explicit (st : SvState) (N : Nat)
    (e : ∀ k : Nat, k < N + 1 → st.boolAt "s" k = if k < N then st.boolAt "a" k else false) :
    st.cell "s" ((N : Int) + 1) 0 N = false := by
  sv_bridge (e N (by omega)) with if_neg

-- A wrong index is an error that names the index equation (the goal asks for row `2 * k + 2`).
/--
error: sv_bridge: cannot prove the index equality
  ↑(2 * k✝ + 2) = 2 * ↑k✝ + 1
while matching the read
  st.boolAt "S" (rmN (2 * ↑N) ↑(2 * k✝ + 2) ↑c✝)
of the goal against
  st.boolAt "S" (rmN (2 * ↑N) (2 * ↑k✝ + 1) ↑c✝)
of the equation
-/
#guard_msgs (whitespace := lax) in
theorem bridge_wrong (st : SvState) (N : Nat) (hN : 1 ≤ N)
    (e : ∀ k : Nat, (k : Int) < (N : Int) + -1 → ∀ c : Nat, (c : Int) < 2 * (N : Int) →
      st.boolAt "S" (rmN (2 * (N : Int)) (2 * (k : Int) + 1) (c : Int)) = st.boolAt "X" c) :
    ∀ k, k < N - 1 → ∀ c, c < 2 * N →
      st.cell "S" (2 * (N : Int)) (2 * k + 2) c = st.boolAt "X" c := by
  sv_bridge e

-- A design that writes a constant where the arithmetic reads another net (`drop_carry`: `s[i][N] = 1'b0` instead of
-- `c[i][N]`) is an error that names the two sides, not a search that runs out of heartbeats.
/--
error: sv_bridge: the goal and the equation have different shapes here
  false
against
  st.boolAt "c" (rmN (↑N + 1) ↑i✝ ↑N)
-/
#guard_msgs (whitespace := lax) in
theorem bridge_shape (st : SvState) (N : Nat)
    (e : ∀ i : Nat, 1 ≤ (i : Int) → i < N →
      st.boolAt "s" (rmN ((N : Int) + 1) (i : Int) (N : Int)) = false) :
    ∀ i, 1 ≤ i → i < N → st.cell "s" ((N : Int) + 1) i N = st.cell "c" ((N : Int) + 1) i N := by
  sv_bridge e

/-- info: 'Examples.«system-verilog».comb_bridge.bridge.bridge_casts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bridge_casts

/-- info: 'Examples.«system-verilog».comb_bridge.bridge.bridge_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bridge_window

/-- info: 'Examples.«system-verilog».comb_bridge.bridge.bridge_with' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bridge_with

/-- info: 'Examples.«system-verilog».comb_bridge.bridge.bridge_explicit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bridge_explicit

end Examples.«system-verilog».comb_bridge.bridge
