/-!
# `sv_structure`: the arithmetic library (no `LeanModels.Sv` imports)

Facts the structural stage of `sv_comb` needs about row-major windows and lexicographic ranks. Nothing
here mentions an SV design: this file imports nothing, so promoting it to a language-neutral `Core`
module is a file move (`docs/sv-comb-design.md` §4).

## Row-major windows

A 2-D packed array `x[R-1:0][W-1:0]` is the flat vector whose bit `i * W + j` is `x[i][j]`.
`rmN W i j = i * W + j` is that offset, as a `Nat`, with the coordinates clamped at `0`
(`Int.toNat`) so that the offset is nonnegative by construction. The ONE nonlinear fact about it is
that the flattening is an order isomorphism onto the lexicographic order on `(row, column)`
(`rmN_lt_iff`, `rmN_le_iff`, `rmN_eq_iff`), provided the columns stay inside the row: a window
START has column `< W`, a window END has column `≤ W` (the end of a window is the offset one past
its last bit, which may be the start of the next row). Disjointness of two cells, a cell inside a
row, a cell inside a part select of a row: all of them are one of these three facts.

## Lexicographic keys and the rank they induce

`Acyclic` asks for a `Nat`-valued rank. A lexicographic hint `κ : site → Nat × Nat × Nat` (row,
column, phase) has no order-preserving map into `Nat` in general, but a DESIGN has finitely many
sites: the rank of a site is the NUMBER of sites with a smaller key (`countRank`). Strict key
decrease is then strict rank decrease (`countRank_lt`), with no bound, no multiplication and no
division. -/

namespace LeanModels.Sv
namespace CombView

/-! ## Row-major offsets -/

/-- Row-major bit offset of the cell `(i, j)` in rows of width `W`, clamped at `0`. -/
def rmN (W i j : Int) : Nat := i.toNat * W.toNat + j.toNat

theorem nat_rm_lt_iff {W a c b d : Nat} (hc : c < W) (hd : d ≤ W) :
    a * W + c < b * W + d ↔ a < b ∨ (a = b ∧ c < d) := by
  constructor
  · intro h
    by_cases hab : a < b
    · exact Or.inl hab
    · by_cases heq : a = b
      · subst heq
        exact Or.inr ⟨rfl, by omega⟩
      · have hba : b + 1 ≤ a := by omega
        have h1 : (b + 1) * W ≤ a * W := Nat.mul_le_mul_right W hba
        rw [Nat.add_mul] at h1
        omega
  · intro h
    rcases h with hab | ⟨rfl, hcd⟩
    · have hab' : a + 1 ≤ b := hab
      have h1 : (a + 1) * W ≤ b * W := Nat.mul_le_mul_right W hab'
      rw [Nat.add_mul] at h1
      omega
    · omega

theorem nat_rm_le_iff {W a c b d : Nat} (hc : c < W) (hd : d ≤ W) :
    b * W + d ≤ a * W + c ↔ b < a ∨ (b = a ∧ d ≤ c) := by
  constructor
  · intro h
    by_cases hba : b < a
    · exact Or.inl hba
    · by_cases heq : b = a
      · subst heq
        exact Or.inr ⟨rfl, by omega⟩
      · have hab : a + 1 ≤ b := by omega
        have h1 : (a + 1) * W ≤ b * W := Nat.mul_le_mul_right W hab
        rw [Nat.add_mul] at h1
        omega
  · intro h
    rcases h with hba | ⟨rfl, hdc⟩
    · have hba' : b + 1 ≤ a := hba
      have h1 : (b + 1) * W ≤ a * W := Nat.mul_le_mul_right W hba'
      rw [Nat.add_mul] at h1
      omega
    · omega

/-- **Row-major order is lexicographic**: a window start `(a, c)` (column `< W`) lies strictly
before a window end `(b, d)` (column `≤ W`) iff its row is smaller or the rows agree and its
column is. -/
theorem rmN_lt_iff {W a c b d : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc : c < W)
    (hd0 : 0 ≤ d) (hd : d ≤ W) :
    rmN W a c < rmN W b d ↔ a < b ∨ (a = b ∧ c < d) := by
  unfold rmN
  have h := nat_rm_lt_iff (a := a.toNat) (b := b.toNat) (c := c.toNat) (d := d.toNat)
    (W := W.toNat) (by omega) (by omega)
  rw [h]
  constructor <;> intro h' <;> omega

/-- … and a window end `(b, d)` (column `≤ W`) is at or before a window start `(a, c)`
(column `< W`) iff its row is smaller or the rows agree and its column is at most. -/
theorem rmN_le_iff {W a c b d : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc : c < W)
    (hd0 : 0 ≤ d) (hd : d ≤ W) :
    rmN W b d ≤ rmN W a c ↔ b < a ∨ (b = a ∧ d ≤ c) := by
  unfold rmN
  have h := nat_rm_le_iff (a := a.toNat) (b := b.toNat) (c := c.toNat) (d := d.toNat)
    (W := W.toNat) (by omega) (by omega)
  rw [h]
  constructor <;> intro h' <;> omega

/-- **Row-major injectivity** (the nonlinear fact behind 2-D disjointness): two cells with the
same flat offset are the same cell. -/
theorem rmN_inj {W a c b d : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc : c < W)
    (hd0 : 0 ≤ d) (hd : d < W) (h : rmN W a c = rmN W b d) : a = b ∧ c = d := by
  have h1 : rmN W a c < rmN W b d ↔ a < b ∨ (a = b ∧ c < d) :=
    rmN_lt_iff ha hb hc0 hc hd0 (by omega)
  have h2 : rmN W b d < rmN W a c ↔ b < a ∨ (b = a ∧ d < c) :=
    rmN_lt_iff hb ha hd0 hd hc0 (by omega)
  have h3 : ¬ rmN W a c < rmN W b d := by omega
  have h4 : ¬ rmN W b d < rmN W a c := by omega
  rw [h1] at h3
  rw [h2] at h4
  omega

/-- A window `[c, c + k)` of row `r` is the window `[c, c + k)` of the flat vector: its end is the
offset of column `c + k`. -/
theorem rmN_add_col {W r c : Int} (k : Nat) (hc : 0 ≤ c) : rmN W r c + k = rmN W r (c + (k : Int)) := by
  unfold rmN
  omega

/-- The flat offset of a cell is nonnegative (the cast direction). -/
theorem rmN_cast {W i j : Int} (hW : 0 ≤ W) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    ((rmN W i j : Nat) : Int) = i * W + j := by
  unfold rmN
  have h1 : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hi
  have h2 : ((W.toNat : Nat) : Int) = W := Int.toNat_of_nonneg hW
  have h3 : ((j.toNat : Nat) : Int) = j := Int.toNat_of_nonneg hj
  rw [Int.natCast_add, Int.natCast_mul, h1, h2, h3]

/-- … so the `Int` offset `i * W + j` converted by `toNat` IS `rmN`. -/
theorem rmN_eq_toNat {W i j : Int} (hW : 0 ≤ W) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    (i * W + j).toNat = rmN W i j := by
  have h := rmN_cast hW hi hj
  omega

/-- A whole row `[i*W, i*W + W)`: its start. -/
theorem rmN_row_toNat {W i : Int} (hW : 0 ≤ W) (hi : 0 ≤ i) : (i * W).toNat = rmN W i 0 := by
  have h := rmN_eq_toNat hW hi (Int.le_refl 0)
  simpa using h

/-- A whole row ends inside the vector. -/
theorem rmN_row_le {W i m1 : Int} (hi : i ≤ m1) (hW : 0 ≤ W) (hi0 : 0 ≤ i) :
    rmN W i 0 + W.toNat ≤ (m1 + 1).toNat * W.toNat := by
  unfold rmN
  have h1 : (i.toNat + 1) * W.toNat ≤ (m1 + 1).toNat * W.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at h1
  omega

/-- A part `[lo, hi]` of row `i` ends inside the vector. -/
theorem rmN_part_le {W i m1 lo hi : Int} (hi1 : i ≤ m1) (hW : 0 ≤ W) (hi0 : 0 ≤ i) (hlo : 0 ≤ lo)
    (hlh : lo ≤ hi) (hhi : hi < W) :
    rmN W i lo + (hi - lo + 1).toNat ≤ (m1 + 1).toNat * W.toNat := by
  unfold rmN
  have h1 : (i.toNat + 1) * W.toNat ≤ (m1 + 1).toNat * W.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at h1
  omega

/-- A cell `(i, j)` of an `R`-row array of rows of width `W` ends inside the vector. -/
theorem rmN_cell_le {W i j m1 : Int} (hi : i ≤ m1) (_hW : 0 ≤ W) (hj : j < W) (hj0 : 0 ≤ j)
    (hi0 : 0 ≤ i) : rmN W i j + 1 ≤ (m1 + 1).toNat * W.toNat := by
  unfold rmN
  have h1 : (i.toNat + 1) * W.toNat ≤ (m1 + 1).toNat * W.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at h1
  omega

/-! ## A list lemma -/

/-- `flatMap` respects pointwise equality on the members. -/
theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## Lexicographic keys -/

/-- A rank key: `(row, column, phase)`, compared lexicographically. -/
abbrev Key := Nat × Nat × Nat

/-- The strict lexicographic order on keys. -/
def KLt (a b : Key) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

instance (a b : Key) : Decidable (KLt a b) := by unfold KLt; infer_instance

theorem KLt_irrefl (a : Key) : ¬ KLt a a := by
  unfold KLt; omega

theorem KLt_trans {a b c : Key} (h1 : KLt a b) (h2 : KLt b c) : KLt a c := by
  unfold KLt at *; omega

/-- A monotone count: `p` implies `p'` on `L`. -/
theorem countP_le_of_imp {α : Type} (p p' : α → Bool) :
    ∀ (L : List α), (∀ q ∈ L, p q = true → p' q = true) → L.countP p ≤ L.countP p'
  | [], _ => by simp
  | y :: ys, hy => by
      rw [List.countP_cons, List.countP_cons]
      have h1 := countP_le_of_imp p p' ys (fun q hq hpq => hy q (List.mem_cons_of_mem _ hq) hpq)
      by_cases a : p y = true
      · have b := hy y (List.mem_cons_self ..) a
        simp [a, b] <;> omega
      · by_cases b : p' y = true
        · simp [a, b] <;> omega
        · simp [a, b] <;> omega

/-- If moreover some member of `L` satisfies `p'` but not `p`, the count is strictly smaller. -/
theorem countP_lt_of_imp {α : Type} (p p' : α → Bool) :
    ∀ (L : List α), (∀ q ∈ L, p q = true → p' q = true) →
      (∃ q ∈ L, p q = false ∧ p' q = true) → L.countP p < L.countP p'
  | [], _, ⟨q, hq, _⟩ => absurd hq (by simp)
  | x :: xs, h, ⟨q, hq, hp, hp'⟩ => by
      rw [List.countP_cons, List.countP_cons]
      have hle := countP_le_of_imp p p' xs (fun q hq hpq => h q (List.mem_cons_of_mem _ hq) hpq)
      rcases List.mem_cons.mp hq with rfl | hq'
      · simp [hp, hp'] <;> omega
      · have ih := countP_lt_of_imp p p' xs (fun q hq hpq => h q (List.mem_cons_of_mem _ hq) hpq)
          ⟨q, hq', hp, hp'⟩
        by_cases a : p x = true
        · have b := h x (List.mem_cons_self ..) a
          simp [a, b] <;> omega
        · by_cases b : p' x = true
          · simp [a, b] <;> omega
          · simp [a, b] <;> omega

/-- **The rank a key induces on a finite family**: the number of members with a strictly smaller
key. -/
def countRank {α : Type} (L : List α) (κ : α → Key) (a : α) : Nat :=
  L.countP (fun q => decide (KLt (κ q) (κ a)))

/-- Strict key decrease between two members is strict rank decrease. -/
theorem countRank_lt {α : Type} (L : List α) (κ : α → Key) {a b : α} (hb : b ∈ L)
    (h : KLt (κ b) (κ a)) : countRank L κ b < countRank L κ a := by
  unfold countRank
  apply countP_lt_of_imp
  · intro q _ hq
    simp only [decide_eq_true_eq] at hq ⊢
    exact KLt_trans hq h
  · exact ⟨b, hb, by simpa using KLt_irrefl (κ b), by simpa using h⟩

end CombView
end LeanModels.Sv
