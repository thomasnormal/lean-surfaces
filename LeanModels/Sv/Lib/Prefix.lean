/-!
# `LeanModels.Sv.Lib.Prefix`: parallel-prefix carry arithmetic (no imports)

The algebra a proof of any parallel-prefix adder (Sklansky, Kogge-Stone, Brent-Kung, Han-Carlson, Ladner-Fischer, …)
uses, over (generate, propagate) pairs of `Bool`s:

* `pgOp`: the carry operator `hi ⊙ lo = (g_hi || (p_hi && g_lo), p_hi && p_lo)`, its unit `pgUnit` (the empty block),
  its associativity (`pgOp_assoc`) and its idempotence (`pgOp_idem`, what overlapping blocks need);
* `pgSpan f j n`: the pair of the `n` positions `j, …, j + n - 1` of a position function `f : Nat → Bool × Bool`, and
  its concatenation law `pgSpan_add`;
* `pgBlock f j k`: the pair of the closed block `[j, k]`; adjacent blocks combine (`pgBlock_combine`:
  `[m+1, k] ⊙ [j, m] = [j, k]`), overlapping ones too (`pgBlock_overlap`); it reads only the positions of the block
  (`pgBlock_congr`);
* the same over two bit functions `g p : Nat → Bool` (`pgOf`): the group generate `grpG g p j k` and propagate
  `grpP g p j k` of `[j, k]`, their combination (`grpG_combine`, `grpP_combine`) and their closed forms
  (`grpP_eq_true_iff`: every position of the block propagates; `grpG_eq_true_iff`: some position generates and every
  position above it propagates);
* the adder's positions `addPos a b cin` (position `0` is the carry in, `(cin, false)`; position `k + 1` is bit `k`,
  `(a k && b k, a k ^^ b k)`) and the ripple carry `rippleCarry a b cin k` into bit `k`: the carry into bit `k` is
  the group generate of positions `[0, k]`, that is of the bits `[0, k)` with `cin` at position `0`
  (`rippleCarry_eq_block`, `pgBlock_addPos_zero`), it reads only the operand bits below `k` (`rippleCarry_congr`),
  and it is core's `BitVec.carry` (`rippleCarry_bv`).

Nothing here names a particular prefix network: the aligned blocks of a Sklansky adder, the doubling spans of a
Kogge-Stone adder and so on belong to that design's proof. Plain Lean (Init only), proved by `omega`, case splits
over `Bool` and the lemmas above.
-/

namespace LeanModels.Sv.Lib

/-! ## The carry operator -/

/-- **The carry operator** on (generate, propagate) pairs. `pgOp hi lo` is the pair of the block made of a block `lo`
and, directly above it (more significant), a block `hi`: it generates a carry when `hi` generates one or `hi`
propagates the one `lo` generates, and it propagates when both parts do. -/
def pgOp (hi lo : Bool × Bool) : Bool × Bool := (hi.1 || (hi.2 && lo.1), hi.2 && lo.2)

@[simp] theorem pgOp_fst (hi lo : Bool × Bool) : (pgOp hi lo).1 = (hi.1 || (hi.2 && lo.1)) := rfl

@[simp] theorem pgOp_snd (hi lo : Bool × Bool) : (pgOp hi lo).2 = (hi.2 && lo.2) := rfl

/-- The pair of the empty block: it generates nothing and propagates. -/
def pgUnit : Bool × Bool := (false, true)

/-- The empty block is a left unit. -/
theorem pgOp_unit_left (x : Bool × Bool) : pgOp pgUnit x = x := by
  obtain ⟨g, p⟩ := x
  cases g <;> cases p <;> rfl

/-- The empty block is a right unit. -/
theorem pgOp_unit_right (x : Bool × Bool) : pgOp x pgUnit = x := by
  obtain ⟨g, p⟩ := x
  cases g <;> cases p <;> rfl

/-- **The carry operator is associative**: a block's pair does not depend on how its parts are grouped. -/
theorem pgOp_assoc (x y z : Bool × Bool) : pgOp (pgOp x y) z = pgOp x (pgOp y z) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨e, f⟩ := z
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- **The carry operator is idempotent**: combining a block with itself changes nothing (so overlapping blocks
combine, `pgBlock_overlap`). -/
theorem pgOp_idem (x : Bool × Bool) : pgOp x x = x := by
  obtain ⟨g, p⟩ := x
  cases g <;> cases p <;> rfl

/-! ## Spans: the pair of `n` consecutive positions -/

/-- The pair of the `n` positions `j, j + 1, …, j + n - 1` of the position function `f` (the half-open block
`[j, j + n)`), the top position outermost: `f (j + n - 1) ⊙ (… ⊙ (f j ⊙ pgUnit))`. -/
def pgSpan (f : Nat → Bool × Bool) (j : Nat) : Nat → Bool × Bool
  | 0 => pgUnit
  | n + 1 => pgOp (f (j + n)) (pgSpan f j n)

@[simp] theorem pgSpan_zero (f : Nat → Bool × Bool) (j : Nat) : pgSpan f j 0 = pgUnit := rfl

theorem pgSpan_succ (f : Nat → Bool × Bool) (j n : Nat) :
    pgSpan f j (n + 1) = pgOp (f (j + n)) (pgSpan f j n) := rfl

/-- One position. -/
theorem pgSpan_one (f : Nat → Bool × Bool) (j : Nat) : pgSpan f j 1 = f j := by
  rw [pgSpan_succ, pgSpan_zero, pgOp_unit_right, Nat.add_zero]

/-- **Concatenation**: the `m + n` positions from `j` are the `n` positions from `j + m` above the `m` positions
from `j`. -/
theorem pgSpan_add (f : Nat → Bool × Bool) (j m : Nat) :
    ∀ n, pgSpan f j (m + n) = pgOp (pgSpan f (j + m) n) (pgSpan f j m)
  | 0 => by rw [Nat.add_zero, pgSpan_zero, pgOp_unit_left]
  | n + 1 => by
    rw [← Nat.add_assoc, pgSpan_succ, pgSpan_add f j m n, pgSpan_succ, pgOp_assoc, Nat.add_assoc]

/-- A span reads only its own positions. -/
theorem pgSpan_congr {f f' : Nat → Bool × Bool} {j : Nat} :
    ∀ {n : Nat}, (∀ t, j ≤ t → t < j + n → f t = f' t) → pgSpan f j n = pgSpan f' j n
  | 0, _ => rfl
  | n + 1, h => by
    rw [pgSpan_succ, pgSpan_succ, h (j + n) (Nat.le_add_right j n) (by omega),
      pgSpan_congr (fun t h1 h2 => h t h1 (by omega))]

/-- The propagate of a span: every position propagates. -/
theorem pgSpan_snd_eq_true_iff (f : Nat → Bool × Bool) (j : Nat) :
    ∀ n, (pgSpan f j n).2 = true ↔ ∀ t, j ≤ t → t < j + n → (f t).2 = true
  | 0 => by
    simp only [pgSpan_zero, pgUnit, true_iff]
    intro t h1 h2
    omega
  | n + 1 => by
    rw [pgSpan_succ, pgOp_snd, Bool.and_eq_true, pgSpan_snd_eq_true_iff f j n]
    constructor
    · rintro ⟨htop, hrest⟩ t h1 h2
      by_cases ht : t = j + n
      · subst ht
        exact htop
      · exact hrest t h1 (by omega)
    · intro h
      exact ⟨h (j + n) (by omega) (by omega), fun t h1 h2 => h t h1 (by omega)⟩

/-- The generate of a span: some position `m` generates and every position above `m` propagates. -/
theorem pgSpan_fst_eq_true_iff (f : Nat → Bool × Bool) (j : Nat) :
    ∀ n, (pgSpan f j n).1 = true ↔
      ∃ m, j ≤ m ∧ m < j + n ∧ (f m).1 = true ∧ ∀ t, m < t → t < j + n → (f t).2 = true
  | 0 => by
    simp only [pgSpan_zero, pgUnit, Bool.false_eq_true, false_iff]
    rintro ⟨m, h1, h2, -⟩
    omega
  | n + 1 => by
    rw [pgSpan_succ, pgOp_fst, Bool.or_eq_true, Bool.and_eq_true, pgSpan_fst_eq_true_iff f j n]
    constructor
    · rintro (htop | ⟨hp, m, h1, h2, h3, h4⟩)
      · exact ⟨j + n, by omega, by omega, htop, fun t h1 h2 => by omega⟩
      · refine ⟨m, h1, by omega, h3, fun t ht1 ht2 => ?_⟩
        by_cases ht : t = j + n
        · subst ht
          exact hp
        · exact h4 t ht1 (by omega)
    · rintro ⟨m, h1, h2, h3, h4⟩
      by_cases hm : m = j + n
      · subst hm
        exact Or.inl h3
      · exact Or.inr ⟨h4 (j + n) (by omega) (by omega), m, h1, by omega, h3,
          fun t ht1 ht2 => h4 t ht1 (by omega)⟩

/-! ## Blocks: the pair of the positions `j … k` -/

/-- The pair of the closed block `[j, k]`: the positions `j, …, k` of `f` (the empty block `pgUnit` when `k < j`). -/
def pgBlock (f : Nat → Bool × Bool) (j k : Nat) : Bool × Bool := pgSpan f j (k + 1 - j)

/-- A one-position block. -/
theorem pgBlock_self (f : Nat → Bool × Bool) (j : Nat) : pgBlock f j j = f j := by
  rw [pgBlock, show j + 1 - j = 1 by omega, pgSpan_one]

/-- A block that ends below its start is empty. -/
theorem pgBlock_of_lt (f : Nat → Bool × Bool) {j k : Nat} (h : k < j) : pgBlock f j k = pgUnit := by
  rw [pgBlock, show k + 1 - j = 0 by omega, pgSpan_zero]

/-- Extending a block by one position at the top. -/
theorem pgBlock_succ (f : Nat → Bool × Bool) {j k : Nat} (h : j ≤ k + 1) :
    pgBlock f j (k + 1) = pgOp (f (k + 1)) (pgBlock f j k) := by
  rw [pgBlock, pgBlock, show k + 1 + 1 - j = (k + 1 - j) + 1 by omega, pgSpan_succ,
    show j + (k + 1 - j) = k + 1 by omega]

/-- **Two adjacent blocks combine**: `[m + 1, k] ⊙ [j, m] = [j, k]` for `j ≤ m + 1` and `m ≤ k` (either part may be
empty). -/
theorem pgBlock_combine (f : Nat → Bool × Bool) {j m k : Nat} (hjm : j ≤ m + 1) (hmk : m ≤ k) :
    pgOp (pgBlock f (m + 1) k) (pgBlock f j m) = pgBlock f j k := by
  unfold pgBlock
  have h := pgSpan_add f j (m + 1 - j) (k + 1 - (m + 1))
  rw [show m + 1 - j + (k + 1 - (m + 1)) = k + 1 - j by omega, show j + (m + 1 - j) = m + 1 by omega] at h
  exact h.symm

/-- **Two overlapping blocks combine**: `[i, k] ⊙ [j, m] = [j, k]` for `j ≤ i ≤ m + 1` and `m ≤ k` (the positions
`[i, m]` counted twice change nothing, `pgOp_idem`). -/
theorem pgBlock_overlap (f : Nat → Bool × Bool) {i j m k : Nat} (hji : j ≤ i) (him : i ≤ m + 1) (hmk : m ≤ k) :
    pgOp (pgBlock f i k) (pgBlock f j m) = pgBlock f j k := by
  have hlow : pgBlock f j m = pgOp (pgBlock f i m) (pgSpan f j (i - j)) := by
    have h := pgSpan_add f j (i - j) (m + 1 - i)
    rw [show i - j + (m + 1 - i) = m + 1 - j by omega, show j + (i - j) = i by omega] at h
    exact h
  rw [hlow, ← pgBlock_combine f him hmk, pgOp_assoc, ← pgOp_assoc (pgBlock f i m), pgOp_idem, ← hlow,
    pgBlock_combine f (by omega) hmk]

/-- A block reads only its own positions. -/
theorem pgBlock_congr {f f' : Nat → Bool × Bool} {j k : Nat} (h : ∀ t, j ≤ t → t ≤ k → f t = f' t) :
    pgBlock f j k = pgBlock f' j k :=
  pgSpan_congr fun t h1 h2 => h t h1 (by omega)

/-! ## Group generate and propagate of two bit functions -/

/-- The positions of a generate function `g` and a propagate function `p`. -/
def pgOf (g p : Nat → Bool) : Nat → Bool × Bool := fun k => (g k, p k)

/-- The group generate of the block `[j, k]` of the bit functions `g` (generate) and `p` (propagate). -/
def grpG (g p : Nat → Bool) (j k : Nat) : Bool := (pgBlock (pgOf g p) j k).1

/-- The group propagate of the block `[j, k]` of the bit functions `g` (generate) and `p` (propagate). -/
def grpP (g p : Nat → Bool) (j k : Nat) : Bool := (pgBlock (pgOf g p) j k).2

theorem grpG_self (g p : Nat → Bool) (j : Nat) : grpG g p j j = g j := by
  rw [grpG, pgBlock_self]
  rfl

theorem grpP_self (g p : Nat → Bool) (j : Nat) : grpP g p j j = p j := by
  rw [grpP, pgBlock_self]
  rfl

/-- The group generate of two adjacent blocks, `[m + 1, k]` above `[j, m]`. -/
theorem grpG_combine (g p : Nat → Bool) {j m k : Nat} (hjm : j ≤ m + 1) (hmk : m ≤ k) :
    grpG g p j k = (grpG g p (m + 1) k || (grpP g p (m + 1) k && grpG g p j m)) := by
  rw [grpG, ← pgBlock_combine (pgOf g p) hjm hmk, pgOp_fst]
  rfl

/-- The group propagate of two adjacent blocks, `[m + 1, k]` above `[j, m]`. -/
theorem grpP_combine (g p : Nat → Bool) {j m k : Nat} (hjm : j ≤ m + 1) (hmk : m ≤ k) :
    grpP g p j k = (grpP g p (m + 1) k && grpP g p j m) := by
  rw [grpP, ← pgBlock_combine (pgOf g p) hjm hmk, pgOp_snd]
  rfl

/-- **The group propagate, in closed form**: every position of `[j, k]` propagates. -/
theorem grpP_eq_true_iff (g p : Nat → Bool) (j k : Nat) :
    grpP g p j k = true ↔ ∀ t, j ≤ t → t ≤ k → p t = true := by
  rw [grpP, pgBlock, pgSpan_snd_eq_true_iff]
  constructor
  · intro h t h1 h2
    exact h t h1 (by omega)
  · intro h t h1 h2
    exact h t h1 (by omega)

/-- **The group generate, in closed form**: some position `m` of `[j, k]` generates and every position above `m` in
the block propagates. -/
theorem grpG_eq_true_iff (g p : Nat → Bool) (j k : Nat) :
    grpG g p j k = true ↔ ∃ m, j ≤ m ∧ m ≤ k ∧ g m = true ∧ ∀ t, m < t → t ≤ k → p t = true := by
  rw [grpG, pgBlock, pgSpan_fst_eq_true_iff]
  constructor
  · rintro ⟨m, h1, h2, h3, h4⟩
    exact ⟨m, h1, by omega, h3, fun t ht1 ht2 => h4 t ht1 (by omega)⟩
  · rintro ⟨m, h1, h2, h3, h4⟩
    exact ⟨m, h1, by omega, h3, fun t ht1 ht2 => h4 t ht1 (by omega)⟩

/-! ## The adder: positions, and the carry as a group generate -/

/-- The positions of an adder of the bit functions `a`, `b` with carry in `cin`: position `0` is the carry in
(generate `cin`, propagate `false`), position `k + 1` is bit `k` (generate `a k && b k`, propagate `a k ^^ b k`). -/
def addPos (a b : Nat → Bool) (cin : Bool) : Nat → Bool × Bool
  | 0 => (cin, false)
  | k + 1 => (a k && b k, a k ^^ b k)

/-- The ripple carry into bit `k` of the sum of the bit functions `a`, `b` and the carry in `cin`: `cin` into bit
`0`, and the full adder's carry `(a k && b k) || (c_k && (a k ^^ b k))` into bit `k + 1`. -/
def rippleCarry (a b : Nat → Bool) (cin : Bool) : Nat → Bool
  | 0 => cin
  | k + 1 => (a k && b k) || (rippleCarry a b cin k && (a k ^^ b k))

@[simp] theorem addPos_zero (a b : Nat → Bool) (cin : Bool) : addPos a b cin 0 = (cin, false) := rfl

@[simp] theorem addPos_succ (a b : Nat → Bool) (cin : Bool) (k : Nat) :
    addPos a b cin (k + 1) = (a k && b k, a k ^^ b k) := rfl

@[simp] theorem rippleCarry_zero (a b : Nat → Bool) (cin : Bool) : rippleCarry a b cin 0 = cin := rfl

theorem rippleCarry_succ (a b : Nat → Bool) (cin : Bool) (k : Nat) :
    rippleCarry a b cin (k + 1) = ((a k && b k) || (rippleCarry a b cin k && (a k ^^ b k))) := rfl

/-- The ripple carry into bit `n` reads the operand bits below `n` only. -/
theorem rippleCarry_congr {a b a' b' : Nat → Bool} {cin : Bool} :
    ∀ {n : Nat}, (∀ k, k < n → a k = a' k ∧ b k = b' k) → rippleCarry a b cin n = rippleCarry a' b' cin n
  | 0, _ => rfl
  | n + 1, h => by
    obtain ⟨ha, hb⟩ := h n (by omega)
    rw [rippleCarry_succ, rippleCarry_succ, ha, hb, rippleCarry_congr (fun k hk => h k (by omega))]

/-- **The prefix pairs of an adder**: the block `[0, k]` of the adder's positions (the bits `[0, k)` and the carry in
at position `0`) generates the carry into bit `k`, and it never propagates (position `0` does not). -/
theorem pgBlock_addPos_zero (a b : Nat → Bool) (cin : Bool) :
    ∀ k, pgBlock (addPos a b cin) 0 k = (rippleCarry a b cin k, false)
  | 0 => by rw [pgBlock_self]; rfl
  | k + 1 => by
    rw [pgBlock_succ _ (Nat.zero_le _), pgBlock_addPos_zero a b cin k]
    show pgOp (a k && b k, a k ^^ b k) (rippleCarry a b cin k, false) =
      ((a k && b k) || (rippleCarry a b cin k && (a k ^^ b k)), false)
    generalize a k = u
    generalize b k = v
    generalize rippleCarry a b cin k = c
    cases u <;> cases v <;> cases c <;> rfl

/-- **The carry into bit `k` is the group generate of the block `[0, k]`** of the adder's positions: the bits
`[0, k)`, with `cin` at position `0`. -/
theorem rippleCarry_eq_block (a b : Nat → Bool) (cin : Bool) (k : Nat) :
    rippleCarry a b cin k = (pgBlock (addPos a b cin) 0 k).1 := by
  rw [pgBlock_addPos_zero]

/-- The ripple carry of two `BitVec`s is core's `BitVec.carry`
(`decide (2^k ≤ x % 2^k + y % 2^k + c)`, the carry as a `Nat` comparison). -/
theorem rippleCarry_bv {w : Nat} (x y : BitVec w) (c : Bool) :
    ∀ k, rippleCarry x.getLsbD y.getLsbD c k = BitVec.carry k x y c
  | 0 => BitVec.carry_zero.symm
  | k + 1 => by
    rw [rippleCarry_succ, rippleCarry_bv x y c k, BitVec.carry_succ]
    generalize x.getLsbD k = u
    generalize y.getLsbD k = v
    generalize BitVec.carry k x y c = t
    cases u <;> cases v <;> cases t <;> rfl

end LeanModels.Sv.Lib
