import LeanModels.Sv.Basic

/-!
# Monotonicity of the 4-state operator tables at every width (WS4, R-X, X9 follow-up)

**Status label:** measurement towards R-X (`fourState_abstracts`, ARCH-NOTE §4.3): width-parametric facts about the
operators pinned in `LeanModels/Sv/Basic.lean`. No definition of the semantics is changed or added; this module is
imported by nothing (build it alone: `lake env lean LeanModels/Sv/XMono.lean`).

**The order** (X9's, `x ⊑ z`): on one bit, `a ⊑ b` iff `a = b` or `a = x` (`x` is the unknown, below `0`, `1` and `z`);
on vectors, same width and bitwise (`VLe`). A `Logic`-valued operator is monotone when `f a b ⊑ f a' b'` whenever
`a ⊑ a'` and `b ⊑ b'`.

**What is proved, for every width.** One theorem per operator, grouped by family:
- bitwise `& | ^ ~` and the conditional merge (any width mismatch included: both sides collapse alike);
- the x-collapsing arithmetic `+ - * / % ** ` (signed and unsigned), unary `+ -`;
- the relational operators, signed and unsigned, `==`/`!=`, `&&`/`||`/`!` and the truthiness they use;
- the reductions `|&^` (as folds of monotone scalar tables);
- the shifts `<< >> >>>` with a known or an unknown amount, `?:` (operands of equal width, as elaboration makes them),
  `{,}` and the sign-extending resize.

The non-monotone operators are those of X9 (`===`/`!==`, `==?`/`!=?`, case/casez/casex matching, the `if` decision,
the knownness tests, the 2-state boundary); each keeps its kernel counterexample at one small width (end of file).
-/

namespace LeanModels.Sv.XMono

open LeanModels.Sv

/-! ## The order -/

/-- The information order on one bit: `x` is below every value. -/
def Le (a b : Logic) : Prop := a = b ∨ a = .lx

instance (a b : Logic) : Decidable (Le a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem Le.refl (a : Logic) : Le a a := Or.inl rfl

@[simp] theorem Le.bot (b : Logic) : Le .lx b := Or.inr rfl

/-- A known bit has no proper refinement. -/
theorem Le.eq_of_known {a b : Logic} (h : Le a b) (hk : a.isKnown = true) : b = a := by
  rcases h with rfl | rfl
  · rfl
  · simp [Logic.isKnown] at hk

/-- The order on vectors: same width, bitwise. -/
def VLe (a b : LVec) : Prop :=
  a.bits.size = b.bits.size ∧
    ∀ (i : Nat) (h : i < a.bits.size) (h' : i < b.bits.size), Le a.bits[i] b.bits[i]

theorem VLe.refl (a : LVec) : VLe a a := ⟨rfl, fun _ _ _ => Le.refl _⟩

theorem VLe.width {a b : LVec} (h : VLe a b) : a.width = b.width := h.1

/-- A fully known vector has no proper refinement. -/
theorem VLe.eq_of_allKnown {a b : LVec} (h : VLe a b) (hk : a.allKnown = true) : b = a := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  simp only [LVec.allKnown, Array.all_eq_true] at hk
  obtain ⟨hs, hle⟩ := h
  congr 1
  exact Array.ext hs.symm (fun i h1 h2 => (hle i h2 h1).eq_of_known (hk i h2))

/-- The all-`x` vector is below every vector of its width. -/
theorem xVec_le {w : Nat} {v : LVec} (hw : v.width = w) : VLe (LVec.xVec w) v := by
  refine ⟨by simp [LVec.xVec, LVec.replicate, ← hw, LVec.width], fun i _ _ => ?_⟩
  simp [LVec.xVec, LVec.replicate]

theorem xVec_width (w : Nat) : (LVec.xVec w).width = w := by
  simp [LVec.xVec, LVec.replicate, LVec.width]

theorem ofNat_width (w n : Nat) : (LVec.ofNat w n).width = w := by
  simp [LVec.ofNat, LVec.width]

/-- A refinement keeps a `1` bit. -/
theorem VLe.one {a b : LVec} (h : VLe a b) {i : Nat} (hi : i < a.bits.size) (h1 : a.bits[i] = .l1) :
    b.bits[i]'(h.1 ▸ hi) = .l1 := by
  rw [(h.2 i hi (h.1 ▸ hi)).eq_of_known (by rw [h1]; rfl), h1]

/-- Reading index `j` with a default is monotone (out of range on both sides alike). -/
theorem getD_mono {a a' : LVec} (ha : VLe a a') {d d' : Logic} (hd : Le d d') (j : Nat) :
    Le (a.bits[j]?.getD d) (a'.bits[j]?.getD d') := by
  by_cases hj : j < a.bits.size
  · have hj' : j < a'.bits.size := ha.1 ▸ hj
    rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_getElem hj']
    exact ha.2 j hj hj'
  · have hj' : a'.bits.size ≤ j := by have := ha.1; omega
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none hj']
    exact hd

/-- The most significant bit (the sign-fill bit), with a default, is monotone. -/
theorem back_mono {a a' : LVec} (ha : VLe a a') {d d' : Logic} (hd : Le d d') :
    Le (a.bits.back?.getD d) (a'.bits.back?.getD d') := by
  rw [Array.back?_eq_getElem?, Array.back?_eq_getElem?, ← ha.1]
  exact getD_mono ha hd _

/-! ## Scalar tables (finite case analysis) -/

/-- Monotone binary scalar table. -/
def Mono2 (f : Logic → Logic → Logic) : Prop := ∀ x y x' y', Le x x' → Le y y' → Le (f x y) (f x' y')

theorem and_mono2 : Mono2 Logic.and := by
  intro x y x' y'; cases x <;> cases y <;> cases x' <;> cases y' <;> decide
theorem or_mono2 : Mono2 Logic.or := by
  intro x y x' y'; cases x <;> cases y <;> cases x' <;> cases y' <;> decide
theorem xor_mono2 : Mono2 Logic.xor := by
  intro x y x' y'; cases x <;> cases y <;> cases x' <;> cases y' <;> decide
theorem merge_mono2 : Mono2 Logic.merge := by
  intro x y x' y'; cases x <;> cases y <;> cases x' <;> cases y' <;> decide
theorem not_mono1 : ∀ x x', Le x x' → Le (Logic.not x) (Logic.not x') := by
  intro x x'; cases x <;> cases x' <;> decide
/-- The merge of two arms is below either refined arm. -/
theorem merge_le_left : ∀ x y x', Le x x' → Le (Logic.merge x y) x' := by
  intro x y x'; cases x <;> cases y <;> cases x' <;> decide
theorem merge_le_right : ∀ x y y', Le y y' → Le (Logic.merge x y) y' := by
  intro x y y'; cases x <;> cases y <;> cases y' <;> decide

/-! ## Family 1: bitwise operators -/

theorem zipWith_mono {f : Logic → Logic → Logic} (hf : Mono2 f) {a b a' b' : LVec}
    (ha : VLe a a') (hb : VLe b b') : VLe (LVec.zipWith f a b) (LVec.zipWith f a' b') := by
  unfold LVec.zipWith
  have hwa := ha.width
  have hwb := hb.width
  by_cases h : a.width = b.width
  · have h' : a'.width = b'.width := by omega
    rw [if_pos h, if_pos h']
    refine ⟨by simp [ha.1, hb.1], fun i h1 h2 => ?_⟩
    simp only [Array.getElem_zipWith]
    have hs1 := ha.1
    have hs2 := hb.1
    simp only [Array.size_zipWith, Nat.lt_min] at h1 h2
    exact hf _ _ _ _ (ha.2 i h1.1 h2.1) (hb.2 i h1.2 h2.2)
  · have h' : ¬ a'.width = b'.width := by omega
    rw [if_neg h, if_neg h', ← hwa, ← hwb]
    exact VLe.refl _

theorem and_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.and a b) (LVec.and a' b') :=
  zipWith_mono and_mono2 ha hb
theorem or_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.or a b) (LVec.or a' b') :=
  zipWith_mono or_mono2 ha hb
theorem xor_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.xor a b) (LVec.xor a' b') :=
  zipWith_mono xor_mono2 ha hb
theorem merge_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    VLe (LVec.merge a b) (LVec.merge a' b') :=
  zipWith_mono merge_mono2 ha hb

theorem not_mono {a a' : LVec} (ha : VLe a a') : VLe (LVec.not a) (LVec.not a') := by
  refine ⟨by simp [LVec.not, ha.1], fun i h1 h2 => ?_⟩
  simp only [LVec.not, Array.getElem_map]
  simp only [LVec.not, Array.size_map] at h1 h2
  exact not_mono1 _ _ (ha.2 i h1 h2)

/-! ## Family 2: the x-collapsing arithmetic (§11.4.3)

One lemma does the work: an operator that returns all-`x` whenever an operand has an unknown bit, and whose result
width depends only on the operand widths, is monotone (a known operand has no proper refinement). -/

theorem collapse2 {f : LVec → LVec → LVec} {W : Nat → Nat → Nat}
    (hx : ∀ a b, a.allKnown = false ∨ b.allKnown = false → f a b = LVec.xVec (W a.width b.width))
    (hw : ∀ a b, (f a b).width = W a.width b.width)
    {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (f a b) (f a' b') := by
  by_cases hka : a.allKnown = true
  · by_cases hkb : b.allKnown = true
    · rw [ha.eq_of_allKnown hka, hb.eq_of_allKnown hkb]; exact VLe.refl _
    · rw [hx a b (Or.inr (by simpa using hkb))]
      exact xVec_le (by rw [hw, ← ha.width, ← hb.width])
  · rw [hx a b (Or.inl (by simpa using hka))]
    exact xVec_le (by rw [hw, ← ha.width, ← hb.width])

theorem collapse1 {f : LVec → LVec} {W : Nat → Nat}
    (hx : ∀ a, a.allKnown = false → f a = LVec.xVec (W a.width))
    (hw : ∀ a, (f a).width = W a.width) {a a' : LVec} (ha : VLe a a') : VLe (f a) (f a') := by
  by_cases hka : a.allKnown = true
  · rw [ha.eq_of_allKnown hka]; exact VLe.refl _
  · rw [hx a (by simpa using hka)]
    exact xVec_le (by rw [hw, ← ha.width])

/-- `toNat?` is `none` exactly on a vector with an unknown bit. -/
theorem toNat?_of_unknown {a : LVec} (h : a.allKnown = false) : a.toNat? = none := by
  simp [LVec.toNat?, h]

macro "collapse_x" : tactic =>
  `(tactic| (intro a b h; rcases h with h | h <;>
              simp [LVec.add, LVec.sub, LVec.mul, LVec.div, LVec.sdiv, LVec.rem, LVec.srem, LVec.pow,
                    toNat?_of_unknown h, LVec.arithWidth]))
macro "collapse_w" : tactic =>
  `(tactic| (intro a b
             simp only [LVec.add, LVec.sub, LVec.mul, LVec.div, LVec.sdiv, LVec.rem, LVec.srem, LVec.pow]
             repeat' split
             all_goals simp [xVec_width, ofNat_width, LVec.ofBitVec, LVec.arithWidth]))

theorem add_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.add a b) (LVec.add a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem sub_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.sub a b) (LVec.sub a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem mul_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.mul a b) (LVec.mul a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem div_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.div a b) (LVec.div a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem rem_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.rem a b) (LVec.rem a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem sdiv_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    VLe (LVec.sdiv a b) (LVec.sdiv a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem srem_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    VLe (LVec.srem a b) (LVec.srem a' b') :=
  collapse2 (W := max) (by collapse_x) (by collapse_w) ha hb
theorem pow_mono (sb se : Bool) {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    VLe (LVec.pow sb se a b) (LVec.pow sb se a' b') :=
  collapse2 (W := fun w _ => w) (by collapse_x) (by collapse_w) ha hb

theorem pos_mono {a a' : LVec} (ha : VLe a a') : VLe (LVec.pos a) (LVec.pos a') :=
  collapse1 (W := id) (fun a h => by simp [LVec.pos, h, LVec.width])
    (fun a => by unfold LVec.pos; split <;> simp [xVec_width]) ha
theorem neg_mono {a a' : LVec} (ha : VLe a a') : VLe (LVec.neg a) (LVec.neg a') :=
  collapse1 (W := id) (fun a h => by simp [LVec.neg, toNat?_of_unknown h, LVec.width])
    (fun a => by unfold LVec.neg; split <;> simp [xVec_width, ofNat_width]) ha

/-! ## Family 3: one-bit results — comparisons, equality, logical operators -/

theorem collapseL2 {f : LVec → LVec → Logic}
    (hx : ∀ a b, a.allKnown = false ∨ b.allKnown = false → f a b = .lx)
    {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (f a b) (f a' b') := by
  by_cases hka : a.allKnown = true
  · by_cases hkb : b.allKnown = true
    · rw [ha.eq_of_allKnown hka, hb.eq_of_allKnown hkb]; exact Le.refl _
    · rw [hx a b (Or.inr (by simpa using hkb))]; exact Le.bot _
  · rw [hx a b (Or.inl (by simpa using hka))]; exact Le.bot _

theorem relOp_mono (cmp : Nat → Nat → Bool) {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    Le (LVec.relOp cmp a b) (LVec.relOp cmp a' b') :=
  collapseL2 (fun a b h => by rcases h with h | h <;> simp [LVec.relOp, toNat?_of_unknown h]) ha hb

theorem signedRelOp_mono (cmp : Int → Int → Bool) {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    Le (LVec.signedRelOp cmp a b) (LVec.signedRelOp cmp a' b') :=
  collapseL2 (fun a b h => by rcases h with h | h <;> simp [LVec.signedRelOp, toNat?_of_unknown h]) ha hb

theorem lt_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.lt a b) (LVec.lt a' b') :=
  relOp_mono _ ha hb
theorem le_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.le a b) (LVec.le a' b') :=
  relOp_mono _ ha hb
theorem gt_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.gt a b) (LVec.gt a' b') :=
  relOp_mono _ ha hb
theorem ge_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.ge a b) (LVec.ge a' b') :=
  relOp_mono _ ha hb
theorem slt_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.slt a b) (LVec.slt a' b') :=
  signedRelOp_mono _ ha hb
theorem sle_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.sle a b) (LVec.sle a' b') :=
  signedRelOp_mono _ ha hb
theorem sgt_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.sgt a b) (LVec.sgt a' b') :=
  signedRelOp_mono _ ha hb
theorem sge_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.sge a b) (LVec.sge a' b') :=
  signedRelOp_mono _ ha hb

/-- Logical equality `==`: a definite mismatch survives refinement, full knownness has no proper refinement, and
everything else is `x`. -/
theorem eqLogical_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    Le (LVec.eqLogical a b) (LVec.eqLogical a' b') := by
  have hwa := ha.1
  have hwb := hb.1
  unfold LVec.eqLogical LVec.width
  by_cases hw : a.bits.size = b.bits.size
  · have hw' : a'.bits.size = b'.bits.size := by omega
    simp only [hw, hw', ne_eq, not_true_eq_false, if_false]
    by_cases hm : (Array.zip a.bits b.bits).any
        (fun p => p.1.isKnown && p.2.isKnown && p.1 != p.2) = true
    · have hm' : (Array.zip a'.bits b'.bits).any
          (fun p => p.1.isKnown && p.2.isKnown && p.1 != p.2) = true := by
        rw [Array.any_eq_true] at hm ⊢
        obtain ⟨i, hi, hp⟩ := hm
        simp only [Array.size_zip, Nat.lt_min] at hi
        simp only [Array.getElem_zip, Bool.and_eq_true] at hp
        obtain ⟨⟨hka, hkb⟩, hne⟩ := hp
        have e1 := (ha.2 i hi.1 (by omega)).eq_of_known hka
        have e2 := (hb.2 i hi.2 (by omega)).eq_of_known hkb
        refine ⟨i, by simp only [Array.size_zip, Nat.lt_min]; omega, ?_⟩
        simp only [Array.getElem_zip, Bool.and_eq_true, e1, e2]
        exact ⟨⟨hka, hkb⟩, hne⟩
      simp only [hm, hm', if_true]
      exact Le.refl _
    · by_cases hk : (a.allKnown && b.allKnown) = true
      · simp only [Bool.and_eq_true] at hk
        rw [ha.eq_of_allKnown hk.1, hb.eq_of_allKnown hk.2]
        exact Le.refl _
      · simp only [Bool.not_eq_true] at hm
        simp only [hm, Bool.false_eq_true, if_false]
        rw [if_neg hk]
        exact Le.bot _
  · have hw' : ¬ a'.bits.size = b'.bits.size := by omega
    simp only [hw, hw', ne_eq, not_false_eq_true, if_true]
    exact Le.refl _

theorem neLogical_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    Le (LVec.neLogical a b) (LVec.neLogical a' b') :=
  not_mono1 _ _ (eqLogical_mono ha hb)

/-- `if`-truthiness facts used by `!`, `&&`, `||` and `?:`: a `1` bit survives refinement; an all-`0` vector has no
proper refinement. -/
theorem beq_l1 : ∀ x : Logic, (x == .l1) = true ↔ x = .l1 := by intro x; cases x <;> decide
theorem beq_l0 : ∀ x : Logic, (x == .l0) = true ↔ x = .l0 := by intro x; cases x <;> decide

theorem condTrue_mono {a a' : LVec} (ha : VLe a a') (h : a.condTrue = true) : a'.condTrue = true := by
  simp only [LVec.condTrue, Array.any_eq_true, beq_l1] at h ⊢
  obtain ⟨i, hi, h1⟩ := h
  exact ⟨i, ha.1 ▸ hi, ha.one hi h1⟩

theorem allKnown_of_isKnownZero {a : LVec} (h : a.isKnownZero = true) : a.allKnown = true := by
  simp only [LVec.isKnownZero, LVec.allKnown, Array.all_eq_true, beq_l0] at h ⊢
  intro i hi
  rw [h i hi]; rfl

theorem hasKnownOne_iff : ∀ l : List Logic, LVec.hasKnownOne l = true ↔ Logic.l1 ∈ l
  | [] => by simp [LVec.hasKnownOne]
  | x :: xs => by cases x <;> simp [LVec.hasKnownOne, hasKnownOne_iff xs]

theorem allKnownZero_iff : ∀ l : List Logic, LVec.allKnownZero l = true ↔ ∀ x ∈ l, x = Logic.l0
  | [] => by simp [LVec.allKnownZero]
  | x :: xs => by cases x <;> simp [LVec.allKnownZero, allKnownZero_iff xs]

theorem truthy_mono {a a' : LVec} (ha : VLe a a') : Le (LVec.truthy a) (LVec.truthy a') := by
  unfold LVec.truthy
  by_cases h1 : LVec.hasKnownOne a.bits.toList = true
  · have h1' : LVec.hasKnownOne a'.bits.toList = true := by
      rw [hasKnownOne_iff, List.mem_iff_getElem] at h1 ⊢
      obtain ⟨i, hi, e⟩ := h1
      simp only [Array.length_toList, Array.getElem_toList] at hi e
      exact ⟨i, by simpa [← ha.1] using hi, by simpa using ha.one hi e⟩
    simp [h1, h1', Le.refl]
  · by_cases h0 : LVec.allKnownZero a.bits.toList = true
    · have hk : a.allKnown = true := by
        rw [allKnownZero_iff] at h0
        simp only [LVec.allKnown, Array.all_eq_true]
        intro i hi
        have hm : a.bits[i] ∈ a.bits.toList := by simp
        rw [h0 _ hm]; rfl
      rw [ha.eq_of_allKnown hk]; exact Le.refl _
    · simp only [h1, h0, Bool.false_eq_true, if_false]
      exact Le.bot _

theorem land_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.land a b) (LVec.land a' b') :=
  and_mono2 _ _ _ _ (truthy_mono ha) (truthy_mono hb)
theorem lor_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : Le (LVec.lor a b) (LVec.lor a' b') :=
  or_mono2 _ _ _ _ (truthy_mono ha) (truthy_mono hb)

theorem lnot_mono {a a' : LVec} (ha : VLe a a') : Le (LVec.lnot a) (LVec.lnot a') := by
  unfold LVec.lnot
  by_cases h1 : a.condTrue = true
  · simp [h1, condTrue_mono ha h1, Le.refl]
  · by_cases h0 : a.isKnownZero = true
    · rw [ha.eq_of_allKnown (allKnown_of_isKnownZero h0)]; exact Le.refl _
    · simp only [h1, h0, Bool.false_eq_true, if_false]; exact Le.bot _

/-! ## Family 4: reductions (folds of monotone scalar tables) -/

/-- Bitwise order on lists. -/
def LLe : List Logic → List Logic → Prop
  | [], [] => True
  | x :: xs, y :: ys => Le x y ∧ LLe xs ys
  | _, _ => False

theorem lle_of_index : ∀ (l l' : List Logic), l.length = l'.length →
    (∀ (i : Nat) (h : i < l.length) (h' : i < l'.length), Le l[i] l'[i]) → LLe l l'
  | [], [], _, _ => trivial
  | x :: xs, y :: ys, hl, h =>
      ⟨h 0 (by simp) (by simp),
       lle_of_index xs ys (by simpa using hl)
         (fun i hi hi' => h (i + 1) (by simp; omega) (by simp; omega))⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem VLe.toList {a b : LVec} (h : VLe a b) : LLe a.bits.toList b.bits.toList :=
  lle_of_index _ _ (by simpa using h.1)
    (fun i hi hi' => by simpa using h.2 i (by simpa using hi) (by simpa using hi'))

theorem foldl_mono {f : Logic → Logic → Logic} (hf : Mono2 f) :
    ∀ (l l' : List Logic) (i i' : Logic), LLe l l' → Le i i' → Le (l.foldl f i) (l'.foldl f i')
  | [], [], _, _, _, hi => hi
  | _ :: xs, _ :: ys, _, _, h, hi => foldl_mono hf xs ys _ _ h.2 (hf _ _ _ _ hi h.1)
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem redOr_mono {a a' : LVec} (ha : VLe a a') : Le (LVec.redOr a) (LVec.redOr a') := by
  unfold LVec.redOr
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_mono or_mono2 _ _ _ _ ha.toList (Le.refl _)
theorem redAnd_mono {a a' : LVec} (ha : VLe a a') : Le (LVec.redAnd a) (LVec.redAnd a') := by
  unfold LVec.redAnd
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_mono and_mono2 _ _ _ _ ha.toList (Le.refl _)
theorem redXor_mono {a a' : LVec} (ha : VLe a a') : Le (LVec.redXor a) (LVec.redXor a') := by
  unfold LVec.redXor
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_mono xor_mono2 _ _ _ _ ha.toList (Le.refl _)

theorem evalRedOp_mono (op : RedOp) {a a' : LVec} (ha : VLe a a') : Le (evalRedOp op a) (evalRedOp op a') := by
  cases op
  · exact redOr_mono ha
  · exact redAnd_mono ha
  · exact redXor_mono ha
  · exact not_mono1 _ _ (redOr_mono ha)
  · exact not_mono1 _ _ (redAnd_mono ha)
  · exact not_mono1 _ _ (redXor_mono ha)

/-! ## Family 5: shifts (known and unknown amounts), `?:`, concatenation, resize -/

theorem shl_width (a b : LVec) : (LVec.shl a b).width = a.width := by
  unfold LVec.shl; split <;> simp [LVec.xVec, LVec.replicate, LVec.width]
theorem shr_width (a b : LVec) : (LVec.shr a b).width = a.width := by
  unfold LVec.shr; split <;> simp [LVec.xVec, LVec.replicate, LVec.width]
theorem ashr_width (s : Bool) (a b : LVec) : (LVec.ashr s a b).width = a.width := by
  unfold LVec.ashr; split <;> simp [LVec.xVec, LVec.replicate, LVec.width]

/-- An unknown amount gives all-`x` (below anything of the operand's width); a known amount has no proper refinement
and moves bits, which `getD_mono` follows index by index. -/
theorem shl_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.shl a b) (LVec.shl a' b') := by
  by_cases hk : b.allKnown = true
  · rw [hb.eq_of_allKnown hk]
    unfold LVec.shl
    split
    · exact xVec_le (by rw [xVec_width, ha.width])
    · refine ⟨by simpa using ha.width, fun i h1 h2 => ?_⟩
      simp only [Array.getElem_ofFn]
      split
      · exact Le.refl _
      · exact getD_mono ha (Le.refl _) _
  · have e : LVec.shl a b = LVec.xVec a.width := by
      simp [LVec.shl, LVec.shiftAmount?, toNat?_of_unknown (by simpa using hk)]
    rw [e]; exact xVec_le (by rw [shl_width, ha.width])

theorem shr_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') : VLe (LVec.shr a b) (LVec.shr a' b') := by
  by_cases hk : b.allKnown = true
  · rw [hb.eq_of_allKnown hk]
    unfold LVec.shr
    split
    · exact xVec_le (by rw [xVec_width, ha.width])
    · refine ⟨by simpa using ha.width, fun i h1 h2 => ?_⟩
      simp only [Array.getElem_ofFn]
      exact getD_mono ha (Le.refl _) _
  · have e : LVec.shr a b = LVec.xVec a.width := by
      simp [LVec.shr, LVec.shiftAmount?, toNat?_of_unknown (by simpa using hk)]
    rw [e]; exact xVec_le (by rw [shr_width, ha.width])

theorem ashr_mono (s : Bool) {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    VLe (LVec.ashr s a b) (LVec.ashr s a' b') := by
  by_cases hk : b.allKnown = true
  · rw [hb.eq_of_allKnown hk]
    unfold LVec.ashr
    split
    · exact xVec_le (by rw [xVec_width, ha.width])
    · refine ⟨by simpa using ha.width, fun i h1 h2 => ?_⟩
      simp only [Array.getElem_ofFn]
      refine getD_mono ha ?_ _
      cases s
      · exact Le.refl _
      · exact back_mono ha (Le.refl _)
  · have e : LVec.ashr s a b = LVec.xVec a.width := by
      simp [LVec.ashr, LVec.shiftAmount?, toNat?_of_unknown (by simpa using hk)]
    rw [e]; exact xVec_le (by rw [ashr_width, ha.width])

theorem ashl_mono {a b a' b' : LVec} (ha : VLe a a') (hb : VLe b b') :
    VLe (LVec.ashl a b) (LVec.ashl a' b') :=
  shl_mono ha hb

/-- The merge of two equal-width arms is below either refined arm. -/
theorem merge_le_leftV {a b a' : LVec} (hab : a.width = b.width) (ha : VLe a a') : VLe (LVec.merge a b) a' := by
  unfold LVec.merge LVec.zipWith
  rw [if_pos hab]
  simp only [LVec.width] at hab
  refine ⟨by simp [hab, ← ha.1], fun i h1 h2 => ?_⟩
  simp only [Array.getElem_zipWith]
  simp only [Array.size_zipWith, Nat.lt_min] at h1
  exact merge_le_left _ _ _ (ha.2 i h1.1 h2)

theorem merge_le_rightV {a b b' : LVec} (hab : a.width = b.width) (hb : VLe b b') : VLe (LVec.merge a b) b' := by
  unfold LVec.merge LVec.zipWith
  rw [if_pos hab]
  simp only [LVec.width] at hab
  refine ⟨by simp [hab, ← hb.1], fun i h1 h2 => ?_⟩
  simp only [Array.getElem_zipWith]
  simp only [Array.size_zipWith, Nat.lt_min] at h1
  exact merge_le_right _ _ _ (hb.2 i h1.2 h2)

/-- `c ? a : b` with arms of equal width (elaboration makes them so, §11.4.11): monotone in all three operands. -/
theorem ternary_mono {c a b c' a' b' : LVec} (hab : a.width = b.width) (hc : VLe c c') (ha : VLe a a')
    (hb : VLe b b') : VLe (LVec.ternary c a b) (LVec.ternary c' a' b') := by
  have hab' : a'.width = b'.width := by rw [← ha.width, ← hb.width]; exact hab
  unfold LVec.ternary
  by_cases h1 : c.condTrue = true
  · simp only [h1, condTrue_mono hc h1, if_true]; exact ha
  · by_cases h0 : c.isKnownZero = true
    · rw [hc.eq_of_allKnown (allKnown_of_isKnownZero h0)]
      simp only [h1, h0, Bool.false_eq_true, if_false, if_true]; exact hb
    · simp only [h1, h0, Bool.false_eq_true, if_false]
      split
      · exact merge_le_leftV hab ha
      · split
        · exact merge_le_rightV hab hb
        · exact merge_mono ha hb

/-- `{msb, lsb}`. -/
theorem concat_mono {m l m' l' : LVec} (hm : VLe m m') (hl : VLe l l') :
    VLe (LVec.concat m l) (LVec.concat m' l') := by
  have hs1 := hm.1
  have hs2 := hl.1
  refine ⟨by simp [LVec.concat, hs1, hs2], fun i h1 h2 => ?_⟩
  simp only [LVec.concat, Array.size_append] at h1 h2 ⊢
  by_cases hi : i < l.bits.size
  · rw [Array.getElem_append_left hi, Array.getElem_append_left (by omega)]
    exact hl.2 i hi (by omega)
  · rw [Array.getElem_append_right (by omega), Array.getElem_append_right (by omega)]
    have e : i - l'.bits.size = i - l.bits.size := by rw [hs2]
    simp only [e]
    exact hm.2 _ (by omega) (by omega)

/-- The sign-extending resize to any width (truncation and extension alike). -/
theorem resizeSigned_mono (w : Nat) {a a' : LVec} (ha : VLe a a') :
    VLe (LVec.resizeSigned a w) (LVec.resizeSigned a' w) := by
  refine ⟨by simp [LVec.resizeSigned], fun i h1 h2 => ?_⟩
  simp only [LVec.resizeSigned, Array.getElem_ofFn]
  exact getD_mono ha (back_mono ha (Le.refl _)) _

/-! ## The non-monotone operators (X9's list), each refuted by a kernel-checked counterexample at width 1

Each statement is the NEGATION of monotonicity; the witness is the X9 counterexample. -/

/-- A width-1 vector. -/
abbrev v1 (b : Logic) : LVec := ⟨#[b]⟩

theorem v1_le {x y : Logic} (h : Le x y) : VLe (v1 x) (v1 y) :=
  ⟨rfl, fun i hi _ => by
    have : i = 0 := by simp at hi; omega
    subst this; exact h⟩

/-- `===`: `x === x` is `1`, its refinement `0 === x` is `0`. -/
theorem eqCase_not_mono :
    ¬ ∀ a b a' b', VLe a a' → VLe b b' → Le (LVec.eqCase a b) (LVec.eqCase a' b') := fun h =>
  absurd (h (v1 .lx) (v1 .lx) (v1 .l0) (v1 .lx) (v1_le (Le.bot _)) (v1_le (Le.refl _))) (by decide +kernel)

theorem neCase_not_mono :
    ¬ ∀ a b a' b', VLe a a' → VLe b b' → Le (LVec.neCase a b) (LVec.neCase a' b') := fun h =>
  absurd (h (v1 .lx) (v1 .lx) (v1 .l0) (v1 .lx) (v1_le (Le.bot _)) (v1_le (Le.refl _))) (by decide +kernel)

/-- `==?`: an `x` in the right operand is a wildcard; `1 ==? x` is `1`, `1 ==? 0` is `0`. -/
theorem eqWildcard_not_mono :
    ¬ ∀ a b a' b', VLe a a' → VLe b b' → Le (LVec.eqWildcard a b) (LVec.eqWildcard a' b') := fun h =>
  absurd (h (v1 .l1) (v1 .lx) (v1 .l1) (v1 .l0) (v1_le (Le.refl _)) (v1_le (Le.bot _))) (by decide +kernel)

theorem neWildcard_not_mono :
    ¬ ∀ a b a' b', VLe a a' → VLe b b' → Le (LVec.neWildcard a b) (LVec.neWildcard a' b') := fun h =>
  absurd (h (v1 .l1) (v1 .lx) (v1 .l1) (v1 .l0) (v1_le (Le.refl _)) (v1_le (Le.bot _))) (by decide +kernel)

/-- The `if` decision: `if (x)` takes the else branch, its refinement `if (1)` the then branch. -/
theorem condTrue_not_mono : ¬ ∀ a a', VLe a a' → a.condTrue = a'.condTrue := fun h =>
  absurd (h (v1 .lx) (v1 .l1) (v1_le (Le.bot _))) (by decide +kernel)

/-- `casez` and `casex` item matching. -/
theorem casez_not_mono :
    ¬ ∀ a b a' b', VLe a a' → VLe b b' → LVec.matchesCase false a b = LVec.matchesCase false a' b' := fun h =>
  absurd (h (v1 .lx) (v1 .lx) (v1 .l0) (v1 .lx) (v1_le (Le.bot _)) (v1_le (Le.refl _))) (by decide +kernel)

theorem casex_not_mono :
    ¬ ∀ a b a' b', VLe a a' → VLe b b' → LVec.matchesCase true a b = LVec.matchesCase true a' b' := fun h =>
  absurd (h (v1 .lx) (v1 .l1) (v1 .l0) (v1 .l1) (v1_le (Le.bot _)) (v1_le (Le.refl _))) (by decide +kernel)

/-- The knownness tests (the `$isunknown` family). -/
theorem isKnownZero_not_mono : ¬ ∀ a a', VLe a a' → a.isKnownZero = a'.isKnownZero := fun h =>
  absurd (h (v1 .lx) (v1 .l0) (v1_le (Le.bot _))) (by decide +kernel)

theorem allKnown_not_mono : ¬ ∀ a a', VLe a a' → a.allKnown = a'.allKnown := fun h =>
  absurd (h (v1 .lx) (v1 .l0) (v1_le (Le.bot _))) (by decide +kernel)

/-- The 2-state storage boundary: `x ↦ 0`, but its refinement `1 ↦ 1`. -/
theorem toTwoState_not_mono : ¬ ∀ a a', VLe a a' → VLe (LVec.toTwoState a) (LVec.toTwoState a') := fun h =>
  absurd ((h (v1 .lx) (v1 .l1) (v1_le (Le.bot _))).2 0 (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-! ## Axioms: every theorem above (only `propext`, `Classical.choice`, `Quot.sound` may appear) -/

#print axioms Le.refl
#print axioms Le.eq_of_known
#print axioms VLe.refl
#print axioms VLe.width
#print axioms VLe.eq_of_allKnown
#print axioms xVec_le
#print axioms xVec_width
#print axioms ofNat_width
#print axioms VLe.one
#print axioms getD_mono
#print axioms back_mono
#print axioms and_mono2
#print axioms or_mono2
#print axioms xor_mono2
#print axioms merge_mono2
#print axioms not_mono1
#print axioms merge_le_left
#print axioms merge_le_right
#print axioms zipWith_mono
#print axioms and_mono
#print axioms or_mono
#print axioms xor_mono
#print axioms merge_mono
#print axioms not_mono
#print axioms collapse2
#print axioms collapse1
#print axioms toNat?_of_unknown
#print axioms add_mono
#print axioms sub_mono
#print axioms mul_mono
#print axioms div_mono
#print axioms rem_mono
#print axioms sdiv_mono
#print axioms srem_mono
#print axioms pow_mono
#print axioms pos_mono
#print axioms neg_mono
#print axioms collapseL2
#print axioms relOp_mono
#print axioms signedRelOp_mono
#print axioms lt_mono
#print axioms le_mono
#print axioms gt_mono
#print axioms ge_mono
#print axioms slt_mono
#print axioms sle_mono
#print axioms sgt_mono
#print axioms sge_mono
#print axioms eqLogical_mono
#print axioms neLogical_mono
#print axioms beq_l1
#print axioms beq_l0
#print axioms condTrue_mono
#print axioms allKnown_of_isKnownZero
#print axioms hasKnownOne_iff
#print axioms allKnownZero_iff
#print axioms truthy_mono
#print axioms land_mono
#print axioms lor_mono
#print axioms lnot_mono
#print axioms lle_of_index
#print axioms VLe.toList
#print axioms foldl_mono
#print axioms redOr_mono
#print axioms redAnd_mono
#print axioms redXor_mono
#print axioms evalRedOp_mono
#print axioms shl_width
#print axioms shr_width
#print axioms ashr_width
#print axioms shl_mono
#print axioms shr_mono
#print axioms ashr_mono
#print axioms ashl_mono
#print axioms merge_le_leftV
#print axioms merge_le_rightV
#print axioms ternary_mono
#print axioms concat_mono
#print axioms resizeSigned_mono
#print axioms v1_le
#print axioms eqCase_not_mono
#print axioms neCase_not_mono
#print axioms eqWildcard_not_mono
#print axioms neWildcard_not_mono
#print axioms condTrue_not_mono
#print axioms casez_not_mono
#print axioms casex_not_mono
#print axioms isKnownZero_not_mono
#print axioms allKnown_not_mono
#print axioms toTwoState_not_mono

end LeanModels.Sv.XMono
