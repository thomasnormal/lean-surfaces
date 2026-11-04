import LeanModels.Sv.CombWord
import LeanModels.Sv.Lib.NatArith

/-!
# `LeanModels.Sv.Lib.XFVal`: the `Nat` value of the word-level bit helpers

`sv_equations` states a netlist over bit functions (`st.boolAt "x" : Nat → Bool`) and the word-level helpers of
`CombKnownBits.lean` / `CombWord.lean`. These are the VALUE lemmas of the helpers, all in `Nat`, so a proof can
carry a netlist into a `Nat` model of the datapath without a `BitVec` cast:

* `XF.val` of a `testBit` function (`val_of_testBit`), of a window (`val_window`, `val_window_of_testBit`), of a
  prefix (`val_prefix`), of a concatenation (`val_cat`, `val_cons_false`), of a zero extension (`XF.val_zext`, in
  `CombWord.lean`, and `val_zext_trunc`), of a constant (`val_constBit`, `val_constBit_one`, `val_constBit_zero`), of
  a multiplexer (`val_ite`), of `addBits`/`subBits` (`val_addBits`, `val_subBits`), of the shifts
  (`val_shlBits_zext`, `val_shrBits`, `val_shlBits_one`), of a complement (`val_not`), of constant functions
  (`val_false`, `val_all_true`, `val_all_false`);
* the bits of the constant `0` (`constBit_zero`);
* the Boolean reductions as tests on values (`any_eq_decide_val`, `all_eq_decide_val`, `eqv_eq_decide_val`,
  `val_ne_zero_iff`);
* a bit of a value (`bit_eq_of_val`) and the top bit (`top_bit_iff`, `top_bit_succ_iff`);
* the recursion of `XF.val` from either end (`val_succ`, `val_succ_low`, `val_one`) and its splits (`val_split`,
  `val_four`).

In namespace `LeanModels.Sv.XF`, next to the helpers. None is `@[simp]`: a proof rewrites the equations
`sv_equations` prints by name, and these lemmas do not form a terminating normal form together.
-/

namespace LeanModels.Sv.XF

/-- The value of `n` bits is nonzero exactly when one of the bits is set. -/
theorem val_ne_zero_iff (f : Nat → Bool) : ∀ n, XF.val f n ≠ 0 ↔ ∃ j, j < n ∧ f j = true
  | 0 => by simp [XF.val]
  | n + 1 => by
    have ih := val_ne_zero_iff f n
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    simp only [XF.val]
    cases hb : f n
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
      rw [ih]
      constructor
      · rintro ⟨j, hj, hf⟩
        exact ⟨j, by omega, hf⟩
      · rintro ⟨j, hj, hf⟩
        have hne : j ≠ n := by
          intro e
          subst e
          rw [hb] at hf
          exact absurd hf (by simp)
        exact ⟨j, by omega, hf⟩
    · simp only [Bool.toNat_true, Nat.mul_one]
      constructor
      · intro _
        exact ⟨n, by omega, hb⟩
      · intro _
        omega

/-- **The value of bits that are a number's bits**: if `f` agrees with `x.testBit` below `w`, `XF.val f w` is
`x mod 2^w`. -/
theorem val_of_testBit {f : Nat → Bool} {w x : Nat} (h : ∀ k, k < w → f k = x.testBit k) :
    XF.val f w = x % 2 ^ w := (XF.val_congr_lt h).trans (XF.val_testBit x w)

/-- The value of the window `f[s +: m]` of an `n`-bit value (`s + m ≤ n`): bits `[s, s + m)` of `XF.val f n`. -/
theorem val_window (f : Nat → Bool) (s m n : Nat) (h : s + m ≤ n) :
    XF.val (fun x => f (s + x)) m = XF.val f n / 2 ^ s % 2 ^ m := by
  apply val_of_testBit
  intro k hk
  rw [Nat.testBit_div_two_pow, XF.testBit_val f n (k + s) (by omega), Nat.add_comm k s]

/-- **The value of a concatenation**: `m` bits of `f` below `n` bits of `g` (the `{g, f}` of SV) have the value
`val f m + 2^m · val g n`. -/
theorem val_cat (f g : Nat → Bool) (m : Nat) :
    ∀ n, XF.val (fun k => if k < m then f k else g (k - m)) (m + n) = XF.val f m + 2 ^ m * XF.val g n
  | 0 => by
    simp only [Nat.add_zero, XF.val, Nat.mul_zero]
    exact XF.val_congr_lt (fun j hj => by simp [hj])
  | n + 1 => by
    have ih := val_cat f g m n
    show XF.val _ (m + n + 1) = _
    simp only [XF.val]
    rw [ih]
    have e : ¬ (m + n < m) := by omega
    simp only [if_neg e, Nat.add_sub_cancel_left, Nat.pow_add]
    rw [Nat.mul_add, Nat.mul_assoc]
    omega

/-- `XF.any n f` (the reduction `|f`) is the test `XF.val f n ≠ 0`. -/
theorem any_eq_decide_val (n : Nat) (f : Nat → Bool) : XF.any n f = decide (XF.val f n ≠ 0) := by
  rw [Bool.eq_iff_iff, XF.any_eq_true, decide_eq_true_iff]
  exact (val_ne_zero_iff f n).symm

/-- `XF.all n f` (the reduction `&f`) is the test `XF.val f n = 2^n - 1`. -/
theorem all_eq_decide_val (n : Nat) (f : Nat → Bool) : XF.all n f = decide (XF.val f n = 2 ^ n - 1) := by
  rw [Bool.eq_iff_iff, XF.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h
    have hb : XF.val f n = (2 ^ n - 1) % 2 ^ n :=
      val_of_testBit (fun k hk => by rw [h k hk, Nat.testBit_two_pow_sub_one]; simp [hk])
    rw [hb]
    exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos n; omega)
  · intro h k hk
    rw [XF.testBit_val f n k hk |>.symm, h, Nat.testBit_two_pow_sub_one]
    simp [hk]

/-- **A bit of a known value**: if the `w` bits of `f` have the value `x`, bit `j < w` is bit `j` of `x`. -/
theorem bit_eq_of_val (f : Nat → Bool) (w x j : Nat) (h : XF.val f w = x) (hj : j < w) :
    f j = decide (x / 2 ^ j % 2 = 1) := by
  rw [← XF.testBit_val f w j hj, h, Nat.testBit_eq_decide_div_mod_eq]

/-- The low `m ≤ n` bits of a zero extension from `n` bits are the low `m` bits of the operand (the extension
truncated back; the widening direction is `XF.val_zext`). -/
theorem val_zext_trunc (n m : Nat) (f : Nat → Bool) (h : m ≤ n) : XF.val (XF.zext n f) m = XF.val f m :=
  XF.val_congr_lt (fun k hk => by simp [XF.zext]; omega)

/-- **The value of a constant**: the low `w` bits of the `W`-bit constant `c` (`w ≤ W`, `0 ≤ c < 2^w`) have the
value `c`. -/
theorem val_constBit (c : Int) (W w : Nat) (hc0 : 0 ≤ c) (hc : c < 2 ^ w) (hw : w ≤ W) :
    XF.val (fun k => XF.constBit c W k) w = c.toNat := by
  have hW : (2 : Int) ^ w ≤ (2 : Int) ^ W := by exact_mod_cast Nat.pow_le_pow_right (by omega) hw
  have e : c.emod ((2 : Int) ^ W) = c := Int.emod_eq_of_lt hc0 (Int.lt_of_lt_of_le hc hW)
  have hlt : c.toNat < 2 ^ w := by
    have h3 : (c.toNat : Int) = c := Int.toNat_of_nonneg hc0
    have h4 : (c.toNat : Int) < (2 : Int) ^ w := by rw [h3]; exact hc
    exact_mod_cast h4
  unfold XF.constBit
  rw [XF.val_testBit, e]
  exact Nat.mod_eq_of_lt hlt

/-- The low `w ≥ 1` bits of the `W`-bit constant `1` (`w ≤ W`) have the value `1` (`val_constBit` at `c = 1`). -/
theorem val_constBit_one (W w : Nat) (h1 : 1 ≤ w) (h2 : w ≤ W) : XF.val (fun k => XF.constBit 1 W k) w = 1 :=
  val_constBit 1 W w (by omega) (by exact_mod_cast Nat.one_lt_two_pow (by omega)) h2

/-- The value of a multiplexer `c ? f : g` is the value of the selected operand. -/
theorem val_ite (c : Bool) (f g : Nat → Bool) (w : Nat) :
    XF.val (fun k => if c = true then f k else g k) w = if c = true then XF.val f w else XF.val g w := by
  cases c <;> simp

/-- The value of `w` bits of a sum (`XF.addBits`): the operands' values added, modulo `2^w`. -/
theorem val_addBits (wa wb w : Nat) (fa fb : Nat → Bool) :
    XF.val (fun k => XF.addBits wa fa wb fb k) w = (XF.val fa wa + XF.val fb wb) % 2 ^ w :=
  XF.val_testBit _ w

/-- The value of `w` bits of a difference (`XF.subBits`): `a + (2^max wa wb - b)`, modulo `2^w`. -/
theorem val_subBits (wa wb w : Nat) (fa fb : Nat → Bool) :
    XF.val (fun k => XF.subBits wa fa wb fb k) w = (XF.val fa wa + (2 ^ max wa wb - XF.val fb wb)) % 2 ^ w :=
  XF.val_testBit _ w

/-- **A left shift by a vector**: `w` bits of `zext w f << g` (`g` of `wr` bits) have the value
`val f w · 2^(val g wr)`, modulo `2^w`. -/
theorem val_shlBits_zext (w wr : Nat) (f g : Nat → Bool) :
    XF.val (fun k => XF.shlBits (XF.zext w f) wr g k) w = (XF.val f w * 2 ^ XF.val g wr) % 2 ^ w := by
  have h := XF.bv_shlBits (w := w) (wl := w) (wr := wr) f g
  have := congrArg BitVec.toNat h
  simp only [XF.toNat_bv, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq] at this
  rw [Nat.mod_eq_of_lt (XF.val_lt f w)] at this
  exact this

/-- **A logical right shift by a vector**: `w` bits of `f >> g` (`g` of `wr` bits) have the value
`val f w / 2^(val g wr)`. -/
theorem val_shrBits (w wr : Nat) (f g : Nat → Bool) :
    XF.val (fun k => XF.shrBits w f wr g k) w = XF.val f w / 2 ^ XF.val g wr := by
  have h := XF.bv_shrBits (w := w) (wl := w) (wr := wr) f g
  have := congrArg BitVec.toNat h
  simp only [XF.toNat_bv, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (XF.val_lt f w))] at this
  exact this

/-- `a << 1` at width `P`, the constant `1` a vector of `wr ≥ 1` bits (`wr = 32` for SV's unsized `1`): twice the
value, modulo `2^P`. -/
theorem val_shlBits_one (f : Nat → Bool) (P wr : Nat) (h : 1 ≤ wr) :
    XF.val (fun k => XF.shlBits (XF.zext P f) wr (fun x => XF.constBit 1 wr x) k) P = (XF.val f P * 2) % 2 ^ P := by
  rw [val_shlBits_zext, val_constBit_one wr wr h (Nat.le_refl _), Nat.pow_one]

/-- **The top bit of a `P`-bit value** (`P ≥ 1`) is the test `2^(P-1) ≤ value`. -/
theorem top_bit_iff (f : Nat → Bool) (P x : Nat) (hP : 1 ≤ P) (h : XF.val f P = x) :
    f (P - 1) = true ↔ 2 ^ (P - 1) ≤ x := by
  have hb := bit_eq_of_val f P x (P - 1) h (by omega)
  have hlt : x < 2 * 2 ^ (P - 1) := by
    have := h ▸ XF.val_lt f P
    have e : 2 ^ P = 2 * 2 ^ (P - 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, P = t + 1 := ⟨P - 1, by omega⟩
      simp [Nat.pow_succ]; omega
    omega
  have hbt := Lib.div_mod_two_eq_zero_iff_lt x (2 ^ (P - 1)) hlt
  rw [hb]
  rw [decide_eq_true_iff]
  have : x / 2 ^ (P - 1) % 2 = 1 ↔ ¬ (x / 2 ^ (P - 1) % 2 = 0) := by omega
  rw [this, hbt]
  omega

/-- `XF.val` from the low end: the lowest bit, then the rest shifted down. -/
theorem val_succ_low (f : Nat → Bool) : ∀ n, XF.val f (n + 1) = (f 0).toNat + 2 * XF.val (fun k => f (k + 1)) n
  | 0 => by simp [XF.val]
  | n + 1 => by
    have ih := val_succ_low f n
    have e : 2 ^ (n + 1) * (f (n + 1)).toNat = 2 * (2 ^ n * (f (n + 1)).toNat) := by
      rw [Nat.pow_succ]; ac_rfl
    show XF.val f (n + 1) + 2 ^ (n + 1) * (f (n + 1)).toNat =
      (f 0).toNat + 2 * (XF.val (fun k => f (k + 1)) n + 2 ^ n * (f (n + 1)).toNat)
    rw [ih, e]; omega

/-- `XF.val` from the high end (its definition). -/
theorem val_succ (f : Nat → Bool) (n : Nat) : XF.val f (n + 1) = XF.val f n + 2 ^ n * (f n).toNat := rfl

/-- The value of one bit is that bit. -/
theorem val_one (f : Nat → Bool) : XF.val f 1 = (f 0).toNat := by
  show XF.val f 0 + 2 ^ 0 * (f 0).toNat = (f 0).toNat
  simp [XF.val]

/-- The value of `n` clear bits is `0`. -/
theorem val_false (n : Nat) : XF.val (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [val_succ, ih]

/-- The value of the window `fa[m +: n]` when `fa` agrees with `av.testBit` below `m + n`: bits `[m, m + n)` of
`av`. -/
theorem val_window_of_testBit (fa : Nat → Bool) (av m n : Nat) (ha : ∀ j, j < m + n → fa j = av.testBit j) :
    XF.val (fun x => fa (m + x)) n = av / 2 ^ m % 2 ^ n :=
  val_of_testBit (fun k hk => by rw [ha (m + k) (by omega), Nat.testBit_div_two_pow, Nat.add_comm k m])

/-- The value of a prefix: the low `m ≤ n` bits of `f` are `XF.val f n` modulo `2^m`. -/
theorem val_prefix (f : Nat → Bool) (n m : Nat) (h : m ≤ n) : XF.val f m = XF.val f n % 2 ^ m :=
  val_of_testBit (fun k hk => (XF.testBit_val f n k (by omega)).symm)

/-- The value of `m + n` bits split at `m`: the low `m` bits plus `2^m` times the next `n`. -/
theorem val_split (f : Nat → Bool) (m : Nat) :
    ∀ n, XF.val f (m + n) = XF.val f m + 2 ^ m * XF.val (fun x => f (m + x)) n
  | 0 => by simp [XF.val]
  | n + 1 => by
    have ih := val_split f m n
    have e1 : XF.val f (m + (n + 1)) = XF.val f (m + n) + 2 ^ (m + n) * (f (m + n)).toNat := val_succ f (m + n)
    have e2 : XF.val (fun x => f (m + x)) (n + 1) =
        XF.val (fun x => f (m + x)) n + 2 ^ n * (f (m + n)).toNat := val_succ (fun x => f (m + x)) n
    rw [e1, e2, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]
    omega

/-- Every bit of the constant `0` is clear, at any width. -/
theorem constBit_zero (M x : Nat) : XF.constBit 0 M x = false := by
  have hpos : (0 : Int) < (2 : Int) ^ M := by exact_mod_cast Nat.two_pow_pos M
  have e1 : (0 : Int).emod ((2 : Int) ^ M) = 0 := Int.emod_eq_of_lt (by omega) hpos
  unfold XF.constBit
  rw [e1]
  simp

/-- The value of any number of bits of the constant `0` is `0`. -/
theorem val_constBit_zero (W w : Nat) : XF.val (fun x => XF.constBit 0 W x) w = 0 := by
  rw [XF.val_congr_lt (g := fun _ => false) (fun j _ => constBit_zero W j)]
  exact val_false w

/-- The value of `n` set bits is `2^n - 1`. -/
theorem val_all_true (f : Nat → Bool) (n : Nat) (h : ∀ k, k < n → f k = true) : XF.val f n = 2 ^ n - 1 := by
  have hb : XF.val f n = (2 ^ n - 1) % 2 ^ n :=
    val_of_testBit (fun k hk => by rw [h k hk, Nat.testBit_two_pow_sub_one]; simp [hk])
  rw [hb]
  exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos n; omega)

/-- The value of `n` clear bits (given bitwise) is `0`. -/
theorem val_all_false (f : Nat → Bool) (n : Nat) (h : ∀ k, k < n → f k = false) : XF.val f n = 0 := by
  rw [XF.val_congr_lt (g := fun _ => false) h]
  exact val_false n

/-- The top bit of an `(n + 1)`-bit value is the test `2^n ≤ value` (`top_bit_iff` at `P = n + 1`, without the
subtraction). -/
theorem top_bit_succ_iff (f : Nat → Bool) (n x : Nat) (h : XF.val f (n + 1) = x) : f n = true ↔ 2 ^ n ≤ x := by
  have hlt : x < 2 * 2 ^ n := by
    have hl := XF.val_lt f (n + 1)
    rw [h, Nat.pow_succ] at hl
    omega
  have hb := bit_eq_of_val f (n + 1) x n h (by omega)
  have hbt := Lib.div_mod_two_eq_zero_iff_lt x (2 ^ n) hlt
  rw [hb, decide_eq_true_iff]
  have : x / 2 ^ n % 2 = 1 ↔ ¬ (x / 2 ^ n % 2 = 0) := by omega
  rw [this, hbt]
  omega

/-- `XF.eqv w f g` (the equality `f == g` of `w` bits) is the test `XF.val f w = XF.val g w`. -/
theorem eqv_eq_decide_val (w : Nat) (f g : Nat → Bool) : XF.eqv w f g = decide (XF.val f w = XF.val g w) := by
  rw [Bool.eq_iff_iff, XF.eqv_eq_true, decide_eq_true_iff]
  constructor
  · intro h
    exact XF.val_congr_lt h
  · intro h k hk
    rw [← XF.testBit_val f w k hk, ← XF.testBit_val g w k hk, h]

/-- The complement `~x`: `2^n - 1 - x`. -/
theorem val_not (f : Nat → Bool) (n : Nat) : XF.val (fun x => !f x) n = 2 ^ n - 1 - XF.val f n := by
  have key : ∀ n, XF.val (fun x => !f x) n + XF.val f n = 2 ^ n - 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [val_succ, val_succ, Nat.pow_succ]
      have hp := Nat.two_pow_pos n
      cases f n <;> simp <;> omega
  have := key n
  omega

/-- The concatenation `{x, 1'b0}` (a clear bit below `f`): twice the value. -/
theorem val_cons_false (f : Nat → Bool) (n : Nat) :
    XF.val (fun x => if x = 0 then false else f (x - 1)) (n + 1) = 2 * XF.val f n := by
  rw [val_succ_low]
  simp

/-- A value cut into four fields: bits `[0, a)`, bit `a`, bits `[a + 1, a + 1 + w)` and the top bit. -/
theorem val_four (f : Nat → Bool) (a w : Nat) :
    XF.val f (a + 1 + w + 1) = XF.val f a + (f a).toNat * 2 ^ a + XF.val (fun x => f (a + 1 + x)) w * 2 ^ (a + 1) +
      (f (a + 1 + w)).toNat * 2 ^ (a + 1 + w) := by
  rw [val_succ f (a + 1 + w), val_split f (a + 1) w, val_succ f a,
    Nat.mul_comm (2 ^ a) (f a).toNat, Nat.mul_comm (2 ^ (a + 1)) (XF.val (fun x => f (a + 1 + x)) w),
    Nat.mul_comm (2 ^ (a + 1 + w)) (f (a + 1 + w)).toNat]

end LeanModels.Sv.XF
