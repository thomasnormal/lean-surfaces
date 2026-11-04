import LeanModels.Sv.CombWord
import LeanModels.Sv.Lib.NatArith

/-!
# `LeanModels.Sv.Lib.XFVal`: the `Nat` value of the word-level bit helpers

`sv_equations` states a netlist over bit functions (`st.boolAt "x" : Nat → Bool`) and the word-level helpers of
`CombKnownBits.lean` / `CombWord.lean`. These are the VALUE lemmas of the helpers, all in `Nat`, so a proof can
carry a netlist into a `Nat` model of the datapath without a `BitVec` cast: `XF.val` of a `testBit` function, of a
window, of a prefix, of a concatenation, of a zero extension, of a constant, of a multiplexer, of the shifts by a
constant and by a vector, of `addBits`/`subBits`, of a complement; the Boolean reductions (`XF.any`, `XF.all`, `XF.eqv`) as tests on
values; a bit of a value; and the recursion of `XF.val` from either end.

In namespace `LeanModels.Sv.XF`, next to the helpers.
-/

namespace LeanModels.Sv.XF

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

theorem val_bits {f : Nat → Bool} {w x : Nat} (h : ∀ k, k < w → f k = x.testBit k) :
    XF.val f w = x % 2 ^ w := (XF.val_congr_lt h).trans (XF.val_testBit x w)

theorem val_win (f : Nat → Bool) (s m n : Nat) (h : s + m ≤ n) :
    XF.val (fun x => f (s + x)) m = XF.val f n / 2 ^ s % 2 ^ m := by
  apply val_bits
  intro k hk
  rw [Nat.testBit_div_two_pow, XF.testBit_val f n (k + s) (by omega), Nat.add_comm k s]

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

theorem any_eq (n : Nat) (f : Nat → Bool) : XF.any n f = decide (XF.val f n ≠ 0) := by
  rw [Bool.eq_iff_iff, XF.any_eq_true, decide_eq_true_iff]
  exact (val_ne_zero_iff f n).symm

theorem all_eq (n : Nat) (f : Nat → Bool) : XF.all n f = decide (XF.val f n = 2 ^ n - 1) := by
  rw [Bool.eq_iff_iff, XF.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h
    have hb : XF.val f n = (2 ^ n - 1) % 2 ^ n :=
      val_bits (fun k hk => by rw [h k hk, Nat.testBit_two_pow_sub_one]; simp [hk])
    rw [hb]
    exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos n; omega)
  · intro h k hk
    rw [XF.testBit_val f n k hk |>.symm, h, Nat.testBit_two_pow_sub_one]
    simp [hk]

/-- A bit of a value known modulo `2^w`. -/
theorem bit_eq (f : Nat → Bool) (w x j : Nat) (h : XF.val f w = x) (hj : j < w) :
    f j = decide (x / 2 ^ j % 2 = 1) := by
  rw [← XF.testBit_val f w j hj, h, Nat.testBit_eq_decide_div_mod_eq]

theorem val_zext_trunc (n m : Nat) (f : Nat → Bool) (h : m ≤ n) : XF.val (XF.zext n f) m = XF.val f m :=
  XF.val_congr_lt (fun k hk => by simp [XF.zext]; omega)

theorem val_const (c : Int) (w : Nat) (hc0 : 0 ≤ c) (hc1 : c < 2 ^ w) :
    XF.val (fun k => XF.constBit c w k) w = c.toNat := by
  have e : c.emod ((2 : Int) ^ w) = c := Int.emod_eq_of_lt hc0 hc1
  have hlt : c.toNat < 2 ^ w := by
    have h3 : (c.toNat : Int) = c := Int.toNat_of_nonneg hc0
    have h4 : (c.toNat : Int) < (2 : Int) ^ w := by rw [h3]; exact hc1
    exact_mod_cast h4
  unfold XF.constBit
  rw [XF.val_testBit, e]
  exact Nat.mod_eq_of_lt hlt

theorem val_constBit1 (W' w' : Nat) (h1 : 1 ≤ w') (h2 : w' ≤ W') :
    XF.val (fun x => XF.constBit 1 W' x) w' = 1 := by
  have hW : 2 ^ 1 ≤ 2 ^ W' := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : (1 : Int) < (2 : Int) ^ W' := by exact_mod_cast (show 1 < 2 ^ W' by omega)
  have e1 : (1 : Int).emod ((2 : Int) ^ W') = 1 := Int.emod_eq_of_lt (by omega) hlt
  have e : ∀ k, XF.constBit 1 W' k = (1 : Nat).testBit k := by
    intro k
    unfold XF.constBit
    rw [e1]
    try rfl
  rw [XF.val_congr_lt (g := fun k => (1 : Nat).testBit k) (fun j _ => e j), XF.val_testBit]
  have : 2 ^ 1 ≤ 2 ^ w' := Nat.pow_le_pow_right (by omega) h1
  exact Nat.mod_eq_of_lt (by omega)

theorem val_ite (c : Bool) (f g : Nat → Bool) (w : Nat) :
    XF.val (fun k => if c = true then f k else g k) w = if c = true then XF.val f w else XF.val g w := by
  cases c <;> simp

theorem val_addBits (wa wb w : Nat) (fa fb : Nat → Bool) :
    XF.val (fun k => XF.addBits wa fa wb fb k) w = (XF.val fa wa + XF.val fb wb) % 2 ^ w :=
  XF.val_testBit _ w

theorem val_subBits (wa wb w : Nat) (fa fb : Nat → Bool) :
    XF.val (fun k => XF.subBits wa fa wb fb k) w = (XF.val fa wa + (2 ^ max wa wb - XF.val fb wb)) % 2 ^ w :=
  XF.val_testBit _ w

theorem val_shl_var (w wr : Nat) (f g : Nat → Bool) :
    XF.val (fun k => XF.shlBits (XF.zext w f) wr g k) w = (XF.val f w * 2 ^ XF.val g wr) % 2 ^ w := by
  have h := XF.bv_shlBits (w := w) (wl := w) (wr := wr) f g
  have := congrArg BitVec.toNat h
  simp only [XF.toNat_bv, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq] at this
  rw [Nat.mod_eq_of_lt (XF.val_lt f w)] at this
  exact this

theorem val_shr_var (w wr : Nat) (f g : Nat → Bool) :
    XF.val (fun k => XF.shrBits w f wr g k) w = XF.val f w / 2 ^ XF.val g wr := by
  have h := XF.bv_shrBits (w := w) (wl := w) (wr := wr) f g
  have := congrArg BitVec.toNat h
  simp only [XF.toNat_bv, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (XF.val_lt f w))] at this
  exact this

/-- The unsized constant `1` (a 32-bit vector). -/
theorem val_const1 : XF.val (fun x => XF.constBit 1 32 x) 32 = 1 := by
  have := val_const 1 32 (by omega) (by omega)
  simpa using this

/-- `a << 1` at width `P` (the unsized constant `1` is a 32-bit vector). -/
theorem val_shl1 (f : Nat → Bool) (P : Nat) :
    XF.val (fun k => XF.shlBits (XF.zext P f) 32 (fun x => XF.constBit 1 32 x) k) P = (XF.val f P * 2) % 2 ^ P := by
  rw [val_shl_var, val_const1, Nat.pow_one]

/-- The top bit of a `P`-bit value is the test `2^(P-1) <= value`. -/
theorem top_bit (f : Nat → Bool) (P x : Nat) (hP : 1 ≤ P) (h : XF.val f P = x) :
    f (P - 1) = true ↔ 2 ^ (P - 1) ≤ x := by
  have hb := bit_eq f P x (P - 1) h (by omega)
  have hlt : x < 2 * 2 ^ (P - 1) := by
    have := h ▸ XF.val_lt f P
    have e : 2 ^ P = 2 * 2 ^ (P - 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, P = t + 1 := ⟨P - 1, by omega⟩
      simp [Nat.pow_succ]; omega
    omega
  have hbt := Lib.bit_top x (2 ^ (P - 1)) (Nat.two_pow_pos _) hlt
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

theorem val_one (f : Nat → Bool) : XF.val f 1 = (f 0).toNat := by
  show XF.val f 0 + 2 ^ 0 * (f 0).toNat = (f 0).toNat
  simp [XF.val]

theorem val_false (n : Nat) : XF.val (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [val_succ, ih]

theorem val_win_in (fa : Nat → Bool) (av m n : Nat) (ha : ∀ j, j < m + n → fa j = av.testBit j) :
    XF.val (fun x => fa (m + x)) n = av / 2 ^ m % 2 ^ n :=
  val_bits (fun k hk => by rw [ha (m + k) (by omega), Nat.testBit_div_two_pow, Nat.add_comm k m])

theorem val_low_in (fa : Nat → Bool) (av n : Nat) (ha : ∀ j, j < n → fa j = av.testBit j) :
    XF.val fa n = av % 2 ^ n :=
  val_bits ha

theorem val_prefix (f : Nat → Bool) (n m : Nat) (h : m ≤ n) : XF.val f m = XF.val f n % 2 ^ m :=
  val_bits (fun k hk => (XF.testBit_val f n k (by omega)).symm)

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

theorem val_zext_eta (n : Nat) (f : Nat → Bool) (m : Nat) (h : n ≤ m) :
    XF.val (fun k => XF.zext n f k) m = XF.val f n := XF.val_zext n f m h

theorem val_ztr (n m : Nat) (f : Nat → Bool) (h : m ≤ n) :
    XF.val (fun k => XF.zext n f k) m = XF.val f m := val_zext_trunc n m f h

theorem constBit0_false (M x : Nat) : XF.constBit 0 M x = false := by
  have hpos : (0 : Int) < (2 : Int) ^ M := by exact_mod_cast Nat.two_pow_pos M
  have e1 : (0 : Int).emod ((2 : Int) ^ M) = 0 := Int.emod_eq_of_lt (by omega) hpos
  unfold XF.constBit
  rw [e1]
  simp

theorem val_constBit0 (W' w' : Nat) : XF.val (fun x => XF.constBit 0 W' x) w' = 0 := by
  rw [XF.val_congr_lt (g := fun _ => false) (fun j _ => constBit0_false W' j)]
  exact val_false w'

theorem val_all_true (f : Nat → Bool) (n : Nat) (h : ∀ k, k < n → f k = true) : XF.val f n = 2 ^ n - 1 := by
  have hb : XF.val f n = (2 ^ n - 1) % 2 ^ n :=
    val_bits (fun k hk => by rw [h k hk, Nat.testBit_two_pow_sub_one]; simp [hk])
  rw [hb]
  exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos n; omega)

theorem val_all_false (f : Nat → Bool) (n : Nat) (h : ∀ k, k < n → f k = false) : XF.val f n = 0 := by
  rw [XF.val_congr_lt (g := fun _ => false) h]
  exact val_false n

/-- The top bit of an `(n + 1)`-bit value is the test `2^n <= value`. -/
theorem top_bit' (f : Nat → Bool) (n x : Nat) (h : XF.val f (n + 1) = x) : f n = true ↔ 2 ^ n ≤ x := by
  have hlt : x < 2 * 2 ^ n := by
    have hl := XF.val_lt f (n + 1)
    rw [h, Nat.pow_succ] at hl
    omega
  have hb := bit_eq f (n + 1) x n h (by omega)
  have hbt := Lib.bit_top x (2 ^ n) (Nat.two_pow_pos _) hlt
  rw [hb, decide_eq_true_iff]
  have : x / 2 ^ n % 2 = 1 ↔ ¬ (x / 2 ^ n % 2 = 0) := by omega
  rw [this, hbt]
  omega

theorem eqv_val (w : Nat) (f g : Nat → Bool) : XF.eqv w f g = decide (XF.val f w = XF.val g w) := by
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

/-- The concatenation `{x, 1'b0}`: twice the value. -/
theorem val_shl0 (f : Nat → Bool) (n : Nat) :
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
