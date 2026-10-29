/-!
# Gate-level library for `sv_comb` consumers (plain Lean, no ls-sv dependency)

Ported from `svgolf/design/ideal_add_lib.lean` and `svgolf/design/ideal_mul.lean` (`LeanModels` may
not import `svgolf`): the value of a bit function (`bfVal`), the full-adder arithmetic, the
ripple-row theorem shared by adders and multipliers, row-major injectivity, lexicographic order,
the bridges from a value equation to a `BitVec` equation, and the two consumer halves:

* `AddView` / `add_value` / `add_spec` — the adder, from its four pointwise equations;
* `MulNetlistView` / `ideal_mul` / `ideal_mul_view` — the array multiplier, from its thirteen.

Nothing here mentions `Design2`, a state, or a process: these are the player-side lemmas the
equations produced by `sv_equations` (`CombEq*.lean`) are fed to. Core Lean only.
-/

namespace LeanModels.Sv.CombLib


/-! ## Gate-level library: the value of a bit function -/

/-- `bfVal f n = Σ_{j<n} 2^j · f j`. -/
def bfVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bfVal f n + 2 ^ n * (f n).toNat

theorem bfVal_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j < n, f j = g j) :
    bfVal f n = bfVal g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem bfVal_testBit (x n : Nat) : bfVal (x.testBit) n = x % 2 ^ n := by
  induction n with
  | zero => simp [bfVal, Nat.mod_one]
  | succ n ih =>
    simp only [bfVal, ih]
    rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    have h2 : x / 2 ^ n % 2 = 0 ∨ x / 2 ^ n % 2 = 1 := by omega
    rcases h2 with h | h <;> simp [h]

theorem bfVal_bv {w : Nat} (x : BitVec w) : bfVal x.getLsbD w = x.toNat := by
  have : x.getLsbD = x.toNat.testBit := by funext i; rfl
  rw [this, bfVal_testBit, Nat.mod_eq_of_lt x.isLt]

theorem bfVal_shift (f : Nat → Bool) (n : Nat) :
    bfVal f (n + 1) = (f 0).toNat + 2 * bfVal (fun j => f (j + 1)) n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    rw [bfVal, ih, bfVal]
    simp only [Nat.pow_succ]
    generalize (f (n + 1)).toNat = F
    generalize 2 ^ n = P
    grind

theorem bfVal_split (f : Nat → Bool) (m n : Nat) :
    bfVal f (m + n) = bfVal f m + 2 ^ m * bfVal (fun j => f (m + j)) n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    rw [← Nat.add_assoc, bfVal, ih, bfVal, Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

theorem bfVal_and (x : Nat → Bool) (y : Bool) (n : Nat) :
    bfVal (fun j => x j && y) n = y.toNat * bfVal x n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    simp only [bfVal, ih]
    cases y <;> simp

/-- One full adder, as arithmetic: `sum + 2·carry = x + y + cin`. -/
theorem fullAdder_arith (x y c : Bool) :
    ((x ^^ y) ^^ c).toNat + 2 * ((x && y) || (c && (x ^^ y))).toNat =
      x.toNat + y.toNat + c.toNat := by
  cases x <;> cases y <;> cases c <;> decide

/-- **A ripple row computes a sum.** `t j = x j ^^ y j`, `s j = t j ^^ c j`,
`c (j+1) = (x j && y j) || (c j && t j)` for `j < N` give
`Σ 2^j s_j + 2^N c_N = Σ 2^j x_j + Σ 2^j y_j + c_0`. -/
theorem ripple_row (N : Nat) (x y t s c : Nat → Bool)
    (ht : ∀ j < N, t j = (x j ^^ y j))
    (hs : ∀ j < N, s j = (t j ^^ c j))
    (hc : ∀ j < N, c (j + 1) = ((x j && y j) || (c j && t j))) :
    bfVal s N + 2 ^ N * (c N).toNat = bfVal x N + bfVal y N + (c 0).toNat := by
  suffices h : ∀ n ≤ N, bfVal s n + 2 ^ n * (c n).toNat = bfVal x n + bfVal y n + (c 0).toNat from
    h N (Nat.le_refl N)
  intro n
  induction n with
  | zero => intro _; simp [bfVal]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    have hfa := fullAdder_arith (x n) (y n) (c n)
    rw [← ht n (by omega)] at hfa
    rw [← hs n (by omega), ← hc n (by omega)] at hfa
    simp only [bfVal, Nat.pow_succ]
    generalize (s n).toNat = S at *
    generalize (c (n + 1)).toNat = C at *
    generalize (c n).toNat = C0 at *
    generalize (x n).toNat = X at *
    generalize (y n).toNat = Y at *
    generalize 2 ^ n = P at *
    -- ih : Σs + P*C0 = Σx + Σy + c0 ; hfa : S + 2*C = X + Y + C0
    have : P * (S + 2 * C) = P * (X + Y + C0) := by rw [hfa]
    simp only [Nat.mul_add, Nat.mul_assoc] at this ⊢
    omega

theorem bfVal_bv_mod {w : Nat} (x : BitVec w) (n : Nat) : bfVal x.getLsbD n = x.toNat % 2 ^ n := by
  have : x.getLsbD = x.toNat.testBit := by funext i; rfl
  rw [this, bfVal_testBit]


/-! ## Row-major windows and ranks -/

/-- A row-major index `i * W + j` with the column in range determines the row and the column.
The one nonlinear fact behind every 2-D window-disjointness goal. -/
theorem rowMajor_inj {W i j i' j' : Nat} (hj : j < W) (hj' : j' < W)
    (h : i * W + j = i' * W + j') : i = i' ∧ j = j' := by
  have hW : 0 < W := by omega
  have h1 : (i * W + j) / W = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i' * W + j') / W = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hj', Nat.zero_add]
  have hi : i = i' := by rw [← h1, ← h2, h]
  subst hi
  exact ⟨rfl, by omega⟩

/-- Lexicographic order on `(row, column)` pairs: a rank for 2-D dependencies. -/
def lexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem lexLt_wf : WellFounded lexLt := by
  have : lexLt = Prod.Lex (· < ·) (· < ·) := by
    funext p q; apply propext; rw [Prod.lex_def]; rfl
  rw [this]
  exact (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- Reading the previous row, or an earlier column of the same row, decreases `lexLt`. -/
theorem lexLt_prev_row {i j j' : Nat} : lexLt (i, j') (i + 1, j) := Or.inl (Nat.lt_succ_self i)
theorem lexLt_same_row {i j : Nat} : lexLt (i, j) (i, j + 1) := Or.inr ⟨rfl, Nat.lt_succ_self j⟩

/-! ## The bridge from a value equation to a `BitVec` equation -/

/-- If `s < 2^w` and `t = s + 2^w · q`, then `s = t mod 2^w` and `q = t / 2^w`. -/
theorem sum_split {w s q t : Nat} (hs : s < 2 ^ w) (ht : t = s + 2 ^ w * q) :
    s = t % 2 ^ w ∧ q = t / 2 ^ w := by
  subst ht
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hs, Nat.zero_add]

theorem bitvec_eq_ofNat_of_val {w : Nat} (x : BitVec w) {s t : Nat}
    (hx : x.toNat = s) (hs : s = t % 2 ^ w) : x = BitVec.ofNat w t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hx, hs]

theorem ofBool_eq_ofNat (b : Bool) : BitVec.ofBool b = BitVec.ofNat 1 b.toNat := by
  cases b <;> rfl

/-! # The adder on the bit-function library (draft)

The producer contract, in value form: the sum is a bit function, so no `BitVec.carry` lemma and
no `xor_assoc` step are needed. -/

structure AddView (N : Nat) (a b : BitVec N) (cin : Bool)
    (c s : Nat → Bool) (cout : Bool) : Prop where
  carry_zero : c 0 = cin
  carry_step : ∀ i < N, c (i + 1) =
    ((a.getLsbD i && b.getLsbD i) || (c i && (a.getLsbD i ^^ b.getLsbD i)))
  sum_bit : ∀ i < N, s i = (a.getLsbD i ^^ b.getLsbD i ^^ c i)
  carry_out : cout = c N

/-- The adder, as a value equation: `Σ 2^j s_j + 2^N · cout = a + b + cin`. -/
theorem add_value {N : Nat} {a b : BitVec N} {cin : Bool} {c s : Nat → Bool} {cout : Bool}
    (hv : AddView N a b cin c s cout) :
    bfVal s N + 2 ^ N * cout.toNat = a.toNat + b.toNat + cin.toNat := by
  have hr := ripple_row N a.getLsbD b.getLsbD (fun i => a.getLsbD i ^^ b.getLsbD i) s c
    (fun _ _ => rfl) hv.sum_bit hv.carry_step
  rw [hv.carry_zero, bfVal_bv, bfVal_bv] at hr
  rw [hv.carry_out]
  exact hr

/-- The task statement's form, for an adder whose sum port is a `BitVec`. -/
theorem add_spec {N : Nat} {a b : BitVec N} {cin : Bool} {c : Nat → Bool}
    {sv : BitVec N} {cout : Bool} (hv : AddView N a b cin c sv.getLsbD cout) :
    sv = BitVec.ofNat N (a.toNat + b.toNat + cin.toNat) ∧
    BitVec.ofBool cout = BitVec.ofNat 1 ((a.toNat + b.toNat + cin.toNat) / 2 ^ N) := by
  have hval := add_value hv
  rw [bfVal_bv] at hval
  have ⟨h1, h2⟩ := sum_split sv.isLt hval.symm
  refine ⟨bitvec_eq_ofNat_of_val sv rfl h1, ?_⟩
  rw [ofBool_eq_ofNat, h2]

/-! # The array multiplier on the bit-function library -/

/-- THE IDEAL GOAL for `mul_n.sv`, as `sv_comb` would leave it: 2-D signals are bit functions
`Nat → Nat → Bool` (row, column); every hypothesis is one `assign` of the SV, transcribed. -/
theorem ideal_mul {N : Nat} (hN : 1 ≤ N) (a b : BitVec N) (p : BitVec (2 * N))
    (pp t s c : Nat → Nat → Bool)
    -- assign pp[i][j] = a[j] & b[i]
    (hpp : ∀ i < N, ∀ j < N, pp i j = (a.getLsbD j && b.getLsbD i))
    -- assign s[0] = {1'b0, pp[0]}; assign c[0] = '0; assign t[0] = '0
    (hs0 : ∀ j < N, s 0 j = pp 0 j) (hs0N : s 0 N = false)
    (hc0 : ∀ j, j ≤ N → c 0 j = false) (ht0 : ∀ j < N, t 0 j = false)
    -- rows 1 ≤ i < N
    (hci0 : ∀ i, 1 ≤ i → i < N → c i 0 = false)
    (hti : ∀ i, 1 ≤ i → i < N → ∀ j < N, t i j = (s (i - 1) (j + 1) ^^ pp i j))
    (hsi : ∀ i, 1 ≤ i → i < N → ∀ j < N, s i j = (t i j ^^ c i j))
    (hci : ∀ i, 1 ≤ i → i < N → ∀ j < N,
        c i (j + 1) = ((s (i - 1) (j + 1) && pp i j) || (c i j && t i j)))
    (hsiN : ∀ i, 1 ≤ i → i < N → s i N = c i N)
    -- assign p[i] = s[i][0]; assign p[2*N-1:N] = s[N-1][N:1]
    (hpl : ∀ i < N, p.getLsbD i = s i 0)
    (hph : ∀ j < N, p.getLsbD (N + j) = s (N - 1) (j + 1)) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) := by
  -- value of a partial-product row
  have hppv : ∀ i < N, bfVal (pp i) N = (b.getLsbD i).toNat * a.toNat := by
    intro i hi
    rw [bfVal_congr (g := fun j => a.getLsbD j && b.getLsbD i) (fun j hj => hpp i hi j hj),
      bfVal_and, bfVal_bv]
  -- row 0, and a later row, as sums
  have hW0 : bfVal (s 0) (N + 1) = a.toNat * (b.getLsbD 0).toNat := by
    have : bfVal (s 0) N = bfVal (pp 0) N := bfVal_congr hs0
    rw [bfVal, hs0N, this, hppv 0 (by omega)]
    simp [Nat.mul_comm]
  have hWi : ∀ i, 1 ≤ i → i < N →
      bfVal (s i) (N + 1) = bfVal (fun j => s (i - 1) (j + 1)) N + bfVal (pp i) N := by
    intro i h1 h2
    have hr := ripple_row N (fun j => s (i - 1) (j + 1)) (pp i) (t i) (s i) (c i)
      (hti i h1 h2) (hsi i h1 h2) (hci i h1 h2)
    rw [hci0 i h1 h2] at hr
    rw [bfVal, hsiN i h1 h2]
    simpa using hr
  -- the row invariant: low output bits so far + shifted row = a * (low bits of b)
  have inv : ∀ i, i < N →
      bfVal (fun k => s k 0) i + 2 ^ i * bfVal (s i) (N + 1) = a.toNat * (b.toNat % 2 ^ (i + 1)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hW0, ← bfVal_bv_mod b 1]
      simp [bfVal, Nat.mul_comm]
    | succ i ih =>
      intro hi
      have ih := ih (by omega)
      have hW := hWi (i + 1) (by omega) hi
      simp only [Nat.add_sub_cancel] at hW
      rw [hppv (i + 1) hi] at hW
      have hsh := bfVal_shift (s i) N
      have hb : b.toNat % 2 ^ (i + 1 + 1) =
          b.toNat % 2 ^ (i + 1) + 2 ^ (i + 1) * (b.getLsbD (i + 1)).toNat := by
        rw [← bfVal_bv_mod b (i + 1 + 1), bfVal, bfVal_bv_mod]
      rw [hW, hb]
      simp only [bfVal, Nat.pow_succ] at *
      rw [hsh] at ih
      generalize (s i 0).toNat = S at *
      generalize (b.getLsbD (i + 1)).toNat = B at *
      generalize bfVal (fun j => s i (j + 1)) N = X at *
      generalize bfVal (fun k => s k 0) i = L at *
      generalize 2 ^ i = P at *
      generalize b.toNat % 2 ^ (i + 1) = M at *
      generalize a.toNat = A at *
      grind
  -- assemble the product
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hi := inv n (by omega)
  have hbn : b.toNat % 2 ^ (n + 1) = b.toNat := Nat.mod_eq_of_lt b.isLt
  rw [hbn] at hi
  have hp : p.toNat = a.toNat * b.toNat := by
    have hsplit := bfVal_split p.getLsbD (n + 1) (n + 1)
    rw [show (n + 1) + (n + 1) = 2 * (n + 1) by omega, bfVal_bv] at hsplit
    rw [hsplit]
    have h1 : bfVal p.getLsbD (n + 1) = bfVal (fun k => s k 0) (n + 1) :=
      bfVal_congr (fun j hj => hpl j hj)
    have h2 : bfVal (fun j => p.getLsbD ((n + 1) + j)) (n + 1) =
        bfVal (fun j => s n (j + 1)) (n + 1) :=
      bfVal_congr (fun j hj => by simpa using hph j hj)
    rw [h1, h2, ← hi]
    have hsh := bfVal_shift (s n) (n + 1)
    simp only [bfVal, Nat.pow_succ] at *
    rw [hsh]
    generalize (s n 0).toNat = S at *
    generalize bfVal (fun j => s n (j + 1)) (n + 1) = X at *
    generalize bfVal (fun k => s k 0) n = L at *
    generalize 2 ^ n = P at *
    grind
  apply BitVec.eq_of_toNat_eq
  rw [hp, BitVec.toNat_ofNat]
  have hlt : a.toNat * b.toNat < 2 ^ (2 * (n + 1)) := by
    rw [show 2 * (n + 1) = (n + 1) + (n + 1) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul'' a.isLt b.isLt
  rw [Nat.mod_eq_of_lt hlt]

/-- THE PRODUCER CONTRACT for `mul_n.sv`: one field per group of `assign`s. 2-D signals are
bit functions (row, column); `s`/`c` rows have `N + 1` columns, `pp`/`t` rows have `N`. -/
structure MulNetlistView (N : Nat) (a b : BitVec N) (p : BitVec (2 * N))
    (pp t s c : Nat → Nat → Bool) : Prop where
  pp_def : ∀ i < N, ∀ j < N, pp i j = (a.getLsbD j && b.getLsbD i)
  s0 : ∀ j < N, s 0 j = pp 0 j
  s0_top : s 0 N = false
  c0 : ∀ j, j ≤ N → c 0 j = false
  t0 : ∀ j < N, t 0 j = false
  ci0 : ∀ i, 1 ≤ i → i < N → c i 0 = false
  t_def : ∀ i, 1 ≤ i → i < N → ∀ j < N, t i j = (s (i - 1) (j + 1) ^^ pp i j)
  s_def : ∀ i, 1 ≤ i → i < N → ∀ j < N, s i j = (t i j ^^ c i j)
  c_def : ∀ i, 1 ≤ i → i < N → ∀ j < N,
    c i (j + 1) = ((s (i - 1) (j + 1) && pp i j) || (c i j && t i j))
  s_top : ∀ i, 1 ≤ i → i < N → s i N = c i N
  p_low : ∀ i < N, p.getLsbD i = s i 0
  p_high : ∀ j < N, p.getLsbD (N + j) = s (N - 1) (j + 1)

theorem ideal_mul_view {N : Nat} (hN : 1 ≤ N) {a b : BitVec N} {p : BitVec (2 * N)}
    {pp t s c : Nat → Nat → Bool} (hv : MulNetlistView N a b p pp t s c) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) :=
  ideal_mul hN a b p pp t s c hv.pp_def hv.s0 hv.s0_top hv.c0 hv.t0 hv.ci0 hv.t_def hv.s_def
    hv.c_def hv.s_top hv.p_low hv.p_high

/-- info: 'LeanModels.Sv.CombLib.add_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_spec

/-- info: 'LeanModels.Sv.CombLib.ideal_mul_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_mul_view

end LeanModels.Sv.CombLib
