import LeanModels.Sv.Known2
import LeanModels.Sv.Comb2Base

/-!
# The x-free fragment: static widths, Boolean bit functions, expression-level knownness

Part 1 of the **x-free knownness theorem** (`docs/sv-comb-design.md`, principle 14); part 2 is
`CombKnownThm.lean`. Lane K of the `sv_comb` effort. Nothing here mentions a design's processes:
this file is about ONE expression and ONE state.

A four-state value is *known* when every bit is `0` or `1`. The static checks of svGolf's
`fourstate` stage (`svgolf/score/fourstate.py`) refuse every SOURCE of an `x`/`z` (literals,
unknown constants, out-of-range reads, undriven nets, latches, loops, division by zero); this
file and its sibling prove, once, that for designs in the fragment below those checks suffice:
with known inputs, every settled signal is known, and every bit has an explicit Boolean
equation. `sv_known` is then an application of the theorem plus the static check, and
`sv_equations` reads its pointwise Boolean equations off `CombKnown.settled`.

## The fragment (`Expr2.xfWidth d e = some w`)

`xfWidth` is a structural function `Design2 → Expr2 → Option Nat`: `some w` means "`e` is in the
fragment over the declarations of `d` and is statically `w` bits wide". Covered:

| form | width | condition |
|---|---|---|
| `lit v` | `v.width` | `v.knownB` = `v.allKnown` (no `x`/`z` digit) |
| `ident n` | declared width of `n` | `n` is declared |
| `~a`, `!a`, `+a`, `-a` | `w` / `1` / `w` / `w` | `a` in the fragment |
| `a & b`, `a \| b`, `a ^ b` | `w` | both operands in the fragment, SAME width |
| `a + b`, `a - b`, `a * b` | `max wa wb` | both operands in the fragment |
| `a == b`, `a != b`, `a === b`, `a !== b` | `1` | both operands in the fragment, SAME width |
| `a < b`, `a <= b`, `a > b`, `a >= b` | `1` | both operands in the fragment |
| `a << b`, `a >> b`, `a <<< b`, `a >>> b` (unsigned) | width of `a` | both operands in the fragment |
| `a && b`, `a \|\| b` | `1` | both operands in the fragment (any widths) |
| `&a \| ~&a \| …` (reductions) | `1` | `a` in the fragment |
| `c ? t : f` | `w` | `c` in the fragment (any width); `t`, `f` of the same width |
| `{p₀, …, pₙ}` | sum of the parts | every part in the fragment |
| `{n{a}}` (`repl`) | `n * wa` | `a` in the fragment |
| `a[lo +: k]` (`slice`) | `k` | `a` in the fragment, `lo + k ≤` width of `a`, `0 < k` |
| `resize k a` | `k` | `a` in the fragment (zero-extend / truncate: no `x` appears) |

The bitwise rows have a bit-level Boolean equation (`Expr2.xfBits` is a bitwise function of the
operands' bits); the word-level rows (`+ - *`, comparisons, shifts, `-`) have it through the
unsigned value `XF.val` of a bit function (`XF.addBits`, `XF.subBits`, `XF.mulBits`,
`XF.shlBits`, …): `(XF.val fa wa + XF.val fb wb).testBit k`. `LVec.ofBoolFn w f =
LVec.ofBitVec (XF.bv w f)` (`LVec.ofBoolFn_eq_ofBitVec_bv`) is the bridge to `BitVec`.

NOT covered (`xfWidth = none`), and why:

* **mismatched widths** of a bitwise/equality/ternary pair: `LVec.zipWith` and `eqLogical`
  answer all-`x` on a width mismatch, so the fragment must rule it out statically (the
  instantiated gate-level designs never have one: `fitExpr2` inserts `resize`);
* **dynamic `index`** (`a[i]` with a run-time `i`): the read is in range only if the VALUE of `i`
  is, which is not a static fact (fourstate rule (d) bounds it by the index TYPE; a constant
  index is already a `slice` after instantiation);
* **`/ % **`**: a zero divisor (or a negative exponent) gives `x`; the task bans run-time
  `/` and `%` and fourstate has no rule for them, so a design using them is outside;
* **signed forms** (`scmp`, `slt …`, `resizeSigned`, `>>>` on a signed left operand) and the
  wildcard equalities `==?`/`!=?`: known operands DO give a known result, but their Boolean
  equations (two's-complement value, sign fill, wildcard matching) are not yet written — an
  extension, not a soundness gap: the theorem simply does not apply to a design that uses them;
* **`squash2`** (the 2-state conversion, `Expr2.squash2`: an assignment to a 2-state declaration):
  on a known operand it is the identity, but the fragment is a FOUR-state one (the comb layer's
  `CombDesign.inFourState`, `CombView.declOf?`), so a design that squashes is outside it and the
  theorem does not apply — the conservative placement, no bit equation is claimed;
* **`unsupported`** nodes.

## Vocabulary

* `LVec.boolAt v k` / `SvState.boolAt st n k` — bit `k` of a vector / of signal `n`, as a `Bool`:
  `true` iff it is a definite `1` (`0`, `x`, `z`, absent: `false`). The Boolean accessor.
* `LVec.ofBoolFn w f` — the known vector of width `w` with bit `k` equal to `f k` (a bit
  function with a width; `LVec.ofBitVec x = LVec.ofBoolFn w x.getLsbD` by `rfl`).
* `Expr2.xfBits d env e : Nat → Bool` — the Boolean evaluator: bit `k` of `e`, given `env n k`
  = Boolean value of bit `k` of signal `n`. One `rfl` equation per constructor
  (`Expr2.xfBits` unfolds). Valid for `k <` the static width; `Expr2.xfBitsZ` is the
  zero-extended read (what a wider target sees).
* `KnownBit st n k` — bit `k` of `n` exists in `st` and is `0`/`1`. `WinKnown`, `WholeKnown`,
  `ReadKnown d st r` — the same for a window / the whole declared vector / a `ReadWin`.

## Design laws

* **Exact, not approximate.** `Expr2.evalPure2_ofBoolFn` is an EQUATION
  `evalPure2 st e = .ok (LVec.ofBoolFn w (e.xfBits d (SvState.boolAt st)))`, so a consumer
  rewrites with it; nothing is "up to knownness".
* **Reads, not signals.** The hypothesis is about `Expr2.reads e` (windows for constant
  slices of an identifier, whole signals otherwise), the same granularity as `Acyclic`: a carry
  chain `c` read one bit at a time needs only those bits known, never the whole vector.
* **Widths are static.** They come from the declarations (`Design2.declWidth`), so they are the
  widths the state holds for every driven signal (`StateShape.driven`) and every known input.
* **Fuel enters only as the induction bound** of `Expr2.evalPure2_ofBoolFn` (`e.size < n`);
  instantiate with `n = e.size + 1`. No `evalExpr2` fuel appears (`Pure2.lean`).
-/

namespace LeanModels.Sv

/-! ## Boolean bit reads -/

/-- Bit `k` of a vector as a Boolean: `true` iff it is a definite `1` (`0`, `x`, `z` and an
out-of-range read are `false`). -/
def LVec.boolAt (v : LVec) (k : Nat) : Bool := v.bits[k]?.getD .lx == .l1

/-- Structural known test: every bit is `0`/`1` (the list form of `LVec.allKnown`, which reduces
in the kernel, so `decide` evaluates the fragment checks on concrete designs). -/
def LVec.knownB (v : LVec) : Bool := v.bits.toList.all Logic.isKnown

theorem LVec.knownB_eq_allKnown (v : LVec) : v.knownB = v.allKnown := by
  simp [LVec.knownB, LVec.allKnown]

/-- Bit `k` of signal `n` of a state as a Boolean (`false` for an unbound name). -/
def SvState.boolAt (st : SvState) (n : String) (k : Nat) : Bool :=
  match SvState.lookup st n with
  | some v => v.boolAt k
  | none => false

theorem Logic.ofBool_beq_l1 (b : Bool) : (Logic.ofBool b == Logic.l1) = b := by
  cases b <;> rfl

theorem Logic.ofBool_beq_l1_of_isKnown {b : Logic} (h : b.isKnown = true) :
    Logic.ofBool (b == Logic.l1) = b := by
  cases b <;> simp_all [Logic.isKnown, Logic.ofBool]

theorem Logic.isKnown_ofBool (b : Bool) : (Logic.ofBool b).isKnown = true := by
  cases b <;> rfl

namespace LVec

/-- The known vector of width `w` whose bit `k` is the Boolean `f k`. -/
def ofBoolFn (w : Nat) (f : Nat → Bool) : LVec :=
  ⟨Array.ofFn (n := w) fun i => Logic.ofBool (f i.val)⟩

@[simp] theorem width_ofBoolFn (w : Nat) (f : Nat → Bool) : (ofBoolFn w f).width = w := by
  simp [ofBoolFn, width]

theorem getElem?_ofBoolFn (w : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBoolFn w f).bits[i]? = if i < w then some (Logic.ofBool (f i)) else none := by
  simp only [ofBoolFn, Array.getElem?_ofFn]
  split <;> simp_all

theorem ofBoolFn_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    ofBoolFn w f = ofBoolFn w g := by
  apply ext_getElem?
  intro i
  rw [getElem?_ofBoolFn, getElem?_ofBoolFn]
  by_cases hi : i < w
  · simp [hi, h i hi]
  · simp [hi]

/-- `ofBitVec` is `ofBoolFn` of its bit function (definitional). -/
theorem ofBitVec_eq_ofBoolFn {w : Nat} (x : BitVec w) : ofBitVec x = ofBoolFn w x.getLsbD := rfl

theorem ofBoolFn_eq_ofBitVec {w : Nat} {x : BitVec w} {f : Nat → Bool}
    (h : ∀ k, k < w → x.getLsbD k = f k) : ofBoolFn w f = ofBitVec x := by
  rw [ofBitVec_eq_ofBoolFn]; exact ofBoolFn_congr (fun k hk => (h k hk).symm)

/-- A fully known vector is `ofBoolFn` of its Boolean bits. -/
theorem eq_ofBoolFn_of_allKnown {v : LVec} (h : v.allKnown = true) :
    v = ofBoolFn v.width v.boolAt := by
  apply ext_getElem?
  intro i
  rw [getElem?_ofBoolFn]
  by_cases hi : i < v.width
  · have hi' : i < v.bits.size := hi
    rw [if_pos hi, Array.getElem?_eq_getElem hi']
    simp only [boolAt, Array.getElem?_eq_getElem hi', Option.getD_some]
    have hk : v.bits[i].isKnown = true := by
      simp only [allKnown, Array.all_eq_true] at h
      exact h i hi'
    rw [Logic.ofBool_beq_l1_of_isKnown hk]
  · rw [if_neg hi]
    exact Array.getElem?_eq_none (by simpa [width] using hi)

/-! ### Operators on `ofBoolFn` -/

theorem not_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (ofBoolFn w f).not = ofBoolFn w (fun k => !f k) := by
  apply ext_getElem?
  intro i
  simp only [LVec.not, Array.getElem?_map, getElem?_ofBoolFn]
  by_cases hi : i < w <;> simp [hi]

theorem zipWith_ofBoolFn (w : Nat) (g : Logic → Logic → Logic) (h : Bool → Bool → Bool)
    (hg : ∀ a b, g (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (h a b))
    (f1 f2 : Nat → Bool) :
    zipWith g (ofBoolFn w f1) (ofBoolFn w f2) = ofBoolFn w (fun k => h (f1 k) (f2 k)) := by
  unfold zipWith
  rw [if_pos (by simp)]
  apply ext_getElem?
  intro i
  show (Array.zipWith g (ofBoolFn w f1).bits (ofBoolFn w f2).bits)[i]? = _
  rw [Array.getElem?_zipWith, getElem?_ofBoolFn, getElem?_ofBoolFn, getElem?_ofBoolFn]
  by_cases hi : i < w
  · simp only [hi, if_true, hg]
  · simp only [hi, if_false]

theorem extract_ofBoolFn {w : Nat} (f : Nat → Bool) {lo k : Nat} (h : lo + k ≤ w) :
    (ofBoolFn w f).extract lo k = ofBoolFn k (fun i => f (lo + i)) := by
  apply ext_getElem?
  intro i
  rw [getElem?_extract, getElem?_ofBoolFn, getElem?_ofBoolFn]
  by_cases hi : i < k
  · have : lo + i < w := by omega
    simp [hi, this]
  · simp [hi]

theorem resizeU_ofBoolFn (w w' : Nat) (f : Nat → Bool) :
    (ofBoolFn w f).resizeU w' = ofBoolFn w' (fun i => decide (i < w) && f i) := by
  apply ext_getElem?
  intro i
  simp only [resizeU, Array.getElem?_ofFn, getElem?_ofBoolFn]
  by_cases hi : i < w'
  · by_cases hw : i < w
    · simp [hi, hw]
    · simp [hi, hw, Logic.ofBool]
  · simp [hi]

/-- A window of a vector all of whose bits are known is the Boolean vector of those bits. -/
theorem extract_eq_ofBoolFn_of_known {v : LVec} {lo w : Nat}
    (h : ∀ k, k < w → ∃ b, v.bits[lo + k]? = some b ∧ b.isKnown = true) :
    v.extract lo w = ofBoolFn w (fun k => v.boolAt (lo + k)) := by
  apply ext_getElem?
  intro i
  rw [getElem?_extract, getElem?_ofBoolFn]
  by_cases hi : i < w
  · obtain ⟨b, hb, hk⟩ := h i hi
    simp only [hi, if_true, hb, Option.getD_some, boolAt]
    rw [Logic.ofBool_beq_l1_of_isKnown hk]
  · simp [hi]

theorem ofLogic_ofBool_eq (b : Bool) :
    LVec.ofLogic (Logic.ofBool b) = ofBoolFn 1 (fun _ => b) := by
  apply ext_getElem?
  intro i
  rw [getElem?_ofBoolFn]
  cases i with
  | zero => simp [ofLogic]
  | succ i => simp [ofLogic]

theorem concat_ofBoolFn (wp W : Nat) (fp g : Nat → Bool) :
    (ofBoolFn wp fp).concat (ofBoolFn W g) =
      ofBoolFn (W + wp) (fun k => if k < W then g k else fp (k - W)) := by
  apply ext_getElem?
  intro i
  simp only [LVec.concat, Array.getElem?_append, getElem?_ofBoolFn]
  have hs : (ofBoolFn W g).bits.size = W := width_ofBoolFn W g
  rw [hs]
  by_cases h1 : i < W
  · simp [h1, show i < W + wp by omega]
  · by_cases h2 : i < W + wp
    · simp [h1, h2, show i - W < wp by omega]
    · simp [h1, h2, show ¬ i - W < wp by omega]

end LVec

/-! ### Boolean reductions -/

namespace XF

/-- `|v`: some bit of the first `w` is set. -/
def any (w : Nat) (f : Nat → Bool) : Bool := decide (∃ k, k < w ∧ f k = true)
/-- `&v`: every bit of the first `w` is set. -/
def all (w : Nat) (f : Nat → Bool) : Bool := decide (∀ k, k < w → f k = true)
/-- `^v`: parity of the first `w` bits. -/
def parity (w : Nat) (f : Nat → Bool) : Bool :=
  (List.ofFn fun i : Fin w => f i.val).foldl (· ^^ ·) false

/-- The Boolean value of a reduction operator over the first `w` bits of `f`. -/
def red : RedOp → Nat → (Nat → Bool) → Bool
  | .or, w, f => any w f
  | .and, w, f => all w f
  | .xor, w, f => parity w f
  | .nor, w, f => !any w f
  | .nand, w, f => !all w f
  | .xnor, w, f => !parity w f

theorem any_eq_true {w : Nat} {f : Nat → Bool} : any w f = true ↔ ∃ k, k < w ∧ f k = true := by
  simp [any]

theorem all_eq_true {w : Nat} {f : Nat → Bool} : all w f = true ↔ ∀ k, k < w → f k = true := by
  simp [all]

theorem all_not (w : Nat) (f : Nat → Bool) : all w (fun k => !f k) = !any w f := by
  cases hc : any w f
  · have h1 : ¬ ∃ k, k < w ∧ f k = true := by simpa [any] using hc
    simp only [all, Bool.not_false, decide_eq_true_eq]
    intro k hk
    cases hf : f k
    · rfl
    · exact absurd ⟨k, hk, hf⟩ h1
  · have h1 : ∃ k, k < w ∧ f k = true := by simpa [any] using hc
    obtain ⟨k, hk, hf⟩ := h1
    simp only [all, Bool.not_true]
    apply decide_eq_false
    intro h
    have := h k hk
    simp [hf] at this

private theorem foldl_map_ofBool (f : Logic → Logic → Logic) (g : Bool → Bool → Bool)
    (hf : ∀ a b, f (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (g a b))
    (l : List Bool) (b : Bool) :
    (l.map Logic.ofBool).foldl f (Logic.ofBool b) = Logic.ofBool (l.foldl g b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldl_cons, hf, ih]

private theorem bits_foldl_ofBoolFn (w : Nat) (f : Nat → Bool) (g' : Logic → Logic → Logic)
    (g : Bool → Bool → Bool)
    (hg : ∀ a b, g' (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (g a b)) (b : Bool) :
    (LVec.ofBoolFn w f).bits.foldl g' (Logic.ofBool b) =
      Logic.ofBool ((List.ofFn fun i : Fin w => f i.val).foldl g b) := by
  rw [← Array.foldl_toList]
  show (Array.ofFn (n := w) fun i => Logic.ofBool (f i.val)).toList.foldl g' _ = _
  rw [Array.toList_ofFn, ← foldl_map_ofBool g' g hg, List.map_ofFn]
  rfl

private theorem foldl_or_eq' (l : List Bool) (b : Bool) :
    l.foldl (· || ·) b = (b || l.any id) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, Bool.or_assoc]

private theorem foldl_and_eq' (l : List Bool) (b : Bool) :
    l.foldl (· && ·) b = (b && l.all id) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, Bool.and_assoc]

theorem redOr_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (LVec.ofBoolFn w f).redOr = Logic.ofBool (any w f) := by
  rw [LVec.redOr, show Logic.l0 = Logic.ofBool false from rfl,
    bits_foldl_ofBoolFn w f _ (· || ·) Logic.or_ofBool, foldl_or_eq']
  congr 1
  rw [Bool.false_or, Bool.eq_iff_iff, any_eq_true, List.any_eq_true]
  simp only [List.mem_ofFn, id]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, i.isLt, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, h⟩

theorem redAnd_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (LVec.ofBoolFn w f).redAnd = Logic.ofBool (all w f) := by
  rw [LVec.redAnd, show Logic.l1 = Logic.ofBool true from rfl,
    bits_foldl_ofBoolFn w f _ (· && ·) Logic.and_ofBool, foldl_and_eq']
  congr 1
  rw [Bool.true_and, Bool.eq_iff_iff, all_eq_true, List.all_eq_true]
  simp only [List.mem_ofFn, id]
  constructor
  · intro h i hi; exact h _ ⟨⟨i, hi⟩, rfl⟩
  · rintro h _ ⟨i, rfl⟩; exact h i i.isLt

theorem redXor_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (LVec.ofBoolFn w f).redXor = Logic.ofBool (parity w f) := by
  rw [LVec.redXor, show Logic.l0 = Logic.ofBool false from rfl,
    bits_foldl_ofBoolFn w f _ (· ^^ ·) Logic.xor_ofBool]
  rfl

theorem condTrue_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (LVec.ofBoolFn w f).condTrue = any w f := by
  rw [Bool.eq_iff_iff, any_eq_true, LVec.condTrue, Array.any_eq_true]
  simp only [LVec.ofBoolFn, Array.size_ofFn, Array.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by cases hb : f i <;> simp_all [Logic.ofBool]⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by simp [h]⟩

theorem isKnownZero_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (LVec.ofBoolFn w f).isKnownZero = all w (fun k => !f k) := by
  rw [Bool.eq_iff_iff, all_eq_true, LVec.isKnownZero, Array.all_eq_true]
  simp only [LVec.ofBoolFn, Array.size_ofFn, Array.getElem_ofFn]
  constructor
  · intro h i hi; have := h i hi; cases hb : f i <;> simp_all [Logic.ofBool]
  · intro h i hi; have := h i hi; cases hb : f i <;> simp_all [Logic.ofBool]

theorem ternary_ofBoolFn (cw w : Nat) (g f h : Nat → Bool) :
    LVec.ternary (LVec.ofBoolFn cw g) (LVec.ofBoolFn w f) (LVec.ofBoolFn w h) =
      LVec.ofBoolFn w (fun k => if any cw g then f k else h k) := by
  unfold LVec.ternary
  rw [condTrue_ofBoolFn, isKnownZero_ofBoolFn, all_not]
  by_cases hc : any cw g = true
  · simp [hc]
  · have : any cw g = false := by simpa using hc
    simp [this]

end XF

/-! ### Word-level values of a bit function

`XF.val f n = Σ_{j<n} 2^j · f j` (the unsigned value of the first `n` bits), with the facts that
connect `LVec.toNat?`, `LVec.ofNat` and `BitVec` to a bit function. They are the bridge for the
word-level operators of the fragment (`+ - *`, comparisons, shifts). -/

namespace XF

/-- Unsigned value of the first `n` bits of `f`. -/
def val (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => val f n + 2 ^ n * (f n).toNat

theorem val_lt (f : Nat → Bool) (n : Nat) : val f n < 2 ^ n := by
  induction n with
  | zero => simp [val]
  | succ n ih =>
    simp only [val, Nat.pow_succ]
    generalize 2 ^ n = P at *
    cases f n <;> simp <;> omega

theorem testBit_val (f : Nat → Bool) : ∀ (n k : Nat), k < n → (val f n).testBit k = f k
  | 0, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hk => by
    have hlt := val_lt f n
    show (val f n + 2 ^ n * (f n).toNat).testBit k = f k
    cases hb : f n
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
      by_cases hkn : k < n
      · exact testBit_val f n k hkn
      · obtain rfl : k = n := by omega
        rw [Nat.testBit_lt_two_pow hlt, hb]
    · simp only [Bool.toNat_true, Nat.mul_one]
      rw [Nat.add_comm]
      by_cases hkn : k < n
      · rw [Nat.testBit_two_pow_add_gt hkn]
        exact testBit_val f n k hkn
      · obtain rfl : k = n := by omega
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hb]
        rfl

/-- The `BitVec` of a bit function. -/
def bv (w : Nat) (f : Nat → Bool) : BitVec w := BitVec.ofNat w (val f w)

theorem getLsbD_bv {w : Nat} {f : Nat → Bool} {k : Nat} (hk : k < w) :
    (bv w f).getLsbD k = f k := by
  unfold bv
  rw [BitVec.getLsbD_ofNat]
  simp [hk, testBit_val f w k hk]

/-- `a = b` on the first `w` bits. -/
def eqv (w : Nat) (f g : Nat → Bool) : Bool := decide (∀ k, k < w → f k = g k)

theorem eqv_eq_true {w : Nat} {f g : Nat → Bool} : eqv w f g = true ↔ ∀ k, k < w → f k = g k := by
  simp [eqv]

/-- Sum of two bit functions (bit `k`), at their widths. -/
def addBits (wa : Nat) (fa : Nat → Bool) (wb : Nat) (fb : Nat → Bool) (k : Nat) : Bool :=
  (val fa wa + val fb wb).testBit k

/-- Difference (bit `k`): modulo `2^(max wa wb)`, as `LVec.sub`. -/
def subBits (wa : Nat) (fa : Nat → Bool) (wb : Nat) (fb : Nat → Bool) (k : Nat) : Bool :=
  (val fa wa + (2 ^ max wa wb - val fb wb)).testBit k

/-- Product (bit `k`). -/
def mulBits (wa : Nat) (fa : Nat → Bool) (wb : Nat) (fb : Nat → Bool) (k : Nat) : Bool :=
  (val fa wa * val fb wb).testBit k

/-- Two's-complement negation (bit `k`) at width `w`. -/
def negBits (w : Nat) (f : Nat → Bool) (k : Nat) : Bool := (2 ^ w - val f w).testBit k

/-- Left shift by the value of `g` (bit `k`). -/
def shlBits (f : Nat → Bool) (wr : Nat) (g : Nat → Bool) (k : Nat) : Bool :=
  decide (val g wr ≤ k) && f (k - val g wr)

/-- Logical right shift by the value of `g` (bit `k`), of a `w`-bit value. -/
def shrBits (w : Nat) (f : Nat → Bool) (wr : Nat) (g : Nat → Bool) (k : Nat) : Bool :=
  decide (k + val g wr < w) && f (k + val g wr)

/-- Combine two optional widths. -/
def comb (g : Nat → Nat → Nat) : Option Nat → Option Nat → Option Nat
  | some a, some b => some (g a b)
  | _, _ => none

theorem comb_eq_some {g : Nat → Nat → Nat} {a b : Option Nat} {w : Nat} :
    comb g a b = some w ↔ ∃ x y, a = some x ∧ b = some y ∧ g x y = w := by
  rcases a with _ | x <;> rcases b with _ | y <;> simp [comb]

end XF

namespace LVec

theorem ofNat_eq_ofBoolFn (w n : Nat) : LVec.ofNat w n = ofBoolFn w n.testBit := rfl

theorem ofBoolFn_eq_ofNat (w : Nat) (f : Nat → Bool) :
    ofBoolFn w f = LVec.ofNat w (XF.val f w) := by
  rw [ofNat_eq_ofBoolFn]
  exact ofBoolFn_congr (fun k hk => (XF.testBit_val f w k hk).symm)

theorem ofBoolFn_eq_ofBitVec_bv (w : Nat) (f : Nat → Bool) : ofBoolFn w f = ofBitVec (XF.bv w f) :=
  ofBoolFn_eq_ofBitVec (fun _ hk => XF.getLsbD_bv hk)

theorem allKnown_ofBoolFn (w : Nat) (f : Nat → Bool) : (ofBoolFn w f).allKnown = true := by
  rw [ofBoolFn_eq_ofNat]; exact allKnown_ofNat _ _

theorem toNat?_ofBoolFn (w : Nat) (f : Nat → Bool) : (ofBoolFn w f).toNat? = some (XF.val f w) := by
  rw [ofBoolFn_eq_ofNat, toNat?_ofNat, Nat.mod_eq_of_lt (XF.val_lt f w)]

theorem add_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).add (ofBoolFn wb fb) = ofBoolFn (max wa wb) (XF.addBits wa fa wb fb) := by
  unfold LVec.add
  rw [toNat?_ofBoolFn, toNat?_ofBoolFn]
  simp only [arithWidth, width_ofBoolFn]
  exact ofNat_eq_ofBoolFn _ _

theorem sub_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).sub (ofBoolFn wb fb) = ofBoolFn (max wa wb) (XF.subBits wa fa wb fb) := by
  unfold LVec.sub
  rw [toNat?_ofBoolFn, toNat?_ofBoolFn]
  simp only [arithWidth, width_ofBoolFn]
  exact ofNat_eq_ofBoolFn _ _

theorem mul_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).mul (ofBoolFn wb fb) = ofBoolFn (max wa wb) (XF.mulBits wa fa wb fb) := by
  unfold LVec.mul
  rw [toNat?_ofBoolFn, toNat?_ofBoolFn]
  simp only [arithWidth, width_ofBoolFn]
  exact ofNat_eq_ofBoolFn _ _

theorem neg_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (ofBoolFn w f).neg = ofBoolFn w (XF.negBits w f) := by
  unfold LVec.neg
  rw [toNat?_ofBoolFn]
  simp only [width_ofBoolFn]
  exact ofNat_eq_ofBoolFn _ _

theorem pos_ofBoolFn (w : Nat) (f : Nat → Bool) : (ofBoolFn w f).pos = ofBoolFn w f := by
  unfold LVec.pos
  rw [if_pos (allKnown_ofBoolFn w f)]

theorem lt_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).lt (ofBoolFn wb fb) = Logic.ofBool (decide (XF.val fa wa < XF.val fb wb)) := by
  simp only [LVec.lt, relOp, toNat?_ofBoolFn]; rfl

theorem le_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).le (ofBoolFn wb fb) = Logic.ofBool (decide (XF.val fa wa ≤ XF.val fb wb)) := by
  simp only [LVec.le, relOp, toNat?_ofBoolFn]; rfl

theorem gt_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).gt (ofBoolFn wb fb) = Logic.ofBool (decide (XF.val fa wa > XF.val fb wb)) := by
  simp only [LVec.gt, relOp, toNat?_ofBoolFn]; rfl

theorem ge_ofBoolFn (wa wb : Nat) (fa fb : Nat → Bool) :
    (ofBoolFn wa fa).ge (ofBoolFn wb fb) = Logic.ofBool (decide (XF.val fa wa ≥ XF.val fb wb)) := by
  simp only [LVec.ge, relOp, toNat?_ofBoolFn]; rfl

theorem eqv_iff_bv {w : Nat} (f g : Nat → Bool) : XF.bv w f = XF.bv w g ↔ XF.eqv w f g = true := by
  rw [XF.eqv_eq_true, BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h k hk
    rw [← XF.getLsbD_bv (f := f) hk, ← XF.getLsbD_bv (f := g) hk]
    exact h k hk
  · intro h k hk
    rw [XF.getLsbD_bv hk, XF.getLsbD_bv hk]
    exact h k hk

theorem eqLogical_ofBoolFn (w : Nat) (f g : Nat → Bool) :
    (ofBoolFn w f).eqLogical (ofBoolFn w g) = Logic.ofBool (XF.eqv w f g) := by
  rw [ofBoolFn_eq_ofBitVec_bv w f, ofBoolFn_eq_ofBitVec_bv w g, eqLogical_ofBitVec]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eqv_iff_bv]

theorem eqCase_ofBoolFn (w : Nat) (f g : Nat → Bool) :
    (ofBoolFn w f).eqCase (ofBoolFn w g) = Logic.ofBool (XF.eqv w f g) := by
  rw [ofBoolFn_eq_ofBitVec_bv w f, ofBoolFn_eq_ofBitVec_bv w g, eqCase_ofBitVec]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eqv_iff_bv]

theorem shl_ofBoolFn (w wr : Nat) (f g : Nat → Bool) :
    (ofBoolFn w f).shl (ofBoolFn wr g) = ofBoolFn w (XF.shlBits f wr g) := by
  have hb : XF.shlBits f wr g = fun k => decide (XF.val g wr ≤ k) && f (k - XF.val g wr) := rfl
  rw [hb]
  unfold LVec.shl
  simp only [shiftAmount?, toNat?_ofBoolFn]
  generalize XF.val g wr = A
  apply ext_getElem?
  intro i
  simp only [Array.getElem?_ofFn, getElem?_ofBoolFn, width_ofBoolFn]
  by_cases hi : i < w
  · by_cases ha : i < A
    · have h1 : ¬ A ≤ i := by omega
      simp [hi, ha, h1, Logic.ofBool]
    · have h1 : A ≤ i := by omega
      have h2 : i - A < w := by omega
      simp [hi, ha, h1, h2]
  · simp [hi]

theorem shr_ofBoolFn (w wr : Nat) (f g : Nat → Bool) :
    (ofBoolFn w f).shr (ofBoolFn wr g) = ofBoolFn w (XF.shrBits w f wr g) := by
  have hb : XF.shrBits w f wr g = fun k => decide (k + XF.val g wr < w) && f (k + XF.val g wr) :=
    rfl
  rw [hb]
  unfold LVec.shr
  simp only [shiftAmount?, toNat?_ofBoolFn]
  generalize XF.val g wr = A
  apply ext_getElem?
  intro i
  simp only [Array.getElem?_ofFn, getElem?_ofBoolFn, width_ofBoolFn]
  by_cases hi : i < w
  · by_cases ha : i + A < w
    · simp [hi, ha]
    · simp [hi, ha, Logic.ofBool]
  · simp [hi]

private theorem getElem?_flatten_replicate' {α : Type} (l : List α) (n i : Nat) :
    ((List.replicate n l).flatten)[i]? =
      if i < l.length * n then l[i % l.length]? else none := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.getElem?_append, ih]
      by_cases h1 : i < l.length
      · simp [h1, Nat.mod_eq_of_lt h1, Nat.mul_succ, show i < l.length * n + l.length by omega]
      · rw [if_neg h1, Nat.mul_succ]
        have hm : (i - l.length) % l.length = i % l.length :=
          (Nat.mod_eq_sub_mod (by omega)).symm
        rw [hm]
        by_cases h2 : i < l.length * n + l.length
        · rw [if_pos (by omega), if_pos h2]
        · rw [if_neg (by omega), if_neg h2]

theorem replVec_ofBoolFn (n w : Nat) (f : Nat → Bool) :
    replVec n (ofBoolFn w f) = ofBoolFn (w * n) (fun k => f (k % w)) := by
  apply ext_getElem?
  intro i
  rw [getElem?_ofBoolFn, replVec, ← Array.getElem?_toList, Array.toList_flatten,
    Array.toList_replicate, List.map_replicate, getElem?_flatten_replicate',
    Array.getElem?_toList, Array.length_toList]
  have hs : (ofBoolFn w f).bits.size = w := width_ofBoolFn w f
  rw [hs, getElem?_ofBoolFn]
  by_cases hi : i < w * n
  · have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    simp [hi, Nat.mod_lt i hw]
  · simp [hi]

end LVec

/-! ## The fragment: static widths and the Boolean evaluator -/

namespace XF

/-- Two optional widths that agree (the operands of a bitwise operator). -/
def same : Option Nat → Option Nat → Option Nat
  | some a, some b => if a = b then some a else none
  | _, _ => none

theorem same_eq_some {a b : Option Nat} {w : Nat} :
    same a b = some w ↔ a = some w ∧ b = some w := by
  rcases a with _ | x <;> rcases b with _ | y
  · simp [same]
  · simp [same]
  · simp [same]
  · show (if x = y then some x else none) = some w ↔ _
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [if_neg hxy]
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2⟩
        injection h1 with h1
        injection h2 with h2
        exact absurd (h1.trans h2.symm) hxy

end XF

mutual

/-- **The x-free fragment, with static widths.** `e.xfWidth d = some w` says that `e` is in the
fragment of the x-free knownness theorem, over the declarations of `d`, and is `w` bits wide.
Covered forms: known literals; identifiers (their declared width); `~`, `!`; `& | ^` of two
operands of the same width; `&&`, `||`; reductions; `?:` with a condition of any width and arms
of the same width; concatenation; constant in-range non-empty slices; `resize` (zero-extend or
truncate). Everything else is `none` (see `LeanModels.Sv.CombKnownThm` for why). -/
def Expr2.xfWidth (d : Design2) : Expr2 → Option Nat
  | .lit v => if v.knownB then some v.width else none
  | .ident n => d.declWidth n
  | .unary .bnot a => a.xfWidth d
  | .unary .lnot a => (a.xfWidth d).map fun _ => 1
  | .unary .neg a => a.xfWidth d
  | .unary .pos a => a.xfWidth d
  | .binary .and l r => XF.same (l.xfWidth d) (r.xfWidth d)
  | .binary .or l r => XF.same (l.xfWidth d) (r.xfWidth d)
  | .binary .xor l r => XF.same (l.xfWidth d) (r.xfWidth d)
  | .binary .add l r => XF.comb max (l.xfWidth d) (r.xfWidth d)
  | .binary .sub l r => XF.comb max (l.xfWidth d) (r.xfWidth d)
  | .binary .mul l r => XF.comb max (l.xfWidth d) (r.xfWidth d)
  | .binary .eq l r => (XF.same (l.xfWidth d) (r.xfWidth d)).map fun _ => 1
  | .binary .ne l r => (XF.same (l.xfWidth d) (r.xfWidth d)).map fun _ => 1
  | .binary .caseEq l r => (XF.same (l.xfWidth d) (r.xfWidth d)).map fun _ => 1
  | .binary .caseNe l r => (XF.same (l.xfWidth d) (r.xfWidth d)).map fun _ => 1
  | .binary .lt l r => XF.comb (fun _ _ => 1) (l.xfWidth d) (r.xfWidth d)
  | .binary .le l r => XF.comb (fun _ _ => 1) (l.xfWidth d) (r.xfWidth d)
  | .binary .gt l r => XF.comb (fun _ _ => 1) (l.xfWidth d) (r.xfWidth d)
  | .binary .ge l r => XF.comb (fun _ _ => 1) (l.xfWidth d) (r.xfWidth d)
  | .binary (.shl _) l r => XF.comb (fun a _ => a) (l.xfWidth d) (r.xfWidth d)
  | .binary (.shr _) l r => XF.comb (fun a _ => a) (l.xfWidth d) (r.xfWidth d)
  | .binary (.ashl _) l r => XF.comb (fun a _ => a) (l.xfWidth d) (r.xfWidth d)
  | .binary (.ashr false) l r => XF.comb (fun a _ => a) (l.xfWidth d) (r.xfWidth d)
  | .binary _ _ _ => none
  | .logical _ l r =>
      match l.xfWidth d, r.xfWidth d with
      | some _, some _ => some 1
      | _, _ => none
  | .ternary c t f =>
      match c.xfWidth d with
      | some _ => XF.same (t.xfWidth d) (f.xfWidth d)
      | none => none
  | .concat parts => Expr2.xfWidthSum d parts.toList
  | .slice b lo w =>
      match b.xfWidth d with
      | some bw => if lo + w ≤ bw ∧ 0 < w then some w else none
      | none => none
  | .reduce _ a => (a.xfWidth d).map fun _ => 1
  | .resize w a => (a.xfWidth d).map fun _ => w
  | .resizeSigned _ _ => none
  | .squash2 _ => none
  | .scmp _ _ _ => none
  | .index _ _ _ => none
  | .repl n a => (a.xfWidth d).map fun w => w * n
  | .unsupported _ _ => none
termination_by structural e => e

/-- Total static width of a part list (`none` if some part is out of the fragment). -/
def Expr2.xfWidthSum (d : Design2) : List Expr2 → Option Nat
  | [] => some 0
  | e :: es =>
      match e.xfWidth d, Expr2.xfWidthSum d es with
      | some a, some b => some (a + b)
      | _, _ => none
termination_by structural es => es

end

mutual

/-- **The Boolean evaluator.** For `e` in the fragment (`e.xfWidth d = some w`) and `env n k` the
Boolean value of bit `k` of signal `n`, `e.xfBits d env k` is the Boolean value of bit `k` of the
value of `e`, for `k < w` (past `w` it is junk; use `Expr2.xfBitsZ` for the zero-extended read).
One equation per constructor, all by `rfl` (`Expr2.xfBits_*`). -/
def Expr2.xfBits (d : Design2) (env : String → Nat → Bool) : Expr2 → Nat → Bool
  | .lit v => fun k => v.boolAt k
  | .ident n => env n
  | .unary .bnot a => fun k => !(a.xfBits d env k)
  | .unary .lnot a => fun _ => !(XF.any ((a.xfWidth d).getD 0) (a.xfBits d env))
  | .unary .neg a => XF.negBits ((a.xfWidth d).getD 0) (a.xfBits d env)
  | .unary .pos a => a.xfBits d env
  | .binary .and l r => fun k => l.xfBits d env k && r.xfBits d env k
  | .binary .or l r => fun k => l.xfBits d env k || r.xfBits d env k
  | .binary .xor l r => fun k => l.xfBits d env k ^^ r.xfBits d env k
  | .binary .add l r =>
      XF.addBits ((l.xfWidth d).getD 0) (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary .sub l r =>
      XF.subBits ((l.xfWidth d).getD 0) (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary .mul l r =>
      XF.mulBits ((l.xfWidth d).getD 0) (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary .eq l r => fun _ => XF.eqv ((l.xfWidth d).getD 0) (l.xfBits d env) (r.xfBits d env)
  | .binary .ne l r => fun _ => !XF.eqv ((l.xfWidth d).getD 0) (l.xfBits d env) (r.xfBits d env)
  | .binary .caseEq l r =>
      fun _ => XF.eqv ((l.xfWidth d).getD 0) (l.xfBits d env) (r.xfBits d env)
  | .binary .caseNe l r =>
      fun _ => !XF.eqv ((l.xfWidth d).getD 0) (l.xfBits d env) (r.xfBits d env)
  | .binary .lt l r => fun _ =>
      decide (XF.val (l.xfBits d env) ((l.xfWidth d).getD 0) <
        XF.val (r.xfBits d env) ((r.xfWidth d).getD 0))
  | .binary .le l r => fun _ =>
      decide (XF.val (l.xfBits d env) ((l.xfWidth d).getD 0) ≤
        XF.val (r.xfBits d env) ((r.xfWidth d).getD 0))
  | .binary .gt l r => fun _ =>
      decide (XF.val (l.xfBits d env) ((l.xfWidth d).getD 0) >
        XF.val (r.xfBits d env) ((r.xfWidth d).getD 0))
  | .binary .ge l r => fun _ =>
      decide (XF.val (l.xfBits d env) ((l.xfWidth d).getD 0) ≥
        XF.val (r.xfBits d env) ((r.xfWidth d).getD 0))
  | .binary (.shl _) l r =>
      XF.shlBits (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary (.shr _) l r =>
      XF.shrBits ((l.xfWidth d).getD 0) (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary (.ashl _) l r =>
      XF.shlBits (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary (.ashr false) l r =>
      XF.shrBits ((l.xfWidth d).getD 0) (l.xfBits d env) ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .binary _ _ _ => fun _ => false
  | .logical isAnd l r => fun _ =>
      if isAnd then
        XF.any ((l.xfWidth d).getD 0) (l.xfBits d env) &&
          XF.any ((r.xfWidth d).getD 0) (r.xfBits d env)
      else
        XF.any ((l.xfWidth d).getD 0) (l.xfBits d env) ||
          XF.any ((r.xfWidth d).getD 0) (r.xfBits d env)
  | .ternary c t f => fun k =>
      if XF.any ((c.xfWidth d).getD 0) (c.xfBits d env) then t.xfBits d env k
      else f.xfBits d env k
  | .concat parts => Expr2.catBits d env parts.toList
  | .slice b lo _ => fun k => b.xfBits d env (lo + k)
  | .reduce op a => fun _ => XF.red op ((a.xfWidth d).getD 0) (a.xfBits d env)
  | .resize _ a => fun k => decide (k < (a.xfWidth d).getD 0) && a.xfBits d env k
  | .resizeSigned _ _ => fun _ => false
  | .squash2 _ => fun _ => false
  | .scmp _ _ _ => fun _ => false
  | .index _ _ _ => fun _ => false
  | .repl _ a => fun k => a.xfBits d env (k % (a.xfWidth d).getD 0)
  | .unsupported _ _ => fun _ => false
termination_by structural e => e

/-- Bit function of a concatenation (parts in source order, the first part most significant). -/
def Expr2.catBits (d : Design2) (env : String → Nat → Bool) : List Expr2 → Nat → Bool
  | [] => fun _ => false
  | p :: ps => fun k =>
      if k < (Expr2.xfWidthSum d ps).getD 0 then Expr2.catBits d env ps k
      else p.xfBits d env (k - (Expr2.xfWidthSum d ps).getD 0)
termination_by structural es => es

end

/-- The zero-extended read of an expression's bit function (what a wider target sees:
`LVec.resizeU` pads with `0`). -/
def Expr2.xfBitsZ (d : Design2) (env : String → Nat → Bool) (e : Expr2) (j : Nat) : Bool :=
  decide (j < (e.xfWidth d).getD 0) && e.xfBits d env j

theorem Expr2.xfBitsZ_of_lt {d : Design2} {env : String → Nat → Bool} {e : Expr2} {w j : Nat}
    (hw : e.xfWidth d = some w) (hj : j < w) : e.xfBitsZ d env j = e.xfBits d env j := by
  simp [Expr2.xfBitsZ, hw, hj]

/-! ## Knownness predicates -/

/-- Bit `k` of signal `n` exists in `st` and is a definite `0`/`1`. -/
def KnownBit (st : SvState) (n : String) (k : Nat) : Prop :=
  ∃ v, SvState.lookup st n = some v ∧ ∃ b, v.bits[k]? = some b ∧ b.isKnown = true

/-- Bits `lo, …, lo + w - 1` of `n` are known. -/
def WinKnown (st : SvState) (n : String) (lo w : Nat) : Prop :=
  ∀ k, k < w → KnownBit st n (lo + k)

/-- `n` is bound at its declared width and fully known. -/
def WholeKnown (d : Design2) (st : SvState) (n : String) : Prop :=
  ∃ W v, d.declWidth n = some W ∧ SvState.lookup st n = some v ∧ v.width = W ∧
    v.allKnown = true

/-- What an expression's read set must satisfy in `st` for the fragment to evaluate to a known
value. -/
def ReadKnown (d : Design2) (st : SvState) : ReadWin → Prop
  | .whole n => WholeKnown d st n
  | .win n lo w => WinKnown st n lo w

/-! ## Structural facts -/

theorem Expr2.reads_slice_of_not_ident {b : Expr2} (hb : ∀ n, b ≠ .ident n) (lo w : Nat) :
    (Expr2.slice b lo w).reads = b.reads := by
  cases b <;> simp_all [Expr2.reads, Expr2.sliceReads]

theorem mem_listReads {ps : List Expr2} {p : Expr2} (hp : p ∈ ps) {r : ReadWin}
    (hr : r ∈ p.reads) : r ∈ Expr2.listReads ps := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
      simp only [Expr2.listReads, List.mem_append]
      rcases List.mem_cons.mp hp with rfl | h
      · exact Or.inl hr
      · exact Or.inr (ih h)

theorem xfWidthSum_cons_eq_some {d : Design2} {p : Expr2} {ps : List Expr2} {W : Nat}
    (h : Expr2.xfWidthSum d (p :: ps) = some W) :
    ∃ a b, p.xfWidth d = some a ∧ Expr2.xfWidthSum d ps = some b ∧ W = a + b := by
  simp only [Expr2.xfWidthSum] at h
  rcases hp : p.xfWidth d with _ | a <;> rcases hq : Expr2.xfWidthSum d ps with _ | b <;>
    simp [hp, hq] at h
  exact ⟨a, b, rfl, rfl, h.symm⟩

theorem xfWidthSum_mem {d : Design2} :
    ∀ {ps : List Expr2} {W : Nat}, Expr2.xfWidthSum d ps = some W →
      ∀ {p : Expr2}, p ∈ ps → ∃ a, p.xfWidth d = some a
  | [], _, _, _, hp => absurd hp List.not_mem_nil
  | q :: qs, W, h, p, hp => by
      obtain ⟨a, b, hq, hqs, -⟩ := xfWidthSum_cons_eq_some h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨a, hq⟩
      · exact xfWidthSum_mem hqs hp'

/-! ## Compositional forms: `evalPure2` of the fragment's nodes -/

section Compose

variable {st : SvState}

theorem eval_unary {op : UnaryOp} {a : Expr2} {v : LVec} (h : evalPure2 st a = .ok v) :
    evalPure2 st (.unary op a) = .ok (evalUnaryOp op v) := by
  simp only [evalPure2_unary, h, Pure2.res_ok_bind, Pure2.res_pure_eq]

theorem eval_binary {op : BinOp} {l r : Expr2} {a b : LVec} (hl : evalPure2 st l = .ok a)
    (hr : evalPure2 st r = .ok b) : evalPure2 st (.binary op l r) = .ok (evalBinOp op a b) := by
  simp only [evalPure2_binary, hl, hr, Pure2.res_ok_bind, Pure2.res_pure_eq]

theorem evals_bnot {a : Expr2} {w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.unary .bnot a) = .ok (LVec.ofBoolFn w (fun k => !f k)) := by
  rw [eval_unary h]
  exact congrArg Res.ok (LVec.not_ofBoolFn w f)

theorem lnot_ofBoolFn (w : Nat) (f : Nat → Bool) :
    (LVec.ofBoolFn w f).lnot = Logic.ofBool (!XF.any w f) := by
  unfold LVec.lnot
  rw [XF.condTrue_ofBoolFn, XF.isKnownZero_ofBoolFn, XF.all_not]
  cases hc : XF.any w f <;> simp [Logic.ofBool]

theorem evals_lnot {a : Expr2} {w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.unary .lnot a) = .ok (LVec.ofBoolFn 1 (fun _ => !XF.any w f)) := by
  rw [eval_unary h]
  show Res.ok (LVec.ofLogic (LVec.ofBoolFn w f).lnot) = _
  rw [lnot_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_zip {op : BinOp} {l r : Expr2} {w : Nat} {fl fr : Nat → Bool}
    (g : Logic → Logic → Logic) (h : Bool → Bool → Bool)
    (hg : ∀ a b, g (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (h a b))
    (hop : ∀ a b, evalBinOp op a b = LVec.zipWith g a b)
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn w fr)) :
    evalPure2 st (.binary op l r) = .ok (LVec.ofBoolFn w (fun k => h (fl k) (fr k))) := by
  rw [eval_binary hl hr, hop]
  exact congrArg Res.ok (LVec.zipWith_ofBoolFn w g h hg fl fr)

theorem eval_logical {isAnd : Bool} {l r : Expr2} {a b : LVec} (hl : evalPure2 st l = .ok a)
    (hr : evalPure2 st r = .ok b) :
    evalPure2 st (.logical isAnd l r) = .ok (LVec.ofLogic (
      if isAnd then
        (if a.isKnownZero || b.isKnownZero then Logic.l0
         else if a.condTrue && b.condTrue then Logic.l1 else Logic.lx)
      else
        (if a.condTrue || b.condTrue then Logic.l1
         else if a.isKnownZero && b.isKnownZero then Logic.l0 else Logic.lx))) := by
  simp only [evalPure2_logical, hl, hr, Pure2.res_ok_bind, Pure2.res_pure_eq]

theorem LVec.ofLogic_l0_eq : LVec.ofLogic Logic.l0 = LVec.ofBoolFn 1 (fun _ => false) :=
  LVec.ofLogic_ofBool_eq false

theorem LVec.ofLogic_l1_eq : LVec.ofLogic Logic.l1 = LVec.ofBoolFn 1 (fun _ => true) :=
  LVec.ofLogic_ofBool_eq true

theorem evals_logical {isAnd : Bool} {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.logical isAnd l r) = .ok (LVec.ofBoolFn 1 (fun _ =>
      if isAnd then XF.any wl fl && XF.any wr fr else XF.any wl fl || XF.any wr fr)) := by
  rw [eval_logical hl hr, XF.condTrue_ofBoolFn, XF.condTrue_ofBoolFn, XF.isKnownZero_ofBoolFn,
    XF.isKnownZero_ofBoolFn, XF.all_not, XF.all_not]
  cases isAnd <;> cases hA : XF.any wl fl <;> cases hB : XF.any wr fr <;>
    simp [-LVec.ofLogic_l0, -LVec.ofLogic_l1, LVec.ofLogic_l0_eq, LVec.ofLogic_l1_eq]

theorem evalRedOp_ofBoolFn (op : RedOp) (w : Nat) (f : Nat → Bool) :
    evalRedOp op (LVec.ofBoolFn w f) = Logic.ofBool (XF.red op w f) := by
  cases op
  · exact XF.redOr_ofBoolFn w f
  · exact XF.redAnd_ofBoolFn w f
  · exact XF.redXor_ofBoolFn w f
  · show (LVec.ofBoolFn w f).redOr.not = _
    rw [XF.redOr_ofBoolFn, Logic.not_ofBool]; rfl
  · show (LVec.ofBoolFn w f).redAnd.not = _
    rw [XF.redAnd_ofBoolFn, Logic.not_ofBool]; rfl
  · show (LVec.ofBoolFn w f).redXor.not = _
    rw [XF.redXor_ofBoolFn, Logic.not_ofBool]; rfl

theorem evals_reduce {op : RedOp} {a : Expr2} {w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.reduce op a) = .ok (LVec.ofBoolFn 1 (fun _ => XF.red op w f)) := by
  simp only [evalPure2_reduce, h, Pure2.res_ok_bind, Pure2.res_pure_eq, evalRedOp_ofBoolFn,
    LVec.ofLogic_ofBool_eq]

theorem evals_ternary {c t e : Expr2} {cw w : Nat} {g f h : Nat → Bool}
    (hc : evalPure2 st c = .ok (LVec.ofBoolFn cw g))
    (ht : evalPure2 st t = .ok (LVec.ofBoolFn w f))
    (he : evalPure2 st e = .ok (LVec.ofBoolFn w h)) :
    evalPure2 st (.ternary c t e) =
      .ok (LVec.ofBoolFn w (fun k => if XF.any cw g then f k else h k)) := by
  simp only [evalPure2_ternary, hc, ht, he, Pure2.res_ok_bind, Pure2.res_pure_eq,
    XF.ternary_ofBoolFn]

theorem evals_slice {a : Expr2} {bw lo w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn bw f)) (hlo : lo + w ≤ bw) :
    evalPure2 st (.slice a lo w) = .ok (LVec.ofBoolFn w (fun k => f (lo + k))) := by
  simp only [evalPure2_slice, h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    LVec.extract_ofBoolFn f hlo]

theorem evals_resize {a : Expr2} {w' w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.resize w' a) = .ok (LVec.ofBoolFn w' (fun k => decide (k < w) && f k)) := by
  simp only [evalPure2_resize, h, Pure2.res_ok_bind, Pure2.res_pure_eq, LVec.resizeU_ofBoolFn]

/-- A window of a signal whose bits are known (the rest of the signal may be unknown). -/
theorem evals_slice_ident {n : String} {lo w : Nat} {v : LVec}
    (hv : SvState.lookup st n = some v)
    (hk : ∀ k, k < w → ∃ b, v.bits[lo + k]? = some b ∧ b.isKnown = true) :
    evalPure2 st (.slice (.ident n) lo w) =
      .ok (LVec.ofBoolFn w (fun k => SvState.boolAt st n (lo + k))) := by
  have hf : (fun k => v.boolAt (lo + k)) = fun k => SvState.boolAt st n (lo + k) := by
    funext k; simp [SvState.boolAt, hv]
  simp only [evalPure2_slice, evalPure2_ident_of_lookup hv, Pure2.res_ok_bind,
    Pure2.res_pure_eq, LVec.extract_eq_ofBoolFn_of_known hk, hf]

theorem evals_neg {a : Expr2} {w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.unary .neg a) = .ok (LVec.ofBoolFn w (XF.negBits w f)) := by
  rw [eval_unary h]
  exact congrArg Res.ok (LVec.neg_ofBoolFn w f)

theorem evals_pos {a : Expr2} {w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.unary .pos a) = .ok (LVec.ofBoolFn w f) := by
  rw [eval_unary h]
  exact congrArg Res.ok (LVec.pos_ofBoolFn w f)

theorem evals_add {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .add l r) = .ok (LVec.ofBoolFn (max wl wr) (XF.addBits wl fl wr fr)) := by
  rw [eval_binary hl hr]
  exact congrArg Res.ok (LVec.add_ofBoolFn wl wr fl fr)

theorem evals_sub {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .sub l r) = .ok (LVec.ofBoolFn (max wl wr) (XF.subBits wl fl wr fr)) := by
  rw [eval_binary hl hr]
  exact congrArg Res.ok (LVec.sub_ofBoolFn wl wr fl fr)

theorem evals_mul {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .mul l r) = .ok (LVec.ofBoolFn (max wl wr) (XF.mulBits wl fl wr fr)) := by
  rw [eval_binary hl hr]
  exact congrArg Res.ok (LVec.mul_ofBoolFn wl wr fl fr)

theorem evals_eq {l r : Expr2} {w : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn w fr)) :
    evalPure2 st (.binary .eq l r) = .ok (LVec.ofBoolFn 1 (fun _ => XF.eqv w fl fr)) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn w fl).eqLogical (LVec.ofBoolFn w fr))) = _
  rw [LVec.eqLogical_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_ne {l r : Expr2} {w : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn w fr)) :
    evalPure2 st (.binary .ne l r) = .ok (LVec.ofBoolFn 1 (fun _ => !XF.eqv w fl fr)) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn w fl).eqLogical (LVec.ofBoolFn w fr)).not) = _
  rw [LVec.eqLogical_ofBoolFn, Logic.not_ofBool, LVec.ofLogic_ofBool_eq]

theorem evals_caseEq {l r : Expr2} {w : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn w fr)) :
    evalPure2 st (.binary .caseEq l r) = .ok (LVec.ofBoolFn 1 (fun _ => XF.eqv w fl fr)) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn w fl).eqCase (LVec.ofBoolFn w fr))) = _
  rw [LVec.eqCase_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_caseNe {l r : Expr2} {w : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn w fr)) :
    evalPure2 st (.binary .caseNe l r) = .ok (LVec.ofBoolFn 1 (fun _ => !XF.eqv w fl fr)) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn w fl).eqCase (LVec.ofBoolFn w fr)).not) = _
  rw [LVec.eqCase_ofBoolFn, Logic.not_ofBool, LVec.ofLogic_ofBool_eq]

theorem evals_lt {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .lt l r) =
      .ok (LVec.ofBoolFn 1 (fun _ => decide (XF.val fl wl < XF.val fr wr))) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn wl fl).lt (LVec.ofBoolFn wr fr))) = _
  rw [LVec.lt_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_le {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .le l r) =
      .ok (LVec.ofBoolFn 1 (fun _ => decide (XF.val fl wl ≤ XF.val fr wr))) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn wl fl).le (LVec.ofBoolFn wr fr))) = _
  rw [LVec.le_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_gt {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .gt l r) =
      .ok (LVec.ofBoolFn 1 (fun _ => decide (XF.val fl wl > XF.val fr wr))) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn wl fl).gt (LVec.ofBoolFn wr fr))) = _
  rw [LVec.gt_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_ge {l r : Expr2} {wl wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn wl fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary .ge l r) =
      .ok (LVec.ofBoolFn 1 (fun _ => decide (XF.val fl wl ≥ XF.val fr wr))) := by
  rw [eval_binary hl hr]
  show Res.ok (LVec.ofLogic ((LVec.ofBoolFn wl fl).ge (LVec.ofBoolFn wr fr))) = _
  rw [LVec.ge_ofBoolFn, LVec.ofLogic_ofBool_eq]

theorem evals_shl {s : Bool} {l r : Expr2} {w wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary (.shl s) l r) = .ok (LVec.ofBoolFn w (XF.shlBits fl wr fr)) := by
  rw [eval_binary hl hr]
  exact congrArg Res.ok (LVec.shl_ofBoolFn w wr fl fr)

theorem evals_ashl {s : Bool} {l r : Expr2} {w wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary (.ashl s) l r) = .ok (LVec.ofBoolFn w (XF.shlBits fl wr fr)) := by
  rw [eval_binary hl hr]
  exact congrArg Res.ok (LVec.shl_ofBoolFn w wr fl fr)

theorem evals_shr {s : Bool} {l r : Expr2} {w wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary (.shr s) l r) = .ok (LVec.ofBoolFn w (XF.shrBits w fl wr fr)) := by
  rw [eval_binary hl hr]
  exact congrArg Res.ok (LVec.shr_ofBoolFn w wr fl fr)

theorem LVec.ashr_false_eq_shr (a b : LVec) : a.ashr false b = a.shr b := by
  unfold LVec.ashr LVec.shr
  cases LVec.shiftAmount? b <;> rfl

theorem evals_ashr {l r : Expr2} {w wr : Nat} {fl fr : Nat → Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBoolFn w fl))
    (hr : evalPure2 st r = .ok (LVec.ofBoolFn wr fr)) :
    evalPure2 st (.binary (.ashr false) l r) = .ok (LVec.ofBoolFn w (XF.shrBits w fl wr fr)) := by
  rw [eval_binary hl hr]
  show Res.ok ((LVec.ofBoolFn w fl).ashr false (LVec.ofBoolFn wr fr)) = _
  rw [LVec.ashr_false_eq_shr]
  exact congrArg Res.ok (LVec.shr_ofBoolFn w wr fl fr)

theorem evals_repl {n : Nat} {a : Expr2} {w : Nat} {f : Nat → Bool}
    (h : evalPure2 st a = .ok (LVec.ofBoolFn w f)) :
    evalPure2 st (.repl n a) = .ok (LVec.ofBoolFn (w * n) (fun k => f (k % w))) := by
  simp only [evalPure2_repl, h, Pure2.res_ok_bind, Pure2.res_pure_eq, LVec.replVec_ofBoolFn]

theorem concatMany_map_ofBoolFn (d : Design2) (env : String → Nat → Bool) :
    ∀ (ps : List Expr2) (W : Nat), Expr2.xfWidthSum d ps = some W →
      LVec.concatMany (ps.map fun p =>
        LVec.ofBoolFn ((p.xfWidth d).getD 0) (p.xfBits d env)).toArray =
          LVec.ofBoolFn W (Expr2.catBits d env ps)
  | [], W, h => by
      simp only [Expr2.xfWidthSum, Option.some.injEq] at h
      subst h
      simp [LVec.ofBoolFn]
  | p :: ps, W, h => by
      obtain ⟨a, b, hp, hps, rfl⟩ := xfWidthSum_cons_eq_some h
      rw [List.map_cons, LVec.concatMany_cons, concatMany_map_ofBoolFn d env ps b hps,
        LVec.concat_ofBoolFn, Nat.add_comm a b]
      simp only [Expr2.catBits, hps, hp, Option.getD_some]

/-! ## The expression theorem -/

/-- **Expression-level knownness and Boolean semantics.** An expression in the x-free fragment,
all of whose reads are known in `st`, evaluates to the known vector whose bits are the Boolean
bit function `e.xfBits d (SvState.boolAt st)`. (The size bound `e.size < n` is only the fuel of
the induction; instantiate with `n = e.size + 1`.) -/
theorem Expr2.evalPure2_ofBoolFn {d : Design2} {st : SvState} (n : Nat) :
    ∀ e : Expr2, e.size < n → ∀ {w : Nat}, e.xfWidth d = some w →
      (∀ r ∈ e.reads, ReadKnown d st r) →
      evalPure2 st e = .ok (LVec.ofBoolFn w (e.xfBits d (SvState.boolAt st))) := by
  induction n with
  | zero => intro e h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro e hs w hw hr
    cases e with
    | resizeSigned width arg => simp [Expr2.xfWidth] at hw
    | squash2 arg => simp [Expr2.xfWidth] at hw
    | scmp op l r => simp [Expr2.xfWidth] at hw
    | index b i elemW => simp [Expr2.xfWidth] at hw
    | unsupported k t => simp [Expr2.xfWidth] at hw
    | lit v =>
        simp only [Expr2.xfWidth] at hw
        split at hw
        · rename_i hk
          injection hw with hw
          subst hw
          rw [LVec.knownB_eq_allKnown] at hk
          exact congrArg Res.ok (LVec.eq_ofBoolFn_of_allKnown hk)
        · exact absurd hw (by simp)
    | ident name =>
        obtain ⟨W, v, hW, hv, hvw, hk⟩ := hr (.whole name) (by simp [Expr2.reads])
        simp only [Expr2.xfWidth, hW] at hw
        injection hw with hw
        subst hw
        rw [evalPure2_ident_of_lookup hv]
        have h1 := LVec.eq_ofBoolFn_of_allKnown hk
        refine congrArg Res.ok (h1.trans ?_)
        rw [hvw]
        exact LVec.ofBoolFn_congr (fun k _ => by
          show v.boolAt k = SvState.boolAt st name k
          simp [SvState.boolAt, hv])
    | unary op a =>
        have hsa : a.size < n := by simp only [Expr2.size] at hs; omega
        have hra : ∀ r ∈ a.reads, ReadKnown d st r := fun r h' => hr r (by simpa [Expr2.reads] using h')
        cases op with
        | bnot =>
            simp only [Expr2.xfWidth] at hw
            exact evals_bnot (ih a hsa hw hra)
        | lnot =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨aw, haw, rfl⟩ := Option.map_eq_some_iff.mp hw
            have := evals_lnot (ih a hsa haw hra)
            simp only [Expr2.xfBits, haw, Option.getD_some]
            exact this
        | neg =>
            simp only [Expr2.xfWidth] at hw
            have := evals_neg (ih a hsa hw hra)
            simp only [Expr2.xfBits, hw, Option.getD_some]
            exact this
        | pos =>
            simp only [Expr2.xfWidth] at hw
            have := evals_pos (ih a hsa hw hra)
            simp only [Expr2.xfBits]
            exact this
    | binary op l r =>
        have hsl : l.size < n := by simp only [Expr2.size] at hs; omega
        have hsr : r.size < n := by simp only [Expr2.size] at hs; omega
        have hrl : ∀ x ∈ l.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        have hrr : ∀ x ∈ r.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        cases op with
        | and =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hw
            exact evals_zip (op := .and) Logic.and (· && ·) Logic.and_ofBool (fun _ _ => rfl)
              (ih l hsl hwl hrl) (ih r hsr hwr hrr)
        | or =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hw
            exact evals_zip (op := .or) Logic.or (· || ·) Logic.or_ofBool (fun _ _ => rfl)
              (ih l hsl hwl hrl) (ih r hsr hwr hrr)
        | xor =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hw
            exact evals_zip (op := .xor) Logic.xor (· ^^ ·) Logic.xor_ofBool (fun _ _ => rfl)
              (ih l hsl hwl hrl) (ih r hsr hwr hrr)
        | add =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_add (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | sub =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_sub (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | mul =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_mul (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | eq =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨sw, hsw, rfl⟩ := Option.map_eq_some_iff.mp hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hsw
            have := evals_eq (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, Option.getD_some]
            exact this
        | ne =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨sw, hsw, rfl⟩ := Option.map_eq_some_iff.mp hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hsw
            have := evals_ne (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, Option.getD_some]
            exact this
        | caseEq =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨sw, hsw, rfl⟩ := Option.map_eq_some_iff.mp hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hsw
            have := evals_caseEq (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, Option.getD_some]
            exact this
        | caseNe =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨sw, hsw, rfl⟩ := Option.map_eq_some_iff.mp hw
            obtain ⟨hwl, hwr⟩ := XF.same_eq_some.mp hsw
            have := evals_caseNe (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, Option.getD_some]
            exact this
        | lt =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_lt (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | le =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_le (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | gt =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_gt (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | ge =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_ge (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | shl s =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_shl (s := s) (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwr, Option.getD_some]
            exact this
        | shr s =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_shr (s := s) (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
            exact this
        | ashl s =>
            simp only [Expr2.xfWidth] at hw
            obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
            have := evals_ashl (s := s) (ih l hsl hwl hrl) (ih r hsr hwr hrr)
            simp only [Expr2.xfBits, hwr, Option.getD_some]
            exact this
        | ashr s =>
            cases s with
            | true => simp [Expr2.xfWidth] at hw
            | false =>
                simp only [Expr2.xfWidth] at hw
                obtain ⟨wl, wr, hwl, hwr, rfl⟩ := XF.comb_eq_some.mp hw
                have := evals_ashr (ih l hsl hwl hrl) (ih r hsr hwr hrr)
                simp only [Expr2.xfBits, hwl, hwr, Option.getD_some]
                exact this
        | _ => simp [Expr2.xfWidth] at hw
    | logical isAnd l r =>
        have hsl : l.size < n := by simp only [Expr2.size] at hs; omega
        have hsr : r.size < n := by simp only [Expr2.size] at hs; omega
        have hrl : ∀ x ∈ l.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        have hrr : ∀ x ∈ r.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        simp only [Expr2.xfWidth] at hw
        rcases hl : l.xfWidth d with _ | lw <;> rcases hr' : r.xfWidth d with _ | rw' <;>
          simp [hl, hr'] at hw
        subst hw
        have := evals_logical (isAnd := isAnd) (ih l hsl hl hrl) (ih r hsr hr' hrr)
        simp only [Expr2.xfBits, hl, hr', Option.getD_some]
        exact this
    | ternary c t f =>
        have hsc : c.size < n := by simp only [Expr2.size] at hs; omega
        have hst : t.size < n := by simp only [Expr2.size] at hs; omega
        have hsf : f.size < n := by simp only [Expr2.size] at hs; omega
        have hrc : ∀ x ∈ c.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        have hrt : ∀ x ∈ t.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        have hrf : ∀ x ∈ f.reads, ReadKnown d st x := fun x h' => hr x (by simp [Expr2.reads, h'])
        simp only [Expr2.xfWidth] at hw
        rcases hc : c.xfWidth d with _ | cw
        · simp [hc] at hw
        · simp only [hc] at hw
          obtain ⟨hwt, hwf⟩ := XF.same_eq_some.mp hw
          have := evals_ternary (ih c hsc hc hrc) (ih t hst hwt hrt) (ih f hsf hwf hrf)
          simp only [Expr2.xfBits, hc, Option.getD_some]
          exact this
    | concat parts =>
        simp only [Expr2.xfWidth] at hw
        have hparts : ∀ p ∈ parts.toList, evalPure2 st p =
            .ok (LVec.ofBoolFn ((p.xfWidth d).getD 0) (p.xfBits d (SvState.boolAt st))) := by
          intro p hp
          obtain ⟨a, ha⟩ := xfWidthSum_mem hw hp
          have hps : p.size < n := by have := Expr2.size_lt_concat hp; omega
          have := ih p hps ha (fun r hr' => hr r (by simp only [Expr2.reads]; exact mem_listReads hp hr'))
          rw [ha]
          simpa using this
        show evalPure2 st (.concat parts) =
          .ok (LVec.ofBoolFn w (Expr2.catBits d (SvState.boolAt st) parts.toList))
        simp only [evalPure2_concat, evalPures2_map hparts, Pure2.res_ok_bind, Pure2.res_pure_eq]
        rw [concatMany_map_ofBoolFn d _ parts.toList w hw]
    | slice b lo w' =>
        have hsb : b.size < n := by simp only [Expr2.size] at hs; omega
        simp only [Expr2.xfWidth] at hw
        rcases hbw : b.xfWidth d with _ | bw
        · simp [hbw] at hw
        · simp only [hbw] at hw
          split at hw
          · rename_i hcond
            injection hw with hw
            subst hw
            by_cases hid : ∃ nm, b = .ident nm
            · obtain ⟨nm, rfl⟩ := hid
              have hwk : WinKnown st nm lo w' :=
                hr (.win nm lo w') (by simp [Expr2.reads, Expr2.sliceReads])
              obtain ⟨v, hv, -⟩ := hwk 0 hcond.2
              have hk : ∀ k, k < w' → ∃ bb, v.bits[lo + k]? = some bb ∧ bb.isKnown = true := by
                intro k hk'
                obtain ⟨v', hv', bb, hbb, hbk⟩ := hwk k hk'
                rw [hv] at hv'
                cases hv'
                exact ⟨bb, hbb, hbk⟩
              exact evals_slice_ident hv hk
            · have hid' : ∀ nm, b ≠ .ident nm := fun nm h' => hid ⟨nm, h'⟩
              have hrb : ∀ x ∈ b.reads, ReadKnown d st x := fun x h' =>
                hr x (by rw [Expr2.reads_slice_of_not_ident hid']; exact h')
              exact evals_slice (ih b hsb hbw hrb) hcond.1
          · simp at hw
    | repl c a =>
        have hsa : a.size < n := by simp only [Expr2.size] at hs; omega
        have hra : ∀ r ∈ a.reads, ReadKnown d st r := fun r h' => hr r (by simpa [Expr2.reads] using h')
        simp only [Expr2.xfWidth] at hw
        obtain ⟨aw, haw, rfl⟩ := Option.map_eq_some_iff.mp hw
        have := evals_repl (n := c) (ih a hsa haw hra)
        simp only [Expr2.xfBits, haw, Option.getD_some]
        exact this
    | reduce op a =>
        have hsa : a.size < n := by simp only [Expr2.size] at hs; omega
        have hra : ∀ r ∈ a.reads, ReadKnown d st r := fun r h' => hr r (by simpa [Expr2.reads] using h')
        simp only [Expr2.xfWidth] at hw
        obtain ⟨aw, haw, rfl⟩ := Option.map_eq_some_iff.mp hw
        have := evals_reduce (op := op) (ih a hsa haw hra)
        simp only [Expr2.xfBits, haw, Option.getD_some]
        exact this
    | resize w' a =>
        have hsa : a.size < n := by simp only [Expr2.size] at hs; omega
        have hra : ∀ r ∈ a.reads, ReadKnown d st r := fun r h' => hr r (by simpa [Expr2.reads] using h')
        simp only [Expr2.xfWidth] at hw
        obtain ⟨aw, haw, rfl⟩ := Option.map_eq_some_iff.mp hw
        have := evals_resize (w' := w') (ih a hsa haw hra)
        simp only [Expr2.xfBits, haw, Option.getD_some]
        exact this

end Compose



/-! ## Bridges to the port types -/

theorem LVec.boolAt_ofBitVec {w : Nat} (x : BitVec w) {i : Nat} (hi : i < w) :
    (LVec.ofBitVec x).boolAt i = x.getLsbD i := by
  simp [LVec.boolAt, LVec.getElem?_ofBitVec, hi, Logic.ofBool_beq_l1]

theorem LVec.boolAt_ofBoolFn {w : Nat} (f : Nat → Bool) {k : Nat} (hk : k < w) :
    (LVec.ofBoolFn w f).boolAt k = f k := by
  simp [LVec.boolAt, LVec.getElem?_ofBoolFn, hk, Logic.ofBool_beq_l1]

theorem SvState.boolAt_of_lookup {st : SvState} {n : String} {v : LVec}
    (h : SvState.lookup st n = some v) (k : Nat) : st.boolAt n k = v.boolAt k := by
  simp [SvState.boolAt, h]

/-- A port holding `LVec.ofBitVec x` has Boolean bits `x.getLsbD i`. -/
theorem SvState.boolAt_ofBitVec {st : SvState} {n : String} {w : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) {i : Nat} (hi : i < w) :
    st.boolAt n i = x.getLsbD i := by
  rw [SvState.boolAt_of_lookup h, LVec.boolAt_ofBitVec x hi]

/-- A signal all of whose bits are known is the Boolean vector of its Boolean bits. -/
theorem SvState.lookup_eq_ofBoolFn {st : SvState} {n : String} {v : LVec} {W : Nat}
    (hv : SvState.lookup st n = some v) (hw : v.width = W)
    (hk : ∀ k, k < W → KnownBit st n k) : v = LVec.ofBoolFn W (SvState.boolAt st n) := by
  have hall : v.allKnown = true := by
    simp only [LVec.allKnown, Array.all_eq_true]
    intro i hi
    have hiW : i < W := by
      have : v.width = v.bits.size := rfl
      omega
    obtain ⟨v', hv', b, hb, hbk⟩ := hk i hiW
    rw [hv] at hv'
    cases hv'
    rw [Array.getElem?_eq_getElem hi] at hb
    cases hb
    exact hbk
  refine (LVec.eq_ofBoolFn_of_allKnown hall).trans ?_
  rw [hw]
  exact LVec.ofBoolFn_congr (fun k _ => by rw [SvState.boolAt_of_lookup hv])

/-- A signal all of whose bits are known is the `ofBitVec` of the `BitVec` of its Boolean
bits (`XF.bv`): the bridge from per-bit knownness to the port types of `sv_bitvec`. -/
theorem SvState.lookup_eq_ofBitVec_bv {st : SvState} {n : String} {v : LVec} {W : Nat}
    (hv : SvState.lookup st n = some v) (hw : v.width = W)
    (hk : ∀ k, k < W → KnownBit st n k) :
    v = LVec.ofBitVec (XF.bv W (SvState.boolAt st n)) :=
  (SvState.lookup_eq_ofBoolFn hv hw hk).trans (LVec.ofBoolFn_eq_ofBitVec_bv _ _)


/-! ## Agreement table (`#guard`)

The expression theorem is proved; this table is its executable twin and the non-vacuity check of
the DEFINITIONS (a fragment that returned `none` everywhere, or a Boolean evaluator that
disagreed with the interpreter, would still typecheck). Every row evaluates one expression with
the interpreter (`evalPure2`) and with the Boolean evaluator (`xfBits`) on several states, and
checks that the static width is `some w` and that the interpreter's value is exactly
`LVec.ofBoolFn w (xfBits …)`. -/

section Tests

private def tD : Design2 where
  name := "t"
  decls := #[{ name := "a", width := 4, isInput := true }, { name := "b", width := 4, isInput := true },
    { name := "s", width := 1, isInput := true }, { name := "y", width := 4 }]
  processes := #[]

private def tStates : List SvState :=
  [(0, 0, 0), (11, 5, 1), (15, 15, 0), (3, 12, 1), (9, 1, 1), (6, 6, 0), (1, 15, 1), (8, 3, 0)].map
    fun (x, y, z) => [("a", LVec.ofNat 4 x), ("b", LVec.ofNat 4 y), ("s", LVec.ofNat 1 z),
      ("y", LVec.xVec 4)]

private def agree (e : Expr2) (w : Nat) : Bool :=
  e.xfWidth tD == some w &&
    tStates.all fun st =>
      match evalPure2 st e with
      | .ok v => v == LVec.ofBoolFn w (e.xfBits tD (SvState.boolAt st))
      | _ => false

private def ia : Expr2 := .ident "a"
private def ib : Expr2 := .ident "b"
private def is_ : Expr2 := .ident "s"

#guard agree (.lit (LVec.lit "1010")) 4
#guard agree ia 4
#guard agree (.unary .bnot ia) 4
#guard agree (.unary .lnot ia) 1
#guard agree (.unary .neg ia) 4
#guard agree (.unary .pos ia) 4
#guard agree (.binary .and ia ib) 4
#guard agree (.binary .or ia ib) 4
#guard agree (.binary .xor ia ib) 4
#guard agree (.binary .add ia ib) 4
#guard agree (.binary .sub ia ib) 4
#guard agree (.binary .mul ia ib) 4
#guard agree (.binary .eq ia ib) 1
#guard agree (.binary .ne ia ib) 1
#guard agree (.binary .caseEq ia ib) 1
#guard agree (.binary .caseNe ia ib) 1
#guard agree (.binary .lt ia ib) 1
#guard agree (.binary .le ia ib) 1
#guard agree (.binary .gt ia ib) 1
#guard agree (.binary .ge ia ib) 1
#guard agree (.binary (.shl false) ia ib) 4
#guard agree (.binary (.shr false) ia ib) 4
#guard agree (.binary (.ashl false) ia ib) 4
#guard agree (.binary (.ashr false) ia ib) 4
#guard agree (.logical true ia ib) 1
#guard agree (.logical false ia ib) 1
#guard agree (.reduce .or ia) 1
#guard agree (.reduce .and ia) 1
#guard agree (.reduce .xor ia) 1
#guard agree (.reduce .nor ia) 1
#guard agree (.reduce .nand ia) 1
#guard agree (.reduce .xnor ia) 1
#guard agree (.ternary is_ ia ib) 4
#guard agree (.ternary ib ia (.unary .bnot ia)) 4
#guard agree (.concat #[ia, ib]) 8
#guard agree (.concat #[is_, ia, .lit (LVec.lit "01")]) 7
#guard agree (.slice ia 1 2) 2
#guard agree (.slice (.binary .add ia ib) 1 3) 3
#guard agree (.resize 8 ia) 8
#guard agree (.resize 2 ia) 2
#guard agree (.repl 3 ia) 12
#guard agree (.repl 2 (.slice ib 2 2)) 4
#guard agree (.binary .add (.binary .mul ia ib) (.binary (.shl false) ia (.lit (LVec.lit "01")))) 4

-- the rows that must NOT be in the fragment
#guard (Expr2.lit (LVec.lit "1x0")).xfWidth tD == none
#guard (Expr2.lit (LVec.lit "1z")).xfWidth tD == none
#guard (Expr2.ident "nope").xfWidth tD == none
#guard (Expr2.binary .and ia is_).xfWidth tD == none           -- width mismatch
#guard (Expr2.binary .xor ia (.slice ib 0 3)).xfWidth tD == none
#guard (Expr2.ternary is_ ia is_).xfWidth tD == none           -- arm width mismatch
#guard (Expr2.slice ia 2 3).xfWidth tD == none                 -- window leaves the vector
#guard (Expr2.slice ia 0 0).xfWidth tD == none                 -- empty window
#guard (Expr2.index ia ib 1).xfWidth tD == none                -- dynamic index
#guard (Expr2.binary .div ia ib).xfWidth tD == none            -- division
#guard (Expr2.binary .rem ia ib).xfWidth tD == none
#guard (Expr2.binary (.pow false false) ia ib).xfWidth tD == none
#guard (Expr2.binary (.ashr true) ia ib).xfWidth tD == none
#guard (Expr2.binary .slt ia ib).xfWidth tD == none
#guard (Expr2.scmp .lt ia ib).xfWidth tD == none
#guard (Expr2.resizeSigned 8 ia).xfWidth tD == none
#guard (Expr2.unsupported "k" "t").xfWidth tD == none
#guard (Expr2.concat #[ia, .lit (LVec.lit "x")]).xfWidth tD == none

end Tests

end LeanModels.Sv
