import LeanModels.Sv.Pure2
import LeanModels.Sv.Obs

/-!
# Known-value calculus for the semantic tier (`LeanModels.Sv` — Design2)

`evalPure2` (`Pure2.lean`) removed fuel from expression evaluation; this file
removes the four-state representation. On states whose relevant signals hold
fully-known values `LVec.ofBitVec x`, every gate-level operator of the tier
(`slice`, `& | ^ ~`, `+ - *`, `{…}`, `{n{…}}`, reductions, `?:` with a
known condition, unsigned/equality comparisons, select-write `insertAt`,
`resizeU`) computes `LVec.ofBitVec` of the corresponding `BitVec` term, and
`simp` performs the translation. A proof about a design's settled values is
then a proof about `BitVec`/`Bool` algebra — no bit-blasting, no
`bv_decide`, no enumeration of inputs.

## Design laws

* **One representation lemma.** `LVec.ofBitVec x` has bit `i` equal to
  `Logic.ofBool (x.getLsbD i)` (`LVec.ofBitVec_bits`, by `rfl` — `ofBitVec`
  is `ofNat w x.toNat` and `getLsbD` is `toNat.testBit`). The vector-valued
  select, bitwise, concatenation and replication lemmas are proved
  bit-by-bit from it through the extensionality principle
  `LVec.ext_getElem?`, and the reductions and `==` by folding over its bits;
  the arithmetic and comparison lemmas go through `toNat` (`sub_ofBitVec` by
  `BitVec.toNat_sub`; `add_ofBitVec` / `mul_ofBitVec` are `Obs.lean`'s, only
  made `@[simp]` here; `lt`/`le`/`gt`/`ge_ofBitVec` unfold `relOp`); the
  closed `Logic` facts `ofLogic_ofBool`/`_l0`/`_l1` are `decide` on concrete
  1-bit vectors. No lemma evaluates over symbolic inputs.
* **`ofBitVec` is the normal form of a known vector.** The `@[simp]` lemmas
  all rewrite *towards* `LVec.ofBitVec <BitVec term>` (and `LVec.ofNat`,
  `LVec.replicate .l0/.l1`, `LVec.ofLogic` of a known bit are rewritten into
  it). The `BitVec` side is core's: `&&&`, `|||`, `^^^`, `~~~`, `+`, `-`, `*`,
  `++`, `extractLsb'`, `setWidth`, `replicate`, `BitVec.ofBool`, plus two
  helpers defined here, `bvInsertAt` (select-write) and `bvParity` (`^v`).
* **Source order is preserved.** `{p₀, …, pₙ}` (first part = MSB) becomes
  the right-nested `x₀ ++ (x₁ ++ … ++ xₙ)` — core's `++` also puts its left
  operand in the high bits, so no reversal appears anywhere.
* **Range side conditions are explicit.** A slice lemma fires only in range
  (`lo + k ≤ w`; the single-bit form `i < w`); out-of-range reads produce
  `x` bits in the interpreter and are not "known". Under `sv2_known` the
  side conditions are discharged by `omega` from the context.
* **Per-bit conclusion.** `LVec.eq_ofBitVec_of_extract_one` is how a proof
  concludes an output's value from per-bit window equations (`v.width = w`
  and `v.extract i 1 = ofBitVec (BitVec.ofBool (x.getLsbD i))` for all
  `i < w` give `v = ofBitVec x`); `LVec.ext_bits` / `LVec.ext_getElem?` are
  the raw extensionality principles and `LVec.ofBitVec_inj` decides equality
  of known vectors of equal width.

## Simp interface

All operator lemmas are global `@[simp]` (together with `Pure2`'s
per-constructor `evalPure2_*` equation lemmas and `Res` bind normalizers,
which they compose with). The recommended entry point is the tactic

    sv2_known [h₁, h₂, …]

= `simp (disch := sv2_disch) [readSignal, extractLsb'_one_eq_ofBool, h₁, h₂, …]`
where the `hᵢ` are the state facts `SvState.lookup st "a" = some (LVec.ofBitVec x)`
and range facts, and `sv2_disch` = `first | assumption | omega | simp_all`.
The `@[simp]` set it relies on (the "`sv2_known` set"):

* representation: `LVec.width_ofBitVec`, `LVec.toNat_ofBitVec`,
  `LVec.toNat?_ofBitVec`, `LVec.allKnown_ofBitVec`, `LVec.ofBitVec_inj`,
  `LVec.ofNat_eq_ofBitVec`, `LVec.replicate_l0`, `LVec.replicate_l1`,
  `LVec.ofLogic_ofBool`, `LVec.ofLogic_l0`, `LVec.ofLogic_l1`, `LVec.ite_ofBitVec`,
  `Logic.ofBool_true/false/inj`, `Logic.not/and/or/xor_ofBool`;
* selects: `LVec.extract_one_ofBitVec` (priority high), `LVec.extract_ofBitVec`,
  `LVec.insertAt_ofBitVec`, `LVec.resizeU_ofBitVec`, `getLsbD_bvInsertAt`,
  `getElem_bvInsertAt`;
* operators: `LVec.and/or/xor/not_ofBitVec`, `LVec.add/sub/mul_ofBitVec`,
  `LVec.concat_ofBitVec`, `LVec.concatMany_nil/singleton/cons_cons`,
  `LVec.replVec_ofBitVec`, `LVec.redOr/redAnd/redXor_ofBitVec`,
  `LVec.condTrue_ofBitVec`, `LVec.isKnownZero_ofBitVec`,
  `LVec.ternary_ofBitVec_ofBool` (priority high), `LVec.ternary_ofBitVec`,
  `LVec.lt/le/gt/ge_ofBitVec`, `LVec.eqLogical/neLogical/eqCase/neCase_ofBitVec`;
* dispatch: `evalBinOp_{add,sub,mul,and,or,xor,eq,ne,caseEq,caseNe,lt,le,gt,ge}`,
  `evalUnaryOp_bnot`, `evalRedOp_{or,and,xor,nor,nand,xnor}`.

Two priorities matter and are why `sv2_known` does NOT re-list the set (an
explicit simp argument loses its attribute priority): the single-bit slice
lemma must beat the general one (`ofBool (x.getLsbD i)`, not
`x.extractLsb' i 1` — `extractLsb'_one_eq_ofBool` is passed as a backstop
anyway), and the 1-bit ternary lemma must beat the general one (`if c`, not
`if BitVec.ofBool c = 0#1`). Core's own `simp` rewrites an in-range
`x.getLsbD i` to `x[i]`; statements may use either form.

**Never unfold `LVec.ofBitVec` under `simp`.** `ofBitVec x` is defined as
`ofNat w x.toNat`, and the global `@[simp]` lemma `LVec.ofNat_eq_ofBitVec`
folds that straight back, so `simp [LVec.ofBitVec]` loops ("maximum
recursion depth has been reached"). To look inside a known vector, use
`LVec.ofBitVec_bits` (its bits, by `rfl`), `LVec.getElem?_ofBitVec` (one
bit), or `LVec.eq_ofBitVec_iff` (width plus bits); to unfold the definition
itself, `rw [LVec.ofBitVec]`, or `simp [-LVec.ofNat_eq_ofBitVec,
LVec.ofBitVec]`.

For term-mode or `rw` proofs, `evalPure2_*_ofBitVec` (end of file) are the
compositional (Hoare-style) versions: from the operands' `.ok (ofBitVec _)`
facts to the node's. They are not `@[simp]` (their `BitVec` operands are not
determined by the left-hand side).

The acceptance examples at the end: a 3-gate expression over
`slice (ident n) i 1` reads at symbolic width and index, the full-adder
sum/carry pair at symbolic bits, the ripple-adder carry over an `N+1`-bit
carry chain, a mixed-width concatenation with a reduction, a known-condition
ternary over arithmetic, and an `insertAt`/`extract` round trip.
-/

namespace LeanModels.Sv

/-! ## Known bits -/

/-- The `Logic` image of a `Bool` (`true ↦ 1`, `false ↦ 0`): the bits of a
known vector. -/
def Logic.ofBool (b : Bool) : Logic := if b then .l1 else .l0

namespace Logic

@[simp] theorem ofBool_true : Logic.ofBool true = .l1 := rfl
@[simp] theorem ofBool_false : Logic.ofBool false = .l0 := rfl

/-- `Logic.ofBool` is injective. -/
@[simp] theorem ofBool_inj {a b : Bool} : Logic.ofBool a = Logic.ofBool b ↔ a = b := by
  cases a <;> cases b <;> decide

/-- `~` on a known bit. -/
@[simp] theorem not_ofBool (a : Bool) : (Logic.ofBool a).not = Logic.ofBool (!a) := by
  cases a <;> rfl

/-- `&` on known bits. -/
@[simp] theorem and_ofBool (a b : Bool) :
    Logic.and (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- `|` on known bits. -/
@[simp] theorem or_ofBool (a b : Bool) :
    Logic.or (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- `^` on known bits. -/
@[simp] theorem xor_ofBool (a b : Bool) :
    Logic.xor (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (a ^^ b) := by
  cases a <;> cases b <;> rfl

end Logic

namespace LVec

/-! ## Representation and extensionality -/

/-- **The representation lemma.** Bit `i` of `ofBitVec x` is
`Logic.ofBool (x.getLsbD i)` (definitional). -/
theorem ofBitVec_bits {w : Nat} (x : BitVec w) :
    (ofBitVec x).bits = Array.ofFn (fun i : Fin w => Logic.ofBool (x.getLsbD i)) := rfl

/-- A known vector has its `BitVec`'s width. -/
@[simp] theorem width_ofBitVec {w : Nat} (x : BitVec w) : (ofBitVec x).width = w := by
  simp only [width, ofBitVec_bits, Array.size_ofFn]

/-- Optional bit read of a known vector. -/
theorem getElem?_ofBitVec {w : Nat} (x : BitVec w) (i : Nat) :
    (ofBitVec x).bits[i]? = if i < w then some (Logic.ofBool (x.getLsbD i)) else none := by
  rw [ofBitVec_bits, Array.getElem?_ofFn]
  split <;> simp_all

/-- In-range bit read of a known vector. -/
theorem getElem_ofBitVec {w : Nat} (x : BitVec w) (i : Nat) (h : i < (ofBitVec x).bits.size) :
    (ofBitVec x).bits[i] = Logic.ofBool (x.getLsbD i) := by
  simp only [ofBitVec_bits, Array.getElem_ofFn]

/-- Known vectors are fully known. -/
@[simp] theorem allKnown_ofBitVec {w : Nat} (x : BitVec w) : (ofBitVec x).allKnown = true :=
  allKnown_ofNat _ _

/-- The unsigned value of a known vector. -/
@[simp] theorem toNat_ofBitVec {w : Nat} (x : BitVec w) : (ofBitVec x).toNat = x.toNat := by
  rw [ofBitVec, toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- The decided unsigned value of a known vector. -/
@[simp] theorem toNat?_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).toNat? = some x.toNat := by
  rw [ofBitVec, toNat?_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- **Extensionality** on optional bit reads. -/
theorem ext_getElem? {u v : LVec} (h : ∀ i : Nat, u.bits[i]? = v.bits[i]?) : u = v := by
  cases u; cases v
  exact congrArg LVec.mk (Array.ext_getElem? h)

/-- **Extensionality** (`LVec.ext_bits`): two vectors of the same width with
the same bit at every index are equal. -/
theorem ext_bits {u v : LVec} (hw : u.width = v.width)
    (h : ∀ (i : Nat) (hu : i < u.width) (hv : i < v.width), u.bits[i] = v.bits[i]) :
    u = v := by
  apply ext_getElem?
  intro i
  by_cases hi : i < u.width
  · have hv : i < v.width := hw ▸ hi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hv, h i hi hv]
  · have hv : ¬ i < v.width := hw ▸ hi
    rw [Array.getElem?_eq_none (by simpa [width] using hi),
      Array.getElem?_eq_none (by simpa [width] using hv)]

/-- Vector equality is same width and same bit at every index. -/
theorem ext_bits_iff {u v : LVec} :
    u = v ↔ u.width = v.width ∧
      ∀ (i : Nat) (hu : i < u.width) (hv : i < v.width), u.bits[i] = v.bits[i] :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ _ => rfl⟩, fun ⟨hw, h⟩ => ext_bits hw h⟩

/-- A vector is the known value `ofBitVec x` iff it has width `w` and the
bits of `x`. -/
theorem eq_ofBitVec_iff {w : Nat} {v : LVec} {x : BitVec w} :
    v = ofBitVec x ↔
      v.width = w ∧ ∀ i, i < w → v.bits[i]? = some (Logic.ofBool (x.getLsbD i)) := by
  constructor
  · rintro rfl
    refine ⟨width_ofBitVec x, fun i hi => ?_⟩
    rw [getElem?_ofBitVec]; simp only [hi, if_true]
  · rintro ⟨hw, h⟩
    apply ext_getElem?
    intro i
    rw [getElem?_ofBitVec]
    by_cases hi : i < w
    · rw [if_pos hi, h i hi]
    · rw [if_neg hi]
      apply Array.getElem?_eq_none
      simp only [width] at hw; omega

/-- **Injectivity** of `ofBitVec` at equal width. -/
@[simp] theorem ofBitVec_inj {w : Nat} {x y : BitVec w} : ofBitVec x = ofBitVec y ↔ x = y := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v => v.bits[i]?) h
    simp only [getElem?_ofBitVec, hi, if_true, Option.some.injEq, Logic.ofBool_inj] at this
    exact this
  · rintro rfl; rfl

/-- Equal known vectors have equal widths. -/
theorem width_eq_of_ofBitVec_eq {w v : Nat} {x : BitVec w} {y : BitVec v}
    (h : ofBitVec x = ofBitVec y) : w = v := by
  have := congrArg LVec.width h
  simpa using this

/-- `LVec.ofNat` is a known vector (rewritten into the `ofBitVec` normal form). -/
@[simp] theorem ofNat_eq_ofBitVec (w n : Nat) : ofNat w n = ofBitVec (BitVec.ofNat w n) := by
  rw [ofBitVec, BitVec.toNat_ofNat, ofNat_emod]

/-- An all-`0` vector (`'0` fill) is known. -/
@[simp] theorem replicate_l0 (w : Nat) : replicate w .l0 = ofBitVec (0#w) := by
  rw [eq_ofBitVec_iff]
  refine ⟨by simp [replicate, width], fun i hi => ?_⟩
  simp [replicate, hi]

/-- An all-`1` vector (`'1` fill) is known. -/
@[simp] theorem replicate_l1 (w : Nat) : replicate w .l1 = ofBitVec (BitVec.allOnes w) := by
  rw [eq_ofBitVec_iff]
  refine ⟨by simp [replicate, width], fun i hi => ?_⟩
  simp [replicate, hi]

/-- A known single bit lifted to a vector (the `Logic`-valued operators). -/
@[simp] theorem ofLogic_ofBool (b : Bool) :
    ofLogic (Logic.ofBool b) = ofBitVec (BitVec.ofBool b) := by
  cases b <;> decide

@[simp] theorem ofLogic_l0 : ofLogic .l0 = ofBitVec (BitVec.ofBool false) := by decide
@[simp] theorem ofLogic_l1 : ofLogic .l1 = ofBitVec (BitVec.ofBool true) := by decide

/-- A conditional between two known values is the known conditional. -/
@[simp] theorem ite_ofBitVec {w : Nat} (p : Prop) [Decidable p] (x y : BitVec w) :
    (if p then ofBitVec x else ofBitVec y) = ofBitVec (if p then x else y) := by
  split <;> rfl

/-! ## Selects: `extract`, the per-bit window form -/

/-- Optional bit read of a slice. -/
theorem getElem?_extract (v : LVec) (lo k i : Nat) :
    (v.extract lo k).bits[i]? = if i < k then some (v.bits[lo + i]?.getD .lx) else none := by
  simp only [extract, Array.getElem?_ofFn]
  split <;> simp_all

/-- **In-range part-select** of a known vector: `x[lo +: k]`. -/
@[simp] theorem extract_ofBitVec {w : Nat} (x : BitVec w) {lo k : Nat} (h : lo + k ≤ w) :
    (ofBitVec x).extract lo k = ofBitVec (x.extractLsb' lo k) := by
  apply ext_getElem?
  intro i
  rw [getElem?_extract, getElem?_ofBitVec, getElem?_ofBitVec]
  by_cases hi : i < k
  · have : lo + i < w := by omega
    simp [hi, this]
  · simp [hi]

end LVec

/-- A length-1 `extractLsb'` is the `ofBool` of the bit (at every index: out
of range both sides are `0`). Not `@[simp]` (it would race core's
`extractLsb'_eq_self` on `BitVec 1`); `sv2_known` passes it. -/
theorem extractLsb'_one_eq_ofBool {w : Nat} (x : BitVec w) (i : Nat) :
    x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : j = 0 := by omega
  subst this
  simp

namespace LVec

/-- **In-range bit-select** of a known vector: `x[i]` is the 1-bit
`BitVec.ofBool (x.getLsbD i)`. Priority high: preferred over the general
`extract_ofBitVec`. -/
@[simp high] theorem extract_one_ofBitVec {w : Nat} (x : BitVec w) {i : Nat} (h : i < w) :
    (ofBitVec x).extract i 1 = ofBitVec (BitVec.ofBool (x.getLsbD i)) := by
  rw [extract_ofBitVec x (by omega), extractLsb'_one_eq_ofBool]

/-- **The per-bit window form.** A vector of width `w` whose every 1-bit
window holds the corresponding bit of `x` is `ofBitVec x` — how a proof
concludes an output's value from per-bit (settle) equations. -/
theorem eq_ofBitVec_of_extract_one {w : Nat} {v : LVec} {x : BitVec w} (hw : v.width = w)
    (h : ∀ i, i < w → v.extract i 1 = ofBitVec (BitVec.ofBool (x.getLsbD i))) :
    v = ofBitVec x := by
  rw [eq_ofBitVec_iff]
  refine ⟨hw, fun i hi => ?_⟩
  have h1 := congrArg (fun u => u.bits[0]?) (h i hi)
  have hiv : i < v.bits.size := by simp only [width] at hw; omega
  simp only [getElem?_extract, getElem?_ofBitVec, Nat.zero_lt_one, if_true, Nat.add_zero,
    Array.getElem?_eq_getElem hiv, Option.getD_some, Option.some.injEq,
    BitVec.getLsbD_ofBool, decide_true, Bool.true_and] at h1
  rw [Array.getElem?_eq_getElem hiv, h1]

/-! ## Width conversion and select-write -/

/-- `resizeU` (zero-extend / truncate) of a known vector is `setWidth`. -/
@[simp] theorem resizeU_ofBitVec {w : Nat} (x : BitVec w) (w' : Nat) :
    (ofBitVec x).resizeU w' = ofBitVec (x.setWidth w') := by
  apply ext_getElem?
  intro i
  simp only [resizeU, Array.getElem?_ofFn, getElem?_ofBitVec]
  by_cases hi : i < w'
  · by_cases hw : i < w
    · simp [hi, hw]
    · simp [hi, hw, BitVec.getLsbD_of_ge x i (by omega)]
  · simp [hi]

end LVec

/-- `BitVec`-level select-write: `x` with bits `[lo, lo + k)` replaced by
`y`; bits of `y` landing at or above `w` are dropped, exactly as
`LVec.insertAt` drops them. Defined by masking, so `simp`/`getLsbD`
reasoning applies directly (`getLsbD_bvInsertAt`). -/
def bvInsertAt {w k : Nat} (x : BitVec w) (lo : Nat) (y : BitVec k) : BitVec w :=
  (x &&& ~~~(((BitVec.allOnes k).setWidth w) <<< lo)) ||| ((y.setWidth w) <<< lo)

/-- The bits of a select-write: the window holds `y`, everything else `x`. -/
@[simp] theorem getLsbD_bvInsertAt {w k : Nat} (x : BitVec w) (lo : Nat) (y : BitVec k)
    {i : Nat} (hi : i < w) :
    (bvInsertAt x lo y).getLsbD i =
      if lo ≤ i ∧ i < lo + k then y.getLsbD (i - lo) else x.getLsbD i := by
  simp only [bvInsertAt, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases h1 : i < lo
  · have : ¬ (lo ≤ i ∧ i < lo + k) := by omega
    simp [h1, hi, this]
  · by_cases h2 : i < lo + k
    · have : lo ≤ i ∧ i < lo + k := by omega
      simp [h1, hi, this, show i - lo < w by omega, show i - lo < k by omega]
    · have : ¬ (lo ≤ i ∧ i < lo + k) := by omega
      simp [h1, hi, this, show ¬ i - lo < k by omega,
        BitVec.getLsbD_of_ge y (i - lo) (by omega)]

/-- `getElem` twin of `getLsbD_bvInsertAt` (core's `simp` rewrites an
in-range `getLsbD` to `getElem`, so both forms are needed). -/
@[simp] theorem getElem_bvInsertAt {w k : Nat} (x : BitVec w) (lo : Nat) (y : BitVec k)
    {i : Nat} (hi : i < w) :
    (bvInsertAt x lo y)[i] = if lo ≤ i ∧ i < lo + k then y.getLsbD (i - lo) else x[i] := by
  have h := getLsbD_bvInsertAt x lo y hi
  rw [BitVec.getLsbD_eq_getElem hi] at h
  rw [h, BitVec.getLsbD_eq_getElem hi]

/-- Parity of a `BitVec` (xor of all its bits, LSB first) — the value of `^v`. -/
def bvParity {w : Nat} (x : BitVec w) : Bool :=
  (List.ofFn fun i : Fin w => x.getLsbD i).foldl (· ^^ ·) false

namespace LVec

/-- **Select-write** of a known value into a known vector (any offset: bits
past the width are dropped on both sides). -/
@[simp] theorem insertAt_ofBitVec {w k : Nat} (x : BitVec w) (lo : Nat) (y : BitVec k) :
    (ofBitVec x).insertAt lo (ofBitVec y) = ofBitVec (bvInsertAt x lo y) := by
  apply ext_getElem?
  intro i
  simp only [insertAt, Array.getElem?_ofFn, getElem?_ofBitVec, width_ofBitVec]
  by_cases hi : i < w
  · rw [dif_pos hi, if_pos hi, getLsbD_bvInsertAt x lo y hi]
    by_cases hr : lo ≤ i ∧ i < lo + k
    · simp [hr, hi, show i - lo < k by omega]
    · simp [hr, hi]
  · rw [dif_neg hi, if_neg hi]

/-! ## Bitwise operators -/

/-- Generic per-bit zip of known vectors: a `Logic` table that is the image
of a `Bool` table `g` computes the `BitVec` whose bits are `g`. -/
theorem zipWith_ofBitVec {w : Nat} (f : Logic → Logic → Logic) (g : Bool → Bool → Bool)
    (hf : ∀ a b, f (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (g a b))
    (x y z : BitVec w) (hz : ∀ i, i < w → z.getLsbD i = g (x.getLsbD i) (y.getLsbD i)) :
    zipWith f (ofBitVec x) (ofBitVec y) = ofBitVec z := by
  unfold zipWith
  rw [if_pos (by simp)]
  apply ext_getElem?
  intro i
  show (Array.zipWith f (ofBitVec x).bits (ofBitVec y).bits)[i]? = _
  rw [Array.getElem?_zipWith, getElem?_ofBitVec, getElem?_ofBitVec, getElem?_ofBitVec]
  by_cases hi : i < w
  · simp only [hi, if_true, hf, hz i hi]
  · simp only [hi, if_false]

/-- `&` of known vectors. -/
@[simp] theorem and_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).and (ofBitVec y) = ofBitVec (x &&& y) :=
  zipWith_ofBitVec _ (· && ·) Logic.and_ofBool x y _ (fun _ _ => BitVec.getLsbD_and)

/-- `|` of known vectors. -/
@[simp] theorem or_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).or (ofBitVec y) = ofBitVec (x ||| y) :=
  zipWith_ofBitVec _ (· || ·) Logic.or_ofBool x y _ (fun _ _ => BitVec.getLsbD_or)

/-- `^` of known vectors. -/
@[simp] theorem xor_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).xor (ofBitVec y) = ofBitVec (x ^^^ y) :=
  zipWith_ofBitVec _ (· ^^ ·) Logic.xor_ofBool x y _ (fun _ _ => BitVec.getLsbD_xor)

/-- `~` of a known vector. -/
@[simp] theorem not_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).not = ofBitVec (~~~x) := by
  apply ext_getElem?
  intro i
  simp only [LVec.not, Array.getElem?_map, getElem?_ofBitVec]
  by_cases hi : i < w
  · simp [hi]
  · simp [hi]

/-! ## Concatenation and replication -/

/-- `{x, y}` of known vectors (`x` = MSB part) is `x ++ y`. -/
@[simp] theorem concat_ofBitVec {n m : Nat} (x : BitVec n) (y : BitVec m) :
    (ofBitVec x).concat (ofBitVec y) = ofBitVec (x ++ y) := by
  apply ext_getElem?
  intro i
  simp only [LVec.concat, Array.getElem?_append, getElem?_ofBitVec, BitVec.getLsbD_append]
  have hs : (ofBitVec y).bits.size = m := width_ofBitVec y
  rw [hs]
  by_cases h1 : i < m
  · simp [h1, show i < n + m by omega]
  · by_cases h2 : i < n + m
    · simp [h1, h2, show i - m < n by omega]
    · simp [h1, h2, show ¬ i - m < n by omega]

/-- `{}` with no parts. -/
@[simp] theorem concatMany_nil : concatMany #[] = ⟨#[]⟩ := rfl

private theorem foldl_concatStep (ps : List LVec) (acc : LVec) :
    ps.foldl (fun acc p => ⟨p.bits ++ acc.bits⟩) acc =
      ⟨(ps.foldl (fun acc p => (⟨p.bits ++ acc.bits⟩ : LVec)) ⟨#[]⟩).bits ++ acc.bits⟩ := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldl_cons]
      rw [ih, ih ⟨p.bits ++ (⟨#[]⟩ : LVec).bits⟩]
      simp [Array.append_assoc]

/-- `concatMany` peels its FIRST (most significant) part: `{p, ps…} =
{p, {ps…}}`. -/
theorem concatMany_cons (p : LVec) (ps : List LVec) :
    concatMany (p :: ps).toArray = p.concat (concatMany ps.toArray) := by
  simp only [concatMany, List.foldl_toArray', List.foldl_cons, LVec.concat]
  rw [foldl_concatStep]
  simp

/-- `{p}` is `p`. -/
@[simp] theorem concatMany_singleton (p : LVec) : concatMany #[p] = p := by
  rw [concatMany_cons]; simp [LVec.concat]

/-- `{p, q, ps…} = {p, {q, ps…}}` (the `simp` form of `concatMany_cons`,
disjoint from `concatMany_singleton`, so a part list reduces to a
right-nested `concat` chain ending in its last part). -/
@[simp] theorem concatMany_cons_cons (p q : LVec) (ps : List LVec) :
    concatMany (p :: q :: ps).toArray = p.concat (concatMany (q :: ps).toArray) :=
  concatMany_cons p (q :: ps)

private theorem getElem?_flatten_replicate {α : Type} (l : List α) (n i : Nat) :
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

/-- `{n{x}}` of a known vector is `BitVec.replicate`. -/
@[simp] theorem replVec_ofBitVec {w : Nat} (n : Nat) (x : BitVec w) :
    replVec n (ofBitVec x) = ofBitVec (x.replicate n) := by
  apply ext_getElem?
  intro i
  rw [getElem?_ofBitVec, replVec, ← Array.getElem?_toList, Array.toList_flatten,
    Array.toList_replicate, List.map_replicate, getElem?_flatten_replicate,
    Array.getElem?_toList, Array.length_toList]
  have hs : (ofBitVec x).bits.size = w := width_ofBitVec x
  rw [hs, getElem?_ofBitVec]
  by_cases hi : i < w * n
  · have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    simp [hi, Nat.mod_lt i hw, Nat.pos_iff_ne_zero.mp hw]
  · simp [hi]

/-! ## Reductions -/

private theorem foldl_map_ofBool (f : Logic → Logic → Logic) (g : Bool → Bool → Bool)
    (hf : ∀ a b, f (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (g a b))
    (l : List Bool) (b : Bool) :
    (l.map Logic.ofBool).foldl f (Logic.ofBool b) = Logic.ofBool (l.foldl g b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldl_cons, hf, ih]

private theorem bits_foldl_ofBitVec {w : Nat} (x : BitVec w) (f : Logic → Logic → Logic)
    (g : Bool → Bool → Bool)
    (hf : ∀ a b, f (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (g a b)) (b : Bool) :
    (ofBitVec x).bits.foldl f (Logic.ofBool b) =
      Logic.ofBool ((List.ofFn fun i : Fin w => x.getLsbD i).foldl g b) := by
  rw [← Array.foldl_toList, ofBitVec_bits, Array.toList_ofFn, ← foldl_map_ofBool f g hf,
    List.map_ofFn]
  rfl

private theorem foldl_or_eq (l : List Bool) (b : Bool) :
    l.foldl (· || ·) b = (b || l.any id) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, Bool.or_assoc]

private theorem foldl_and_eq (l : List Bool) (b : Bool) :
    l.foldl (· && ·) b = (b && l.all id) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih, Bool.and_assoc]

/-- A `BitVec` is nonzero iff some in-range bit is set. -/
theorem _root_.LeanModels.Sv.bv_ne_zero_iff_exists_getLsbD {w : Nat} (x : BitVec w) :
    x ≠ 0#w ↔ ∃ i, i < w ∧ x.getLsbD i = true := by
  rw [Ne, BitVec.eq_of_getLsbD_eq_iff]
  simp

/-- A `BitVec` is all-ones iff every in-range bit is set. -/
theorem _root_.LeanModels.Sv.bv_eq_allOnes_iff_getLsbD {w : Nat} (x : BitVec w) :
    x = BitVec.allOnes w ↔ ∀ i, i < w → x.getLsbD i = true := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h i hi; rw [h i hi]; simp [hi]
  · intro h i hi; rw [h i hi]; simp [hi]

/-- `|v` of a known vector: `1` iff it is nonzero. -/
@[simp] theorem redOr_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).redOr = Logic.ofBool (decide (x ≠ 0#w)) := by
  rw [redOr, show Logic.l0 = Logic.ofBool false from rfl,
    bits_foldl_ofBitVec x _ (· || ·) Logic.or_ofBool, foldl_or_eq]
  congr 1
  rw [Bool.false_or, Bool.eq_iff_iff, decide_eq_true_iff, bv_ne_zero_iff_exists_getLsbD,
    List.any_eq_true]
  simp only [List.mem_ofFn, id]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩; exact ⟨i, i.isLt, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, h⟩

/-- `&v` of a known vector: `1` iff it is all-ones. -/
@[simp] theorem redAnd_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).redAnd = Logic.ofBool (decide (x = BitVec.allOnes w)) := by
  rw [redAnd, show Logic.l1 = Logic.ofBool true from rfl,
    bits_foldl_ofBitVec x _ (· && ·) Logic.and_ofBool, foldl_and_eq]
  congr 1
  rw [Bool.true_and, Bool.eq_iff_iff, decide_eq_true_iff, bv_eq_allOnes_iff_getLsbD,
    List.all_eq_true]
  simp only [List.mem_ofFn, id]
  constructor
  · intro h i hi; exact h _ ⟨⟨i, hi⟩, rfl⟩
  · rintro h _ ⟨i, rfl⟩; exact h i i.isLt

/-- `^v` of a known vector: its parity. -/
@[simp] theorem redXor_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).redXor = Logic.ofBool (bvParity x) := by
  rw [redXor, show Logic.l0 = Logic.ofBool false from rfl,
    bits_foldl_ofBitVec x _ (· ^^ ·) Logic.xor_ofBool]
  rfl

/-! ## Conditional -/

/-- `if`-truthiness of a known vector: nonzero. -/
@[simp] theorem condTrue_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).condTrue = decide (x ≠ 0#w) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, bv_ne_zero_iff_exists_getLsbD, condTrue,
    Array.any_eq_true]
  simp only [ofBitVec_bits, Array.size_ofFn, Array.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by cases hb : x.getLsbD i <;> simp_all [Logic.ofBool]⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by simp [h]⟩

/-- Definitely-false test of a known vector: zero. -/
@[simp] theorem isKnownZero_ofBitVec {w : Nat} (x : BitVec w) :
    (ofBitVec x).isKnownZero = decide (x = 0#w) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, BitVec.eq_of_getLsbD_eq_iff, isKnownZero,
    Array.all_eq_true]
  simp only [ofBitVec_bits, Array.size_ofFn, Array.getElem_ofFn, BitVec.getLsbD_zero]
  constructor
  · intro h i hi; have := h i hi; cases hb : x.getLsbD i <;> simp_all [Logic.ofBool]
  · intro h i hi; simp [h i hi]

/-- `c ? a : b` with a known condition never merges: zero selects `b`,
nonzero selects `a`. -/
@[simp] theorem ternary_ofBitVec {w : Nat} (c : BitVec w) (a b : LVec) :
    ternary (ofBitVec c) a b = if c = 0#w then b else a := by
  by_cases hc : c = 0#w <;> simp [ternary, hc]

/-- **Known 1-bit condition**: `c ? a : b` selects by the `Bool`. Priority
high: preferred over the general `ternary_ofBitVec` (whose test would be
`BitVec.ofBool c = 0#1`). -/
@[simp high] theorem ternary_ofBitVec_ofBool (c : Bool) (a b : LVec) :
    ternary (ofBitVec (BitVec.ofBool c)) a b = if c then a else b := by
  cases c <;> simp

/-! ## Arithmetic and comparisons -/

attribute [simp] add_ofBitVec mul_ofBitVec

/-- `-` of known vectors is `BitVec` subtraction (the `Obs.lean` twins are
`LVec.add_ofBitVec` and `LVec.mul_ofBitVec`, made `@[simp]` here). -/
@[simp] theorem sub_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).sub (ofBitVec y) = ofBitVec (x - y) := by
  simp only [LVec.sub, toNat?_ofBitVec, arithWidth, width_ofBitVec, Nat.max_self]
  rw [ofBitVec, BitVec.toNat_sub, ofNat_emod, Nat.add_comm]

/-- Unsigned `<` of known vectors. -/
@[simp] theorem lt_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).lt (ofBitVec y) = Logic.ofBool (decide (x < y)) := by
  simp [LVec.lt, relOp, BitVec.lt_def, Logic.ofBool]

/-- Unsigned `<=` of known vectors. -/
@[simp] theorem le_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).le (ofBitVec y) = Logic.ofBool (decide (x ≤ y)) := by
  simp [LVec.le, relOp, BitVec.le_def, Logic.ofBool]

/-- Unsigned `>` of known vectors. -/
@[simp] theorem gt_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).gt (ofBitVec y) = Logic.ofBool (decide (y < x)) := by
  simp [LVec.gt, relOp, BitVec.lt_def, Logic.ofBool]

/-- Unsigned `>=` of known vectors. -/
@[simp] theorem ge_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).ge (ofBitVec y) = Logic.ofBool (decide (y ≤ x)) := by
  simp [LVec.ge, relOp, BitVec.le_def, Logic.ofBool]

/-- `===` of known vectors. -/
@[simp] theorem eqCase_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).eqCase (ofBitVec y) = Logic.ofBool (decide (x = y)) := by
  by_cases h : x = y <;> simp [eqCase, h, Logic.ofBool]

/-- `!==` of known vectors. -/
@[simp] theorem neCase_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).neCase (ofBitVec y) = Logic.ofBool (!decide (x = y)) := by
  simp [neCase]

/-- `==` of known vectors (no `x` arises). -/
@[simp] theorem eqLogical_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).eqLogical (ofBitVec y) = Logic.ofBool (decide (x = y)) := by
  have hk : ∀ b : Bool, (Logic.ofBool b).isKnown = true := by intro b; cases b <;> rfl
  unfold eqLogical
  simp only [width_ofBitVec, ne_eq, not_true_eq_false, if_false, allKnown_ofBitVec,
    Bool.and_self, if_true]
  split
  · rename_i h
    rw [Array.any_eq_true] at h
    simp [ofBitVec_bits, Array.getElem_zip, hk] at h
    have : x ≠ y := by
      rintro rfl; obtain ⟨i, _, hne⟩ := h; exact hne rfl
    simp [this]
  · rename_i h
    rw [Array.any_eq_true] at h
    simp [ofBitVec_bits, Array.getElem_zip, hk] at h
    have : x = y := BitVec.eq_of_getLsbD_eq h
    simp [this]

/-- `!=` of known vectors. -/
@[simp] theorem neLogical_ofBitVec {w : Nat} (x y : BitVec w) :
    (ofBitVec x).neLogical (ofBitVec y) = Logic.ofBool (!decide (x = y)) := by
  simp [neLogical]

end LVec

/-! ## Operator dispatch (`evalBinOp`/`evalUnaryOp`/`evalRedOp` at a constructor) -/

@[simp] theorem evalBinOp_add (a b : LVec) : evalBinOp .add a b = a.add b := rfl
@[simp] theorem evalBinOp_sub (a b : LVec) : evalBinOp .sub a b = a.sub b := rfl
@[simp] theorem evalBinOp_mul (a b : LVec) : evalBinOp .mul a b = a.mul b := rfl
@[simp] theorem evalBinOp_and (a b : LVec) : evalBinOp .and a b = a.and b := rfl
@[simp] theorem evalBinOp_or (a b : LVec) : evalBinOp .or a b = a.or b := rfl
@[simp] theorem evalBinOp_xor (a b : LVec) : evalBinOp .xor a b = a.xor b := rfl
@[simp] theorem evalBinOp_eq (a b : LVec) : evalBinOp .eq a b = .ofLogic (a.eqLogical b) := rfl
@[simp] theorem evalBinOp_ne (a b : LVec) : evalBinOp .ne a b = .ofLogic (a.neLogical b) := rfl
@[simp] theorem evalBinOp_caseEq (a b : LVec) :
    evalBinOp .caseEq a b = .ofLogic (a.eqCase b) := rfl
@[simp] theorem evalBinOp_caseNe (a b : LVec) :
    evalBinOp .caseNe a b = .ofLogic (a.neCase b) := rfl
@[simp] theorem evalBinOp_lt (a b : LVec) : evalBinOp .lt a b = .ofLogic (a.lt b) := rfl
@[simp] theorem evalBinOp_le (a b : LVec) : evalBinOp .le a b = .ofLogic (a.le b) := rfl
@[simp] theorem evalBinOp_gt (a b : LVec) : evalBinOp .gt a b = .ofLogic (a.gt b) := rfl
@[simp] theorem evalBinOp_ge (a b : LVec) : evalBinOp .ge a b = .ofLogic (a.ge b) := rfl
@[simp] theorem evalUnaryOp_bnot (a : LVec) : evalUnaryOp .bnot a = a.not := rfl
@[simp] theorem evalRedOp_or (a : LVec) : evalRedOp .or a = a.redOr := rfl
@[simp] theorem evalRedOp_and (a : LVec) : evalRedOp .and a = a.redAnd := rfl
@[simp] theorem evalRedOp_xor (a : LVec) : evalRedOp .xor a = a.redXor := rfl
@[simp] theorem evalRedOp_nor (a : LVec) : evalRedOp .nor a = a.redOr.not := rfl
@[simp] theorem evalRedOp_nand (a : LVec) : evalRedOp .nand a = a.redAnd.not := rfl
@[simp] theorem evalRedOp_xnor (a : LVec) : evalRedOp .xnor a = a.redXor.not := rfl

/-! ## `evalPure2` on known operands (compositional forms)

Not `@[simp]`: each takes its operands' `.ok (ofBitVec _)` facts as
hypotheses. Under `simp`, the same results come from `Pure2`'s equation
lemmas plus the value lemmas above (see `sv2_known`). -/

section Compositional

variable {st : SvState}

/-- `readSignal` of a bound name. -/
theorem readSignal_of_lookup {n : String} {v : LVec} (h : SvState.lookup st n = some v) :
    readSignal st n = .ok v := by
  simp only [readSignal, h]

/-- An identifier holding a known value. -/
theorem evalPure2_ident_ofBitVec {n : String} {w : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) :
    evalPure2 st (.ident n) = .ok (LVec.ofBitVec x) :=
  evalPure2_ident_of_lookup h

/-- A known literal. -/
theorem evalPure2_lit_ofBitVec {w : Nat} (x : BitVec w) :
    evalPure2 st (.lit (LVec.ofBitVec x)) = .ok (LVec.ofBitVec x) := rfl

/-- In-range part-select of a known operand. -/
theorem evalPure2_slice_ofBitVec {e : Expr2} {w lo k : Nat} {x : BitVec w}
    (h : evalPure2 st e = .ok (LVec.ofBitVec x)) (hr : lo + k ≤ w) :
    evalPure2 st (.slice e lo k) = .ok (LVec.ofBitVec (x.extractLsb' lo k)) := by
  simp only [evalPure2_slice, h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    LVec.extract_ofBitVec x hr]

/-- In-range bit-select of a known operand. -/
theorem evalPure2_bit_ofBitVec {e : Expr2} {w i : Nat} {x : BitVec w}
    (h : evalPure2 st e = .ok (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice e i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) := by
  simp only [evalPure2_slice, h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    LVec.extract_one_ofBitVec x hi]

/-- A binary node over known operands, given the operator's value. -/
theorem evalPure2_binary_ofBitVec {op : BinOp} {l r : Expr2} {w : Nat} {x y : BitVec w}
    {z : LVec} (hl : evalPure2 st l = .ok (LVec.ofBitVec x))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec y))
    (hz : evalBinOp op (LVec.ofBitVec x) (LVec.ofBitVec y) = z) :
    evalPure2 st (.binary op l r) = .ok z := by
  simp only [evalPure2_binary, hl, hr, Pure2.res_ok_bind, Pure2.res_pure_eq, hz]

/-- `&` node over known operands. -/
theorem evalPure2_and_ofBitVec {l r : Expr2} {w : Nat} {x y : BitVec w}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.binary .and l r) = .ok (LVec.ofBitVec (x &&& y)) :=
  evalPure2_binary_ofBitVec hl hr (LVec.and_ofBitVec x y)

/-- `|` node over known operands. -/
theorem evalPure2_or_ofBitVec {l r : Expr2} {w : Nat} {x y : BitVec w}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.binary .or l r) = .ok (LVec.ofBitVec (x ||| y)) :=
  evalPure2_binary_ofBitVec hl hr (LVec.or_ofBitVec x y)

/-- `^` node over known operands. -/
theorem evalPure2_xor_ofBitVec {l r : Expr2} {w : Nat} {x y : BitVec w}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.binary .xor l r) = .ok (LVec.ofBitVec (x ^^^ y)) :=
  evalPure2_binary_ofBitVec hl hr (LVec.xor_ofBitVec x y)

/-- `+` node over known operands. -/
theorem evalPure2_add_ofBitVec {l r : Expr2} {w : Nat} {x y : BitVec w}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.binary .add l r) = .ok (LVec.ofBitVec (x + y)) :=
  evalPure2_binary_ofBitVec hl hr (LVec.add_ofBitVec x y)

/-- `-` node over known operands. -/
theorem evalPure2_sub_ofBitVec {l r : Expr2} {w : Nat} {x y : BitVec w}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.binary .sub l r) = .ok (LVec.ofBitVec (x - y)) :=
  evalPure2_binary_ofBitVec hl hr (LVec.sub_ofBitVec x y)

/-- `*` node over known operands. -/
theorem evalPure2_mul_ofBitVec {l r : Expr2} {w : Nat} {x y : BitVec w}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.binary .mul l r) = .ok (LVec.ofBitVec (x * y)) :=
  evalPure2_binary_ofBitVec hl hr (LVec.mul_ofBitVec x y)

/-- `~` node over a known operand. -/
theorem evalPure2_bnot_ofBitVec {e : Expr2} {w : Nat} {x : BitVec w}
    (h : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    evalPure2 st (.unary .bnot e) = .ok (LVec.ofBitVec (~~~x)) := by
  simp only [evalPure2_unary, h, Pure2.res_ok_bind, Pure2.res_pure_eq, evalUnaryOp_bnot,
    LVec.not_ofBitVec]

/-- `resize` node over a known operand. -/
theorem evalPure2_resize_ofBitVec {e : Expr2} {w : Nat} {x : BitVec w} (w' : Nat)
    (h : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    evalPure2 st (.resize w' e) = .ok (LVec.ofBitVec (x.setWidth w')) := by
  simp only [evalPure2_resize, h, Pure2.res_ok_bind, Pure2.res_pure_eq, LVec.resizeU_ofBitVec]

/-- Replication node over a known operand. -/
theorem evalPure2_repl_ofBitVec {e : Expr2} {w : Nat} {x : BitVec w} (n : Nat)
    (h : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    evalPure2 st (.repl n e) = .ok (LVec.ofBitVec (x.replicate n)) := by
  simp only [evalPure2_repl, h, Pure2.res_ok_bind, Pure2.res_pure_eq, LVec.replVec_ofBitVec]

/-- Two-part concatenation node over known operands (`l` = MSB part). -/
theorem evalPure2_concat_ofBitVec {l r : Expr2} {n m : Nat} {x : BitVec n} {y : BitVec m}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec x)) (hr : evalPure2 st r = .ok (LVec.ofBitVec y)) :
    evalPure2 st (.concat #[l, r]) = .ok (LVec.ofBitVec (x ++ y)) := by
  simp [hl, hr]

/-- Reduction node over a known operand (then `LVec.redOr/redAnd/redXor_ofBitVec`). -/
theorem evalPure2_reduce_ofBitVec {e : Expr2} {w : Nat} {x : BitVec w} (op : RedOp)
    (h : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    evalPure2 st (.reduce op e) = .ok (.ofLogic (evalRedOp op (LVec.ofBitVec x))) := by
  simp only [evalPure2_reduce, h, Pure2.res_ok_bind, Pure2.res_pure_eq]

/-- Ternary node with a known 1-bit condition (both arms must evaluate —
`evalPure2` evaluates both, like the interpreter). -/
theorem evalPure2_ternary_ofBool {c t f : Expr2} {b : Bool} {vt vf : LVec}
    (hc : evalPure2 st c = .ok (LVec.ofBitVec (BitVec.ofBool b)))
    (ht : evalPure2 st t = .ok vt) (hf : evalPure2 st f = .ok vf) :
    evalPure2 st (.ternary c t f) = .ok (if b then vt else vf) := by
  simp only [evalPure2_ternary, hc, ht, hf, Pure2.res_ok_bind, Pure2.res_pure_eq,
    LVec.ternary_ofBitVec_ofBool]

end Compositional

/-! ## The `sv2_known` simp entry point -/

/-- Side-condition discharger of `sv2_known`: range facts (`lo + k ≤ w`,
`i < w`) by `assumption`/`omega` from the context, anything else by
`simp_all`. -/
macro "sv2_disch" : tactic => `(tactic| first | assumption | omega | simp_all)

/-- `sv2_known [h₁, …]`: `simp` with the known-value calculus of
`Known2.lean` (the global `@[simp]` set listed in the module docstring),
`readSignal` unfolding, the `extractLsb'_one_eq_ofBool` backstop, and the
extra facts `hᵢ` (typically `SvState.lookup st "a" = some (LVec.ofBitVec x)`),
with range side conditions discharged by `sv2_disch`. Reduces `evalPure2` of
a gate-level expression over known signals to `.ok (LVec.ofBitVec <BitVec
term>)`, and closes the goal when it is such an equation. -/
syntax (name := sv2Known) "sv2_known" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| sv2_known $[[$args,*]]?) => do
    let extra := (args.map (·.getElems)).getD #[]
    `(tactic| simp (disch := sv2_disch) [readSignal, extractLsb'_one_eq_ofBool, $extra,*])

/-! ## Acceptance examples -/

section Acceptance

/-- A 3-gate expression over bit-select reads `a[i]`, `b[i]`, `c[i]` of known
`N`-bit signals, at symbolic `N` and `i`. -/
example (st : SvState) {N : Nat} (x y z : BitVec N) (i : Nat) (hi : i < N)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "c" = some (LVec.ofBitVec z)) :
    evalPure2 st (.binary .or (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
        (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "c") i 1))) =
      .ok (LVec.ofBitVec (BitVec.ofBool
        (x.getLsbD i && y.getLsbD i || (x.getLsbD i ^^ z.getLsbD i)))) := by
  sv2_known [ha, hb, hc]

/-- The same expression over whole known vectors: `ofBitVec` of a `BitVec`
expression. -/
example (st : SvState) {N : Nat} (x y z : BitVec N)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "c" = some (LVec.ofBitVec z)) :
    evalPure2 st (.binary .or (.binary .and (.ident "a") (.ident "b"))
        (.binary .xor (.ident "a") (.ident "c"))) =
      .ok (LVec.ofBitVec (x &&& y ||| (x ^^^ z))) := by
  sv2_known [ha, hb, hc]

/-- **Full adder** at symbolic bits: sum and carry are `BitVec.ofBool` of the
`Bool` xor/and/or. -/
example (st : SvState) (p q r : Bool)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec (BitVec.ofBool p)))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec (BitVec.ofBool q)))
    (hc : SvState.lookup st "c" = some (LVec.ofBitVec (BitVec.ofBool r))) :
    evalPure2 st (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "c")) =
        .ok (LVec.ofBitVec (BitVec.ofBool (p ^^ q ^^ r))) ∧
      evalPure2 st (.binary .or (.binary .and (.ident "a") (.ident "b"))
          (.binary .and (.ident "c") (.binary .xor (.ident "a") (.ident "b")))) =
        .ok (LVec.ofBitVec (BitVec.ofBool (p && q || r && (p ^^ q)))) := by
  sv2_known [ha, hb, hc]

/-- The ripple-adder carry `(a[i] & b[i]) | (c[i] & (a[i] ^ b[i]))` over an
`N+1`-bit carry chain `c` (range side condition `i < N + 1` by `omega`). -/
example (st : SvState) {N : Nat} (x y : BitVec N) (z : BitVec (N + 1)) (i : Nat) (hi : i < N)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "c" = some (LVec.ofBitVec z)) :
    evalPure2 st (.binary .or (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
        (.binary .and (.slice (.ident "c") i 1)
          (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1)))) =
      .ok (LVec.ofBitVec (BitVec.ofBool
        (x.getLsbD i && y.getLsbD i || z.getLsbD i && (x.getLsbD i ^^ y.getLsbD i)))) := by
  sv2_known [ha, hb, hc]

/-- Mixed-width concatenation (source order = MSB first, right-nested `++`)
with a part-select and a reduction. -/
example (st : SvState) {N : Nat} (x y : BitVec N) (hN : 4 ≤ N)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    evalPure2 st (.concat #[.slice (.ident "a") 0 4, .binary .xor (.ident "a") (.ident "b"),
        .reduce .and (.ident "b")]) =
      .ok (LVec.ofBitVec (x.extractLsb' 0 4 ++ ((x ^^^ y) ++
        BitVec.ofBool (decide (y = BitVec.allOnes N))))) := by
  sv2_known [ha, hb]

/-- A known 1-bit condition selecting between arithmetic and negation. -/
example (st : SvState) {N : Nat} (x y : BitVec N) (c : Bool)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "c" = some (LVec.ofBitVec (BitVec.ofBool c))) :
    evalPure2 st (.ternary (.ident "c") (.resize N (.binary .add (.ident "a") (.ident "b")))
        (.unary .bnot (.ident "a"))) =
      .ok (LVec.ofBitVec (if c then x + y else ~~~x)) := by
  sv2_known [ha, hb, hc]

/-- Literals in `LVec.ofNat` form join the calculus. -/
example (st : SvState) (p : Bool)
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec (BitVec.ofBool p))) :
    evalPure2 st (.concat #[.lit (LVec.ofNat 1 0), .binary .or (.ident "a") (.lit (.ofNat 1 0))]) =
      .ok (LVec.ofBitVec (0#1 ++ BitVec.ofBool p)) := by
  sv2_known [ha]

/-- Select-write then read back the written bit. -/
example {N : Nat} (x : BitVec N) (b : Bool) (i : Nat) (hi : i < N) :
    ((LVec.ofBitVec x).insertAt i (LVec.ofBitVec (BitVec.ofBool b))).extract i 1 =
      LVec.ofBitVec (BitVec.ofBool b) := by
  sv2_known

end Acceptance

end LeanModels.Sv
