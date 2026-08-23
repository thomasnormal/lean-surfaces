/-
# SoftFloat, layer 3 — TRANSFER

Core commissioned this layer in its own words (`docs/softfloat-charter.md`
§0.2): build the library separately, prove core's operations **equivalent**,
then **transfer** lemmas to `Float` and `Float32`.

§3.5.1 clause (3) records that core's parametricity **stops at the packed
boundary**: `Float.Model` and `Float32.Model` take zero parameters and
hard-code `binary64`/`binary32`. The obvious reading is that every transfer
must therefore be written twice, forever.

**IT DOES NOT.** This file restores parametricity ABOVE core's packed boundary
by making the two wrappers INSTANCES of a `Packed` class — which is §3.5.1
clause (1)'s own move ("binary32/64 are instances, never separate
definitions") applied one level up, to the wrappers instead of to the formats.
Each theorem below is stated ONCE and lands on both widths with no new proof.

**The acid test is `packed_stays_definitional`**: `rfl` still closes through
the class at a concrete instance. Had it not, the class would be an
abstraction barrier rather than a view, and the transfer would buy nothing.
-/
import LeanModels.SoftFloat.Theorems

namespace LeanModels.SoftFloat

open Float.Model
open Float.Model.UnpackedFloat (Sign)

/--
A packed IEEE format: a concrete bit-level type together with the `Format` it
packs and the pack/unpack pair, plus the equations saying its operations ARE
the width-parametric ones conjugated by that pair.

Every equation is `rfl` at both of core's instances — they are recorded as
fields rather than proved per use so that a theorem can be stated once over
`α`. A future packed width (binary16, binary128) becomes an instance and
inherits every theorem below without reproving any of them.
-/
class Packed (α : Type) [Add α] [Sub α] [Mul α] [Div α] where
  /-- The IEEE 754-2019 §3.3 format this type packs. -/
  fmt : Format
  /-- Unpack to the width-parametric representation. -/
  unpack : α → UnpackedFloat
  /-- Pack from the width-parametric representation. -/
  pack : UnpackedFloat → α
  /-- Packed `+` is the parametric `add`, conjugated. -/
  add_def : ∀ a b : α, a + b = pack (UnpackedFloat.add fmt (unpack a) (unpack b))
  /-- Packed `-` is the parametric `sub`, conjugated. -/
  sub_def : ∀ a b : α, a - b = pack (UnpackedFloat.sub fmt (unpack a) (unpack b))
  /-- Packed `*` is the parametric `mul`, conjugated. -/
  mul_def : ∀ a b : α, a * b = pack (UnpackedFloat.mul fmt (unpack a) (unpack b))
  /-- Packed `/` is the parametric `div`, conjugated. -/
  div_def : ∀ a b : α, a / b = pack (UnpackedFloat.div fmt (unpack a) (unpack b))
  /-- The packed square root. -/
  sqrt : α → α
  /-- Packed `sqrt` is the parametric one, conjugated. -/
  sqrt_def : ∀ a : α, sqrt a = pack (UnpackedFloat.sqrt fmt (unpack a))
  /-- The packed comparison (IEEE 754-2019 §5.11; `none` is "unordered"). -/
  compare : α → α → Option Ordering
  /-- Packed comparison is the parametric one. -/
  compare_def : ∀ a b : α, compare a b = (unpack a).compare (unpack b)
  /-- Conversion to a 64-bit signed integer, clamping out of range. -/
  toInt64 : α → Int64
  /-- The conversion is the parametric one; note it takes NO format. -/
  toInt64_def : ∀ a : α, toInt64 a = (unpack a).toInt64

instance : Packed Float.Model where
  fmt := Format.binary64
  unpack := Float.Model.unpack
  pack := Float.Model.pack
  add_def := fun _ _ => rfl
  sub_def := fun _ _ => rfl
  mul_def := fun _ _ => rfl
  div_def := fun _ _ => rfl
  sqrt := Float.Model.sqrt
  sqrt_def := fun _ => rfl
  compare := Float.Model.compare
  compare_def := fun _ _ => rfl
  toInt64 := Float.Model.toInt64
  toInt64_def := fun _ => rfl

instance : Packed Float32.Model where
  fmt := Format.binary32
  unpack := Float32.Model.unpack
  pack := Float32.Model.pack
  add_def := fun _ _ => rfl
  sub_def := fun _ _ => rfl
  mul_def := fun _ _ => rfl
  div_def := fun _ _ => rfl
  sqrt := Float32.Model.sqrt
  sqrt_def := fun _ => rfl
  compare := Float32.Model.compare
  compare_def := fun _ _ => rfl
  toInt64 := Float32.Model.toInt64
  toInt64_def := fun _ => rfl

section
variable {α : Type} [Add α] [Sub α] [Mul α] [Div α] [Packed α]

/-! ## The IEEE rows, transferred — ONE statement, EVERY packed width -/

/-- IEEE 754-2019 §6.2: NaN propagates through `+`, at every packed format. -/
theorem packed_add_nan (a b : α) (h : Packed.unpack a = .notANumber) :
    a + b = Packed.pack (α := α) .notANumber := by
  rw [Packed.add_def, h, add_nan_left]

/-- IEEE 754-2019 §6.3: `(+0) + (−0) = +0`, at every packed format. -/
theorem packed_add_zeros (a b : α)
    (ha : Packed.unpack a = .zero .positive) (hb : Packed.unpack b = .zero .negative) :
    a + b = Packed.pack (α := α) (.zero .positive) := by
  rw [Packed.add_def, ha, hb, add_zero_opposite_signs]

/-- IEEE 754-2019 §7.2: `(+∞) + (−∞)` is invalid, at every packed format. -/
theorem packed_add_inf_opposite (a b : α)
    (ha : Packed.unpack a = .infinity .positive) (hb : Packed.unpack b = .infinity .negative) :
    a + b = Packed.pack (α := α) .notANumber := by
  rw [Packed.add_def, ha, hb, add_inf_opposite]

/-- IEEE 754-2019 §7.2: `0/0` is invalid, at every packed format. -/
theorem packed_div_zero_zero (a b : α) (s₁ s₂ : Sign)
    (ha : Packed.unpack a = .zero s₁) (hb : Packed.unpack b = .zero s₂) :
    a / b = Packed.pack (α := α) .notANumber := by
  rw [Packed.div_def, ha, hb, div_zero_zero]

/-- IEEE 754-2019 §7.3: finite nonzero over zero is a signed infinity. -/
theorem packed_div_by_zero (a b : α) (s₁ s₂ : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (ha : Packed.unpack a = .finite s₁ m e hm) (hb : Packed.unpack b = .zero s₂) :
    a / b = Packed.pack (α := α) (.infinity (s₁ / s₂)) := by
  rw [Packed.div_def, ha, hb, div_by_zero]

/-- IEEE 754-2019 §7.2: `√` of a negative finite is invalid. -/
theorem packed_sqrt_neg (a : α) (m : Nat) (e : Int) (hm : 0 < m)
    (ha : Packed.unpack a = .finite .negative m e hm) :
    Packed.sqrt a = Packed.pack (α := α) .notANumber := by
  rw [Packed.sqrt_def, ha, sqrt_neg]

/-- IEEE 754-2019 §5.11: NaN is unordered with everything. -/
theorem packed_compare_nan (a b : α) (h : Packed.unpack a = .notANumber) :
    Packed.compare a b = none := by
  rw [Packed.compare_def, h, compare_nan]

/-! ## THE ES DELIVERY — and the CLAMP is in the statement, on purpose

`toInt_eq_truncate` (`Theorems.lean`) says core's conversion is truncation of
the exact value. The packed `toInt64` additionally **clamps**, and this theorem
says so **in its conclusion** rather than in a comment.

That is deliberate. The ES lane's `%` site was a live bug precisely because the
clamp was invisible at the call site (`docs/backlog/es.md` 2026-08-23-es-1): a
large quotient silently produced a wrong remainder that every in-range test
passed. A theorem whose conclusion names `Int64.ofIntClamp` cannot be used for
a modular conversion (ECMA-262 §7.1.6 `ToInt32` reduces mod 2³²) without the
mismatch being visible in the goal.
-/

/--
IEEE 754-2019 §5.8 `convertToIntegerTowardZero`, at the packed layer, **with
the clamp exposed**: the packed conversion is the truncation of the exact
value, then clamped into `Int64`.

For a MODULAR conversion, do not use this — truncate with `toInt_eq_truncate`
and reduce, which is why that theorem is stated over the exact value.
-/
theorem packed_toInt64_eq_clamped_truncate (a : α) (q : Q)
    (h : valQ (Packed.unpack a) = some q) :
    Packed.toInt64 a = Int64.ofIntClamp q.truncate := by
  rw [Packed.toInt64_def]
  show Int64.ofIntClamp (UnpackedFloat.toInt _ _ (Packed.unpack a)) = _
  rw [toInt_eq_truncate h]

end

/-! ## THE ACID TEST: the class is a VIEW, not a barrier -/

/-- `rfl` still closes through the class at a concrete instance. -/
theorem packed_stays_definitional (a b : Float.Model) :
    Packed.pack (α := Float.Model)
      (UnpackedFloat.add Format.binary64 (Packed.unpack a) (Packed.unpack b)) = a.add b := rfl

/-- And at the other width, by the same `rfl`. -/
theorem packed32_stays_definitional (a b : Float32.Model) :
    Packed.pack (α := Float32.Model)
      (UnpackedFloat.add Format.binary32 (Packed.unpack a) (Packed.unpack b)) = a.add b := rfl

/-! ## Each theorem lands on BOTH concrete widths with NO new proof -/

example (a b : Float.Model) (h : a.unpack = .notANumber) :
    a + b = Float.Model.pack .notANumber := packed_add_nan a b h
example (a b : Float32.Model) (h : a.unpack = .notANumber) :
    a + b = Float32.Model.pack .notANumber := packed_add_nan a b h
example (a : Float.Model) (q : Q) (h : valQ a.unpack = some q) :
    a.toInt64 = Int64.ofIntClamp q.truncate := packed_toInt64_eq_clamped_truncate a q h
example (a : Float32.Model) (q : Q) (h : valQ a.unpack = some q) :
    a.toInt64 = Int64.ofIntClamp q.truncate := packed_toInt64_eq_clamped_truncate a q h

#print axioms packed_add_nan
#print axioms packed_div_by_zero
#print axioms packed_sqrt_neg
#print axioms packed_toInt64_eq_clamped_truncate
#print axioms packed_stays_definitional
#print axioms packed32_stays_definitional

end LeanModels.SoftFloat
