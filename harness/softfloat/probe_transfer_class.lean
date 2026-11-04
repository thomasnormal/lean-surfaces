/-
SOFTFLOAT LAYER 3 — DESIGN BAKE-OFF for the transfer generator.

§3.8 measured that a transfer costs one mechanical `show` per (theorem, width),
and concluded layer 3 should be GENERATED rather than written twice per fact.
There are two ways to generate it, and they are not equally good:

  (a) a SIMP SET of `rfl` unfolding lemmas — one per (op, width).  Mechanical,
      but it is still 2N lemmas and the duplication is real, just cheap.
  (b) a CLASS over the packed type, so `Float.Model` and `Float32.Model` become
      INSTANCES and each transfer theorem is stated ONCE.

(b) is what §3.5.1 clause (1) asks for one level up: the clause says binary32/64
are instances of a general `Format`, and (b) says the PACKED WRAPPERS are
instances of a general packed type.  If it works, clause (3)'s per-width
duplication is paid exactly once, structurally, instead of per theorem forever.

THE RISK, and it is why this is a probe: the class's `pack`/`unpack` fields must
stay DEFINITIONALLY the real ones, or `rfl` stops closing at the instances and
(b) buys nothing.

VERDICT: (b) WINS, and it is landed as `LeanModels/SoftFloat/Transfer.lean`.
The acid test at the bottom passes — `rfl` still closes through the class — so
the class is a VIEW, not a barrier.

AND THIS PROBE COST A LESSON WORTH KEEPING.  Its first version omitted the
`[Add α]` requirement, so `HAdd α α ?m` could not be synthesized and the class
FIELDS failed to elaborate.  `#print axioms packed_add_nan` then printed
"does not depend on any axioms" -- the cleanest line the command emits --
about a theorem whose STATEMENT had never elaborated, in a file carrying
twelve errors.  That is family-architecture §0.1 II(a)'s lying axiom print,
reproduced live.  The fix is the `[Add α] [Div α]` binders below.

Expected: ZERO errors.
RUN:  tools/check.sh harness/softfloat/probe_transfer_class.lean
-/
import Init.Data.Float.Model

open Float.Model

namespace SoftFloatProbe

/-! ## (b) THE CLASS -/

/--
A packed IEEE format: a concrete type carrying bits, its `Format`, and the
pack/unpack pair.  `Float.Model` and `Float32.Model` are the two instances core
ships; the point of the class is that layer-2 theorems transfer to BOTH from a
single statement.
-/
class Packed (α : Type) [Add α] [Div α] where
  /-- The IEEE format this type packs. -/
  fmt : Format
  /-- Unpack to the width-parametric representation. -/
  unpack : α → UnpackedFloat
  /-- Pack from the width-parametric representation. -/
  pack : UnpackedFloat → α
  /-- The packed addition is the parametric one, conjugated. -/
  add_def : ∀ a b : α, HAdd.hAdd a b = pack (UnpackedFloat.add fmt (unpack a) (unpack b))
  /-- The packed division is the parametric one, conjugated. -/
  div_def : ∀ a b : α, HDiv.hDiv a b = pack (UnpackedFloat.div fmt (unpack a) (unpack b))

instance : Packed Float.Model where
  fmt := Format.binary64
  unpack := Float.Model.unpack
  pack := Float.Model.pack
  add_def := fun _ _ => rfl
  div_def := fun _ _ => rfl

instance : Packed Float32.Model where
  fmt := Format.binary32
  unpack := Float32.Model.unpack
  pack := Float32.Model.pack
  add_def := fun _ _ => rfl
  div_def := fun _ _ => rfl

/-! ## The parametric layer-2 facts (stated once, every format) -/

theorem add_nan_left (fmt : Format) (x : UnpackedFloat) :
    UnpackedFloat.add fmt .notANumber x = .notANumber := rfl

theorem div_zero_zero (fmt : Format) (s₁ s₂ : UnpackedFloat.Sign) :
    UnpackedFloat.div fmt (.zero s₁) (.zero s₂) = .notANumber := by
  cases s₁ <;> cases s₂ <;> rfl

/-! ## THE TRANSFER, STATED ONCE, COVERING BOTH WIDTHS -/

/-- IEEE 754-2019 §6.2, at every packed format at once. -/
theorem packed_add_nan {α} [Add α] [Div α] [Packed α] (a b : α)
    (h : Packed.unpack a = .notANumber) :
    a + b = Packed.pack (α := α) .notANumber := by
  rw [Packed.add_def, h, add_nan_left]

/-- IEEE 754-2019 §7.2, at every packed format at once. -/
theorem packed_div_zero_zero {α} [Add α] [Div α] [Packed α] (a b : α) (s₁ s₂ : UnpackedFloat.Sign)
    (ha : Packed.unpack a = .zero s₁) (hb : Packed.unpack b = .zero s₂) :
    a / b = Packed.pack (α := α) .notANumber := by
  rw [Packed.div_def, ha, hb, div_zero_zero]

/-! ## …and it lands on BOTH concrete types with NO new proof -/

example (a b : Float.Model) (h : a.unpack = .notANumber) :
    a + b = Float.Model.pack .notANumber := packed_add_nan a b h

example (a b : Float32.Model) (h : a.unpack = .notANumber) :
    a + b = Float32.Model.pack .notANumber := packed_add_nan a b h

example (a b : Float.Model) (s₁ s₂ : UnpackedFloat.Sign)
    (ha : a.unpack = .zero s₁) (hb : b.unpack = .zero s₂) :
    a / b = Float.Model.pack .notANumber := packed_div_zero_zero a b s₁ s₂ ha hb

example (a b : Float32.Model) (s₁ s₂ : UnpackedFloat.Sign)
    (ha : a.unpack = .zero s₁) (hb : b.unpack = .zero s₂) :
    a / b = Float32.Model.pack .notANumber := packed_div_zero_zero a b s₁ s₂ ha hb

/-! ## THE ACID TEST: does the class stay DEFINITIONAL at the instances? -/

example (a b : Float.Model) :
    Packed.pack (α := Float.Model) (UnpackedFloat.add Format.binary64
      (Packed.unpack a) (Packed.unpack b)) = a.add b := rfl
example (a b : Float32.Model) :
    Packed.pack (α := Float32.Model) (UnpackedFloat.add Format.binary32
      (Packed.unpack a) (Packed.unpack b)) = a.add b := rfl

theorem class_stays_definitional (a b : Float.Model) :
    Packed.pack (α := Float.Model) (UnpackedFloat.add Format.binary64
      (Packed.unpack a) (Packed.unpack b)) = a.add b := rfl

#print axioms packed_add_nan
#print axioms packed_div_zero_zero
#print axioms class_stays_definitional

end SoftFloatProbe
