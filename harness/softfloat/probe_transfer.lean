/-
SOFTFLOAT — LAYER 3 FEASIBILITY PROBE.

Core's `UnpackedFloat` docstring instructs downstream users to build a library
"completely separately", prove core's operations "equivalent" to it, and then
"transfer lemmas from the library to the `Float` and `Float32` types".

THE QUESTION THIS PROBE ANSWERS: what does one transfer COST?  The worry is
that the packed types are per-width duplicates (§3.5.1 clause 3), so the
transfer might cost one lemma per operation PER WIDTH.  Measured below: it does
not, because `Float.Model.op` is DEFINITIONALLY `pack ∘ op binary64 ∘ unpack`.

Expected: ZERO errors.

RUN:  tools/check.sh harness/softfloat/probe_transfer.lean
-/
import Init.Data.Float.Model

open Float.Model

/-! ## 1. The packed ops are definitionally the unpacked ops — `rfl`, both widths -/

example (a b : Float.Model) :
    a.add b = Float.Model.pack (UnpackedFloat.add Format.binary64 a.unpack b.unpack) := rfl
example (a b : Float.Model) :
    a.div b = Float.Model.pack (UnpackedFloat.div Format.binary64 a.unpack b.unpack) := rfl
example (a b : Float32.Model) :
    a.add b = Float32.Model.pack (UnpackedFloat.add Format.binary32 a.unpack b.unpack) := rfl
example (a : Float.Model) :
    a.toInt64 = a.unpack.toInt64 := rfl

/-! ## 2. A PARAMETRIC lemma, and its transfer to BOTH packed widths -/

/-- The parametric fact (this is layer 2's shape: one statement, every format). -/
theorem add_nan_left (fmt : Format) (x : UnpackedFloat) :
    UnpackedFloat.add fmt .notANumber x = .notANumber := rfl

-- transfer to binary64 — ONE line
theorem model_add_nan (a b : Float.Model) (h : a.unpack = .notANumber) :
    a.add b = Float.Model.pack .notANumber := by
  show Float.Model.pack (UnpackedFloat.add Format.binary64 a.unpack b.unpack) = _
  rw [h, add_nan_left]

-- transfer to binary32 — ONE line, and the SAME line
theorem model32_add_nan (a b : Float32.Model) (h : a.unpack = .notANumber) :
    a.add b = Float32.Model.pack .notANumber := by
  show Float32.Model.pack (UnpackedFloat.add Format.binary32 a.unpack b.unpack) = _
  rw [h, add_nan_left]

/-! ## 3. And all the way out to `Float` itself -/

example (a b : Float) : a + b = Float.ofModel (a.toModel.add b.toModel) := rfl
example (a : Float) : a.toModel.toInt64 = a.toModel.unpack.toInt64 := rfl

/-- The transfer reaches the user-facing type, still in one line. -/
theorem float_add_nan (a b : Float) (h : a.toModel.unpack = .notANumber) :
    a + b = Float.ofModel (Float.Model.pack .notANumber) := by
  show Float.ofModel (Float.Model.pack
    (UnpackedFloat.add Format.binary64 a.toModel.unpack b.toModel.unpack)) = _
  rw [h, add_nan_left]

#print axioms model_add_nan
#print axioms model32_add_nan
#print axioms float_add_nan
