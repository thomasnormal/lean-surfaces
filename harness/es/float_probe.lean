/-
  harness/es/float_probe.lean — is core `Float` kernel-reducible on the pin?

  `docs/completeness.md` §6 defers the Python tier's float rung on the
  recorded grounds that *"Lean's `Float` is not kernel-reducible, so
  `#py_check` and every captured `rfl` run would break"*.  The ECMAScript
  tier cannot inherit that deferral — a JS Number IS a binary64 — so
  `docs/es-charter.md` §4.2(a) re-measures the premise instead of quoting
  it, and this file is the measurement.

  Deliberately IMPORT-FREE: this is Lean core only, which is exactly the
  setting `AGENTS.md` pins ("core only, no packages").  It therefore needs
  no build and cannot break one:

      lean harness/es/float_probe.lean          # silence = every check passed

  Every line below is a KERNEL claim.  `rfl` is definitional equality
  checked by the kernel; `#guard` evaluates a `Bool` in the kernel and
  fails loudly with the expression printed.  If core `Float` were opaque,
  none of them would elaborate.

  MEASURED on `leanprover/lean4:v4.33.0-rc1` (2026-08-22): all pass.
  `Float` is a structure over `Float.Model`, itself a `UInt64` of bits
  plus a proof of `Float.Model.Format.binary64.Valid` — a bit-level
  IEEE-754 model with `DecidableEq`, 27 files and 2,918 lines under
  `Init/Data/Float`, carrying `round`, `roundToNearestEven`,
  `roundedMantissa`, `roundToInt` and `roundWithAccuracy`.

  What this does NOT show, and §4.2(a) is careful about: those 2,918 lines
  carry THREE theorems.  Evaluation reduces; the algebra ABOUT rounding
  does not exist yet.  Layer 1 is free, Layer 2 is the work.
-/

/-! ## 1 Kernel defeq decides float arithmetic -/

example : (1.5 : Float) + 2.5 = 4.0 := by rfl

/-- The decisive row: binary64 ROUNDING, not just exact-in-range arithmetic.
    A model that computed over the rationals would answer `0.3` here. -/
example : (0.1 : Float) + 0.2 = 0.30000000000000004 := by rfl

/-! ## 2 `#guard` — kernel Bool evaluation -/

#guard (1.5 : Float) + 2.5 == 4.0
#guard ((0.1 : Float) + 0.2 == 0.3) == false

-- The two non-finite classes, and NaN's defining inequality.
#guard (1.0 : Float) / 0.0 == (1.0 : Float) / 0.0
#guard ((0.0 : Float) / 0.0 == (0.0 : Float) / 0.0) == false

-- Absorption: 1 is below the ulp of 1e16, so the addition is a no-op.
#guard (1.0 : Float) + 1e16 == 1e16

#guard Float.toString ((0.1 : Float) + 0.2) == "0.300000"

/-! ## 3 The equality a captured `rfl` run would need -/

example : ((1.5 : Float) + 2.5 == 4.0) = true := by rfl
