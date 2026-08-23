/-
SOFTFLOAT CORE CENSUS — probe A: what REDUCES.
Every line here is expected to elaborate CLEANLY (zero errors), so that any
`#print axioms` taken from it is meaningful (family-architecture §0.1 II(a)).
Probe B (sf_probe_wall.lean) holds the expected FAILURES.

RUN:  tools/check.sh harness/softfloat/probe_reduces.lean
      (case `scratch` — outside every lake library glob, core imports only, so
       rule 3's exemption applies and no build tenure is needed.)
-/
import Init.Data.Float.Model

open Float.Model

/-! ## 1. `Format` admits widths core never defines — the INSTANCE test (§3.5.1 clause 1) -/

/-- IEEE 754-2019 §3.6 binary16. Core does NOT ship this; it is an instance of core's `Format`. -/
abbrev binary16 : Format := { mantissaBitsWithoutImplicit := 10, exponentBits := 5 }
/-- IEEE 754-2019 §3.6 binary128. Core does NOT ship this either. -/
abbrev binary128 : Format := { mantissaBitsWithoutImplicit := 112, exponentBits := 15 }
/-- A width nobody would ever ask for, to show the record is genuinely unconstrained. -/
abbrev tiny : Format := { mantissaBitsWithoutImplicit := 1, exponentBits := 1 }

#guard binary16.numBits = 16
#guard binary128.numBits = 128
#guard Format.binary32.numBits = 32
#guard Format.binary64.numBits = 64
#guard tiny.numBits = 3

example : binary16.numBits = 16 := rfl
example : binary128.numBits = 128 := rfl
example : Format.binary64.numBits = 64 := rfl

-- IEEE 754-2019 §3.3 Table 3.5: bias = emax = 2^(w-1) - 1.
#guard binary16.exponentBias = 15
#guard Format.binary32.exponentBias = 127
#guard Format.binary64.exponentBias = 1023
#guard binary128.exponentBias = 16383
example : binary128.exponentBias = 16383 := by decide

/-! ## 2. The PARAMETRIC arithmetic reduces, at every width — rfl AND decide AND #guard -/

/-- Build a canonical `UnpackedFloat` for a format. -/
abbrev u (spec : Format) (n : Nat) : UnpackedFloat := UnpackedFloat.ofNat spec n

-- add, at four widths, compared through the packed bits (BitVec has DecidableEq).
example : UnpackedFloat.pack tiny        (UnpackedFloat.add tiny        (u tiny 1)        (u tiny 2))
        = UnpackedFloat.pack tiny        (u tiny 3) := rfl
example : UnpackedFloat.pack binary16    (UnpackedFloat.add binary16    (u binary16 1)    (u binary16 2))
        = UnpackedFloat.pack binary16    (u binary16 3) := rfl
example : UnpackedFloat.pack Format.binary32 (UnpackedFloat.add Format.binary32 (u Format.binary32 1) (u Format.binary32 2))
        = UnpackedFloat.pack Format.binary32 (u Format.binary32 3) := rfl
example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.add Format.binary64 (u Format.binary64 1) (u Format.binary64 2))
        = UnpackedFloat.pack Format.binary64 (u Format.binary64 3) := rfl
set_option maxRecDepth 1000 in
example : UnpackedFloat.pack binary128   (UnpackedFloat.add binary128   (u binary128 1)   (u binary128 2))
        = UnpackedFloat.pack binary128   (u binary128 3) := rfl

-- the same by `decide` (rung 2), and by `#guard` (the interpreter)
example : UnpackedFloat.pack binary16 (UnpackedFloat.add binary16 (u binary16 1) (u binary16 2))
        = UnpackedFloat.pack binary16 (u binary16 3) := by decide
#guard UnpackedFloat.pack binary16 (UnpackedFloat.add binary16 (u binary16 1) (u binary16 2))
        = UnpackedFloat.pack binary16 (u binary16 3)

-- mul / sub / div / sqrt, parametric, at a non-core width
example : UnpackedFloat.pack binary16 (UnpackedFloat.mul binary16 (u binary16 3) (u binary16 5))
        = UnpackedFloat.pack binary16 (u binary16 15) := rfl
example : UnpackedFloat.pack binary16 (UnpackedFloat.sub binary16 (u binary16 9) (u binary16 4))
        = UnpackedFloat.pack binary16 (u binary16 5) := rfl
example : UnpackedFloat.pack binary16 (UnpackedFloat.div binary16 (u binary16 12) (u binary16 4))
        = UnpackedFloat.pack binary16 (u binary16 3) := rfl
-- NOTE: `sqrt` does NOT belong here — it fails `rfl` and `decide`.  Its rows
-- live in probe_walls.lean, because this file hosts axiom prints and an axiom
-- print is meaningful ONLY from a zero-error elaboration (§0.1 II(a)).
set_option maxRecDepth 1000 in
example : UnpackedFloat.pack binary128 (UnpackedFloat.div binary128 (u binary128 12) (u binary128 4))
        = UnpackedFloat.pack binary128 (u binary128 3) := rfl

-- comparison (IEEE 754-2019 §5.11): NaN is unordered with everything, +0 = -0
#guard (UnpackedFloat.compare (u binary16 1) (u binary16 2)) == some Ordering.lt
#guard (UnpackedFloat.compare .notANumber (u binary16 2)) == none
#guard (UnpackedFloat.compare (.zero .positive) (.zero .negative)) == some Ordering.eq
example : UnpackedFloat.compare (.zero .positive) (.zero .negative) = some Ordering.eq := rfl
example : UnpackedFloat.compare (UnpackedFloat.notANumber) (UnpackedFloat.notANumber) = none := rfl

/-! ## 3. THE ES UNBLOCK CANDIDATE: a kernel-reducible float→int truncation -/

-- `UnpackedFloat.toInt64` is a plain Lean definition; unlike `Float.toInt64` it REDUCES.
example : UnpackedFloat.toInt64 (u Format.binary64 42) = (42 : Int64) := rfl
example : UnpackedFloat.toInt64 (u Format.binary64 42) = (42 : Int64) := by decide
#guard UnpackedFloat.toInt64 (u Format.binary64 42) = (42 : Int64)

-- and the whole way down from a real `Float` literal, through the packed model:
example : Float.Model.toInt64 (Float.Model.ofNat 42) = (42 : Int64) := rfl
example : (2.75 : Float).toModel.toInt64 = (2 : Int64) := rfl
example : (-2.75 : Float).toModel.toInt64 = (-2 : Int64) := rfl   -- IEEE §5.8 roundTowardZero
example : (0.0 : Float).toModel.toInt64 = (0 : Int64) := rfl

/-! ## 4. binary64 sanity: the fact that matters (family-architecture §3.5) -/

#guard ((0.1 : Float) + 0.2 == 0.30000000000000004) = true
example : ((0.1 : Float) + 0.2 == 0.30000000000000004) = true := rfl

/-! ## 5. Decimal PARSE is parametric and reduces; decimal PRINT does not exist in core -/

#guard UnpackedFloat.pack binary16 (UnpackedFloat.ofScientific binary16 125 (-1))
     = UnpackedFloat.pack binary16 (UnpackedFloat.div binary16 (u binary16 125) (u binary16 10))
example : UnpackedFloat.pack Format.binary32 (UnpackedFloat.ofScientific Format.binary32 15 (-1))
        = UnpackedFloat.pack Format.binary32 (UnpackedFloat.div Format.binary32 (u Format.binary32 15) (u Format.binary32 10)) := rfl

/-! ## 6. Rounding: core implements ONE of IEEE 754-2019 §4.3's five attributes -/

-- roundTiesToEven (§4.3.1): 2.5 -> 2, 3.5 -> 4.  Tested at binary16 via a 3-bit-mantissa format.
abbrev m3 : Format := { mantissaBitsWithoutImplicit := 2, exponentBits := 5 }  -- 3-bit significand
-- 5 = 101b needs 3 bits: exact.  9 = 1001b needs 4: ties-to-even rounds to 8 (1000b), not 10.
#guard UnpackedFloat.pack m3 (UnpackedFloat.ofNat m3 9) = UnpackedFloat.pack m3 (UnpackedFloat.ofNat m3 8)
#guard UnpackedFloat.pack m3 (UnpackedFloat.ofNat m3 11) = UnpackedFloat.pack m3 (UnpackedFloat.ofNat m3 12)
example : UnpackedFloat.pack m3 (UnpackedFloat.ofNat m3 9) = UnpackedFloat.pack m3 (UnpackedFloat.ofNat m3 8) := rfl

/-! ## 7. Axiom prints — meaningful ONLY from this file's clean elaboration -/

theorem probe_add_binary16 :
    UnpackedFloat.pack binary16 (UnpackedFloat.add binary16 (u binary16 1) (u binary16 2))
  = UnpackedFloat.pack binary16 (u binary16 3) := rfl

theorem probe_toInt64_reduces :
    (2.75 : Float).toModel.toInt64 = (2 : Int64) := rfl

#print axioms probe_add_binary16
#print axioms probe_toInt64_reduces
#print axioms Float.Model.UnpackedFloat.valid_pack
