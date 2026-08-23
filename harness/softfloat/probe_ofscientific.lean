/-
PARSE INCH, EXPLORATORY PROBE — `ofScientific` as an `op_correct`.

The decimal census (2026-08-23-softfloat-12) put PARSE first because core
already ships the primitive: `UnpackedFloat.ofScientific spec m e` computes
`m * 10 ^ e`, width-parametrically and kernel-reducibly.  So this half is an
`op_correct` in the shape the component already has, not a new algorithm.

WHAT THIS PROBE IS FOR: deciding the STATEMENT before writing the theorem.
`ofScientific` has three branches and two of them are SAFETY CUTOFFS that
return a value without computing anything, so a single "= round of exact"
statement would be false at the cutoffs unless they are provably unreachable
in the representable range.  Measured here rather than assumed.

RUN:  tools/check.sh harness/softfloat/probe_ofscientific.lean
-/
import Init.Data.Float.Model

open Float.Model

abbrev binary16  : Format := { mantissaBitsWithoutImplicit := 10,  exponentBits := 5 }
abbrev binary128 : Format := { mantissaBitsWithoutImplicit := 112, exponentBits := 15 }
abbrev u (spec : Format) (n : Nat) : UnpackedFloat := UnpackedFloat.ofNat spec n

/-! ## 1. The three branches, and where each fires -/

-- zero is its own branch, at every width
example : UnpackedFloat.ofScientific binary16 0 5 = .zero .positive := rfl
example : UnpackedFloat.ofScientific Format.binary64 0 (-5) = .zero .positive := rfl

-- the OVERFLOW cutoff: `e > 2 ^ spec.exponentBits` returns +∞ without computing
example : UnpackedFloat.ofScientific binary16 1 33 = .infinity .positive := rfl
example : UnpackedFloat.ofScientific Format.binary64 1 2049 = .infinity .positive := rfl

-- the UNDERFLOW cutoff: `e < -(2 ^ exponentBits + m.log2)` returns +0
example : UnpackedFloat.ofScientific binary16 1 (-34) = .zero .positive := rfl
example : UnpackedFloat.ofScientific Format.binary64 1 (-2050) = .zero .positive := rfl

/-! ## 2. EXACTNESS on the fragment ES actually parses

ES's `StringToNumber` fragment is decimal integers.  `m * 10 ^ e` with `e ≥ 0`
and the product inside the significand is EXACT, and that is the row the parse
inch must certify.
-/

example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofScientific Format.binary64 42 0)
        = UnpackedFloat.pack Format.binary64 (u Format.binary64 42) := rfl
example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofScientific Format.binary64 42 2)
        = UnpackedFloat.pack Format.binary64 (u Format.binary64 4200) := rfl
example : UnpackedFloat.pack binary16 (UnpackedFloat.ofScientific binary16 7 1)
        = UnpackedFloat.pack binary16 (u binary16 70) := rfl
set_option maxRecDepth 2000 in
example : UnpackedFloat.pack binary128 (UnpackedFloat.ofScientific binary128 42 2)
        = UnpackedFloat.pack binary128 (u binary128 4200) := rfl

-- negative exponents that are exact in BINARY (denominator a power of two)
example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofScientific Format.binary64 5 (-1))
        = UnpackedFloat.pack Format.binary64
            (UnpackedFloat.div Format.binary64 (u Format.binary64 1) (u Format.binary64 2)) := rfl
example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofScientific Format.binary64 125 (-3))
        = UnpackedFloat.pack Format.binary64
            (UnpackedFloat.div Format.binary64 (u Format.binary64 1) (u Format.binary64 8)) := rfl

/-! ## 3. THE INEXACT ROW: `0.1` is not a dyadic, and the rounding must be the
    correctly-rounded one.  This is the row that needs `roundQ` to state
    properly; here we only check it AGREES with the literal the elaborator
    produces, which is core's own `ofScientific` — i.e. it is a CONSISTENCY
    check, NOT a correctness claim.  Recorded as such. -/

set_option maxRecDepth 16000 in
example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofScientific Format.binary64 1 (-1))
        = (0.1 : Float).toModel.toBits.toBitVec := rfl
-- AND A MEASURED COST ASYMMETRY, recorded rather than brute-forced.  The same
-- row for `0.3` (`ofScientific 3 (-1)`) does NOT close by `rfl` even at
-- `maxRecDepth 16000`, while `0.1` closes at 4000.  Same width, same operation,
-- same denominator -- only the numerator differs.  So the kernel cost of these
-- rows is VALUE-dependent, not merely width-dependent (§1.3 measured the width
-- axis; this is the other one).  It matters for the decimal inch: an instance
-- row that closes for one literal may not for its neighbour, so the parse
-- theorem must be PARAMETRIC and the `decide`-closed rows chosen, not assumed.

/-! ## 4. IS THE OVERFLOW CUTOFF SOUND?  i.e. does it only fire where the true
    value really does overflow?  binary16's max finite is 65504, and the cutoff
    fires at e > 32.  10 ^ 32 is astronomically past it, so the cutoff is
    CONSERVATIVE here — it never fires early.  Checked at the boundary. -/

-- THE BRANCHES ARE NOT SHAPE-UNIFORM, and this row is how that was found.
-- The guard is `e > 2 ^ exponentBits`, so at e = 32 exactly binary16 does NOT
-- take the cutoff: it computes 10 ^ 32 in full.  The result is NOT `.infinity`
-- -- measured: `.isInf = false`, `.isFinite = true`.  `roundWithAccuracy`
-- returns only `.zero` or `.finite`, NEVER `.infinity`; the overflow to
-- infinity happens in `pack`, one layer up.  Core says so in `UnpackedFloat`'s
-- own docstring: "an unpacked float in canonical form for a given format may
-- not actually be representable in that format ... the `pack` function will
-- overflow the float to infinity."
--
-- CONSEQUENCE FOR THE PARSE THEOREM: `ofScientific` alone is the wrong subject.
-- The cutoff branch yields `.infinity` while the computing branch yields an
-- UNREPRESENTABLE `.finite`, so a single statement about the unpacked result
-- would be comparing two different shapes.  The theorem must be stated AFTER
-- `pack`, or carry a representability hypothesis.
--
-- The row is `#guard` and not `rfl` because the kernel does not manage 10 ^ 32
-- at maxRecDepth 16000 while the untrusted evaluator does it instantly.  The
-- kernel-side claim at that exponent is therefore OWED, and is stated here
-- rather than quietly dropped.
#guard (UnpackedFloat.ofScientific binary16 1 32).isInf == false
#guard (UnpackedFloat.ofScientific binary16 1 32).isFinite == true
#guard UnpackedFloat.pack binary16 (UnpackedFloat.ofScientific binary16 1 32)
     == UnpackedFloat.packedInfinity binary16 .positive
-- the CUTOFF branch, by contrast, yields `.infinity` directly -- and cheaply,
-- because it computes nothing:
example : UnpackedFloat.ofScientific binary16 1 33 = .infinity .positive := rfl
-- and a value just inside the format still computes finitely
example : (UnpackedFloat.ofScientific binary16 1 4).isFinite = true := rfl
example : (UnpackedFloat.ofScientific binary16 65504 0).isFinite = true := rfl

theorem ofsci_zero (spec : Format) (e : Int) :
    UnpackedFloat.ofScientific spec 0 e = .zero .positive := rfl

#print axioms ofsci_zero
