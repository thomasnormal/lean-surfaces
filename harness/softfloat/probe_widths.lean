/-
SOFTFLOAT CORE CENSUS — probe C: THE PRICE, per width.
Expected to elaborate CLEANLY.  Records the maxRecDepth each width needs for a
kernel `rfl` on the parametric ops, which is the component's own entry in the
decide-ladder crossover table (docs/lean-structures-census.md).

RUN:  tools/check.sh harness/softfloat/probe_widths.lean
      (case `scratch` — outside every lake library glob, core imports only, so
       rule 3's exemption applies and no build tenure is needed.)
-/
import Init.Data.Float.Model

open Float.Model

abbrev binary16  : Format := { mantissaBitsWithoutImplicit := 10,  exponentBits := 5 }
abbrev binary128 : Format := { mantissaBitsWithoutImplicit := 112, exponentBits := 15 }
abbrev binary256 : Format := { mantissaBitsWithoutImplicit := 236, exponentBits := 19 }
abbrev u (spec : Format) (n : Nat) : UnpackedFloat := UnpackedFloat.ofNat spec n

/-- one `div` at a width, through the packed bits. -/
abbrev divOK (spec : Format) : Prop :=
  UnpackedFloat.pack spec (UnpackedFloat.div spec (u spec 12) (u spec 4))
    = UnpackedFloat.pack spec (u spec 3)

-- default maxRecDepth is 512.
example : divOK binary16 := rfl
example : divOK Format.binary32 := rfl
example : divOK Format.binary64 := rfl
set_option maxRecDepth 1000 in
example : divOK binary128 := rfl
set_option maxRecDepth 2000 in
example : divOK binary256 := rfl

-- `decide` (rung 2) at the same widths
example : divOK binary16 := by decide
example : divOK Format.binary64 := by decide
set_option maxRecDepth 1000 in
example : divOK binary128 := by decide

/-! ## The parametric statement that no fixed width can express -/

-- Rung 1 shape: a statement quantified over EVERY format, proved once.
-- (Proof deferred to the layer-2 file; here we only check the STATEMENT elaborates,
--  because a statement that fails to elaborate makes `#print axioms` lie — §0.1 II(a).)
example : ∀ (spec : Format) (s : UnpackedFloat.Sign),
    UnpackedFloat.add spec (.zero s) (.zero s) = .zero s := by
  intro spec s
  cases s <;> rfl

-- IEEE 754-2019 §6.3: the sign of a sum of two zeros of DIFFERING sign is +0
-- under roundTiesToEven.  One statement, every format.
example : ∀ (spec : Format),
    UnpackedFloat.add spec (.zero .positive) (.zero .negative) = .zero .positive := by
  intro spec; rfl

-- IEEE 754-2019 §6.2: NaN propagates through add, in every format, on either side.
example : ∀ (spec : Format) (x : UnpackedFloat),
    UnpackedFloat.add spec .notANumber x = .notANumber := by
  intro spec x; rfl

theorem nan_left_add : ∀ (spec : Format) (x : UnpackedFloat),
    UnpackedFloat.add spec .notANumber x = .notANumber := by
  intro spec x; rfl

theorem zero_sum_sign : ∀ (spec : Format),
    UnpackedFloat.add spec (.zero .positive) (.zero .negative) = .zero .positive := by
  intro spec; rfl

#print axioms nan_left_add
#print axioms zero_sum_sign
