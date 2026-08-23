/-
SOFTFLOAT CORE CENSUS — probe B: WHERE THE WALLS ARE.
This file is EXPECTED to report errors.  No `#print axioms` may be quoted from
it (family-architecture §0.1 II(a): an axiom print is meaningful only from a
zero-error elaboration).  Its job is to record which rung of the §0.1 II(a)
ladder each core operation actually reaches.

RUN:  tools/check.sh harness/softfloat/probe_walls.lean
      (case `scratch` — outside every lake library glob, core imports only, so
       rule 3's exemption applies and no build tenure is needed.)
-/
import Init.Data.Float.Model

open Float.Model

abbrev binary16 : Format := { mantissaBitsWithoutImplicit := 10, exponentBits := 5 }
abbrev binary128 : Format := { mantissaBitsWithoutImplicit := 112, exponentBits := 15 }
abbrev u (spec : Format) (n : Nat) : UnpackedFloat := UnpackedFloat.ofNat spec n

/-! ## WALL 1 — `sqrt`: `Nat.sqrt` is well-founded, so `rfl` cannot unfold it -/

-- (a) does the INTERPRETER get it?  (#guard = compiled/interpreted evaluation)
#guard UnpackedFloat.pack binary16 (UnpackedFloat.sqrt binary16 (u binary16 49))
     = UnpackedFloat.pack binary16 (u binary16 7)

-- (b) does the KERNEL get it by `decide`?
example : UnpackedFloat.pack binary16 (UnpackedFloat.sqrt binary16 (u binary16 49))
        = UnpackedFloat.pack binary16 (u binary16 7) := by decide

-- (c) by `rfl`? (expected to FAIL — recorded)
example : UnpackedFloat.pack binary16 (UnpackedFloat.sqrt binary16 (u binary16 49))
        = UnpackedFloat.pack binary16 (u binary16 7) := rfl

-- (d) the underlying cause, isolated:
#guard Nat.sqrt 49 = 7
example : Nat.sqrt 49 = 7 := by decide
example : Nat.sqrt 49 = 7 := rfl        -- expected FAIL: well-founded recursion

/-! ## WALL 2 — width scaling: `>>> n` is `Nat.repeat`, so cost is LINEAR in the width -/

set_option maxRecDepth 4000 in
example : UnpackedFloat.pack binary128 (UnpackedFloat.div binary128 (u binary128 12) (u binary128 4))
        = UnpackedFloat.pack binary128 (u binary128 3) := rfl

set_option maxRecDepth 4000 in
example : UnpackedFloat.pack binary128 (UnpackedFloat.add binary128 (u binary128 1) (u binary128 2))
        = UnpackedFloat.pack binary128 (u binary128 3) := rfl

-- at the DEFAULT maxRecDepth, is binary64 fine?  (recorded: yes/no)
example : UnpackedFloat.pack Format.binary64 (UnpackedFloat.div Format.binary64 (u Format.binary64 12) (u Format.binary64 4))
        = UnpackedFloat.pack Format.binary64 (u Format.binary64 3) := rfl

/-! ## WALL 3 — the PACKED boundary: `opaque` + `@[extern]` (the ES tier's wall) -/

-- core's own docstring on `Float.toInt64`: "This function does not reduce in the kernel."
#guard (2.75 : Float).toInt64 = (2 : Int64)               -- interpreter: expected OK
example : (2.75 : Float).toInt64 = (2 : Int64) := rfl     -- kernel: expected FAIL
example : (2.75 : Float).toInt64 = (2 : Int64) := by decide  -- kernel: expected FAIL

-- and the contrast, one hop away through the MODEL (expected OK on all three):
#guard (2.75 : Float).toModel.toInt64 = (2 : Int64)
example : (2.75 : Float).toModel.toInt64 = (2 : Int64) := rfl
example : (2.75 : Float).toModel.toInt64 = (2 : Int64) := by decide

-- `Float.toUInt64` is `@[extern] def` WITH a Lean body — does it reduce?
#guard (2.75 : Float).toUInt64 = (2 : UInt64)
example : (2.75 : Float).toUInt64 = (2 : UInt64) := rfl

-- `Float.toString` is `opaque` — there is NO decimal-printing model in core at all.
#eval (2.75 : Float).toString
example : (2.75 : Float).toString = "2.750000" := rfl    -- expected FAIL whatever the RHS

/-! ## WALL 4 — what core simply does not have -/

-- fma: no declaration anywhere under Init.Data.Float.  (grep-verified; nothing to probe.)
-- rounding modes: only roundTiesToEven exists (`Accuracy.roundToNearestEven`).
--   There is no roundTowardZero / roundTowardPositive / roundTowardNegative /
--   roundTiesToAway rounding of an `Accuracy`.  Probe: the identifier does not exist.
#check @Float.Model.UnpackedFloat.Accuracy.roundToNearestEven
#check @Float.Model.UnpackedFloat.Accuracy.roundTowardZero   -- expected FAIL: unknown identifier

-- exception flags (IEEE 754-2019 §7): no Status/flag type; `Status.lean` is three predicates.
#check @Float.Model.UnpackedFloat.isNaN
#check @Float.Model.UnpackedFloat.Exception                  -- expected FAIL: unknown identifier

-- NaN payloads (IEEE 754-2019 §6.2.1): the constructor takes NO argument.
#check @Float.Model.UnpackedFloat.notANumber
