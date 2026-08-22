/-
THE ES UNBLOCK — the ZERO-ERROR half, so that its axiom print is evidence.
The comparison against the landed `Float.toInt64` version (which fails `rfl`
and `decide`, deliberately) is in probe_es_unblock.lean.

RUN:  tools/check.sh harness/softfloat/probe_es_unblock_axioms.lean

ORIGINAL NOTE.  `docs/backlog/es.md` 2026-08-22-es-3 (M2 inch 4(a)) says
the exact-integer arm of `numberToString` (ECMA-262 §6.1.6.1.20) is not
`rfl`-provable because it goes through `Float.toInt64`, and that there is
"no kernel-reducible substitute short of the bit-level model".

The bit-level model IS in core and IS kernel-reducible.  This file replicates
the arm both ways, with NO project imports, and runs all three oracles on each.
Expected: the `Float.toInt64` version fails `rfl`/`decide`; the `.toModel`
version passes both.
-/
import Init.Data.Float.Model

/-- `LeanModels/Es/Convert.lean:219-226` as landed. -/
def numberToString (n : Float) : Option String :=
  if n.isNaN then some "NaN"
  else if n == (1.0 / 0.0) then some "Infinity"
  else if n == (-1.0 / 0.0) then some "-Infinity"
  else if n == 0.0 then some "0"
  else
    let t := n.toInt64
    if t.toFloat == n && n.abs < 1e15 then some (ToString.toString t) else none

/-- The same arm routed through `Float.Model` instead of the two `opaque` wrappers. -/
def numberToStringViaModel (n : Float) : Option String :=
  if n.isNaN then some "NaN"
  else if n == (1.0 / 0.0) then some "Infinity"
  else if n == (-1.0 / 0.0) then some "-Infinity"
  else if n == 0.0 then some "0"
  else
    let t := n.toModel.toInt64
    if Float.ofModel (Float.Model.ofInt64 t) == n && n.abs < 1e15 then
      some (ToString.toString t)
    else none

/-! ## The routed version -/
#guard numberToStringViaModel 42.0 == some "42"
example : numberToStringViaModel 42.0 = some "42" := rfl
example : numberToStringViaModel 42.0 = some "42" := by decide

/-! ## The rows the ES tier already pins, on the routed version -/
example : numberToStringViaModel (0.0 / 0.0) = some "NaN" := rfl
example : numberToStringViaModel (1.0 / 0.0) = some "Infinity" := rfl
example : numberToStringViaModel (-1.0 / 0.0) = some "-Infinity" := rfl
example : numberToStringViaModel (-0.0) = some "0" := rfl
example : numberToStringViaModel 0.0 = some "0" := rfl

/-! ## More integer rows, kernel-strength -/
example : numberToStringViaModel 7.0 = some "7" := rfl
example : numberToStringViaModel (-7.0) = some "-7" := rfl
example : numberToStringViaModel 1000.0 = some "1000" := rfl

/-! ## The `%` site, `LeanModels/Es/Convert.lean:303` -/
example : ((7.0 : Float) - 2.0 * ((7.0 / 2.0).toModel.toInt64 |> Float.Model.ofInt64 |> Float.ofModel)) == 1.0 := by
  decide

/-! ## And the arm that stays blocked: non-integer printing -/
#guard numberToStringViaModel 2.5 == none
example : numberToStringViaModel 2.5 = none := rfl

theorem es_int_arm_reduces : numberToStringViaModel 42.0 = some "42" := rfl
theorem es_negzero_reduces : numberToStringViaModel (-0.0) = some "0" := rfl
#print axioms es_int_arm_reduces
#print axioms es_negzero_reduces
