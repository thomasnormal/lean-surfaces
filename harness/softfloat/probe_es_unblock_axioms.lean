/-
THE ES UNBLOCK — the ZERO-ERROR half, so that its axiom print is EVIDENCE.

`probe_es_unblock.lean` carries the comparison, and therefore carries two
deliberate failures (the pre-unblock body under `rfl`/`decide`).  An axiom
print from a file that did not elaborate cleanly is quoting the error
recovery, not the tree (family-architecture §0.1 II(a)) — so the print lives
HERE, in a file that contains only the LANDED shape and must stay green.

WHAT IS LANDED.  The ES lane applied the routing (commit `9dab312`), so
`LeanModels/Es/Convert.lean:224-238` reads `let t := n.toModel.toInt64` and
`Float.ofModel (Float.Model.ofInt64 t)`.  The body below mirrors it.  The
pre-unblock body — `n.toInt64` / `t.toFloat`, both `@[extern] opaque` — is
history and lives in the sibling file.

RUN:  tools/check.sh harness/softfloat/probe_es_unblock_axioms.lean
-/
import Init.Data.Float.Model

/--
Mirrors the LANDED `numberToString`, `LeanModels/Es/Convert.lean:224-238`
(ECMA-262 §6.1.6.1.20), routed through `Float.Model` rather than the two
`opaque` wrappers.
-/
def numberStringLanded (n : Float) : Option String :=
  if n.isNaN then some "NaN"
  else if n == (1.0 / 0.0) then some "Infinity"
  else if n == (-1.0 / 0.0) then some "-Infinity"
  else if n == 0.0 then some "0"
  else
    let t := n.toModel.toInt64
    if Float.ofModel (Float.Model.ofInt64 t) == n && n.abs < 1e15 then
      some (ToString.toString t)
    else none

/-! ## Every arm, kernel-strength -/
#guard numberStringLanded 42.0 == some "42"
example : numberStringLanded 42.0 = some "42" := rfl
example : numberStringLanded 42.0 = some "42" := by decide

example : numberStringLanded (0.0 / 0.0) = some "NaN" := rfl
example : numberStringLanded (1.0 / 0.0) = some "Infinity" := rfl
example : numberStringLanded (-1.0 / 0.0) = some "-Infinity" := rfl
example : numberStringLanded (-0.0) = some "0" := rfl
example : numberStringLanded 0.0 = some "0" := rfl
example : numberStringLanded 7.0 = some "7" := rfl
example : numberStringLanded (-7.0) = some "-7" := rfl
example : numberStringLanded 1000.0 = some "1000" := rfl

/-! ## The shape the WITHDRAWN `%` arm would need

`LeanModels/Es/Convert.lean:315-324` — the arm is **withdrawn**, not landed.
It read `a - b * (a / b).toInt64.toFloat`, and `Float.toInt64` CLAMPS, so a
large quotient silently produced a wrong remainder that every in-range test
would have passed.  ES refuses it by name, citing `toInt_eq_truncate`.  The
row below is what a correct arm would compute on an in-range input; it does
NOT claim the arm is landed.
-/
example : ((7.0 : Float) - 2.0 *
    ((7.0 / 2.0).toModel.toInt64 |> Float.Model.ofInt64 |> Float.ofModel)) == 1.0 := by
  decide

/-! ## And the arm that stays blocked: non-integer printing (SoftFloat step 3) -/
#guard numberStringLanded 2.5 == none
example : numberStringLanded 2.5 = none := rfl

theorem es_int_arm_reduces : numberStringLanded 42.0 = some "42" := rfl
theorem es_negzero_reduces : numberStringLanded (-0.0) = some "0" := rfl
#print axioms es_int_arm_reduces
#print axioms es_negzero_reduces
