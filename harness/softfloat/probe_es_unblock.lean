/-
THE ES UNBLOCK, RUN.  `docs/backlog/es.md` 2026-08-22-es-3 (M2 inch 4(a)) says
the exact-integer arm of `numberToString` (ECMA-262 §6.1.6.1.20) is not
`rfl`-provable because it goes through `Float.toInt64`, and that there is
"no kernel-reducible substitute short of the bit-level model".

The bit-level model IS in core and IS kernel-reducible.  This file replicates
the arm both ways, with NO project imports, and runs all three oracles on each.
Expected: the `Float.toInt64` version fails `rfl`/`decide`; the `.toModel`
version passes both.

RUN:  tools/check.sh harness/softfloat/probe_es_unblock.lean
      (case `scratch` — outside every lake library glob, core imports only, so
       rule 3's exemption applies and no build tenure is needed.)
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

/-! ## The landed version -/
#guard numberToString 42.0 == some "42"                       -- untrusted evaluator
example : numberToString 42.0 = some "42" := rfl               -- expected FAIL
example : numberToString 42.0 = some "42" := by decide         -- expected FAIL

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

-- NO `#print axioms` HERE.  This file is EXPECTED to report two errors (the two
-- `Float.toInt64` kernel rows), and an axiom print from a file that did not
-- elaborate cleanly is quoting the error recovery, not the tree (§0.1 II(a)).
-- The clean axiom print lives in probe_es_unblock_axioms.lean.
