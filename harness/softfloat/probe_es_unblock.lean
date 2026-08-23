/-
THE ES UNBLOCK — NOW A REGRESSION GATE, AND ITS HISTORY.

WHAT THIS FILE WAS.  `docs/backlog/es.md` 2026-08-22-es-3 (M2 inch 4(a)) said
the exact-integer arm of `numberToString` (ECMA-262 §6.1.6.1.20) was not
`rfl`-provable because it went through `Float.toInt64`, and that there was
"no kernel-reducible substitute short of the bit-level model".  This file was
written to show the bit-level model IS in core and IS one projection away.

WHAT IT IS NOW.  **The ES lane applied the routing** (commit `9dab312`), so
`LeanModels/Es/Convert.lean:224-238` is the ROUTED version.  This file is
therefore no longer a proposal — it is:

  1. a REGRESSION GATE: the landed shape must keep closing under `rfl` and
     `decide`, and it would go red if anyone routed it back through the
     externs; and
  2. the RECORD of what the pre-unblock shape could not do, kept because the
     failure is the evidence for the rule.

THE INVERSION THIS FILE ONCE CARRIED, recorded because it is the point.  For
about six minutes this probe was right; then ES committed, and the file went on
labelling the PRE-unblock body "as landed" while the real landed body was the
one it presented as the alternative.  Anyone running it would have concluded the
unblock was unlanded.  Caught by the 2026-08-23 quality audit.  A transcription
of someone else's file is a COPY WITH A TIMESTAMP, and it rots the moment they
commit.

RUN:  tools/check.sh harness/softfloat/probe_es_unblock.lean
      (case `scratch` — outside every lake library glob, core imports only, so
       rule 3's exemption applies and no build tenure is needed.)
-/
import Init.Data.Float.Model

/--
THE PRE-UNBLOCK BODY — history, **not** what is landed.  Kept so the failure
rows below have a subject.  It routed through `Float.toInt64` and
`Int64.toFloat`, both `@[extern] opaque`.
-/
def numberStringPreUnblock (n : Float) : Option String :=
  if n.isNaN then some "NaN"
  else if n == (1.0 / 0.0) then some "Infinity"
  else if n == (-1.0 / 0.0) then some "-Infinity"
  else if n == 0.0 then some "0"
  else
    let t := n.toInt64
    if t.toFloat == n && n.abs < 1e15 then some (ToString.toString t) else none

/--
THE LANDED BODY — mirrors `LeanModels/Es/Convert.lean:224-238`, which routes
through `Float.Model` rather than the two `opaque` wrappers.
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

/-! ## THE PRE-UNBLOCK VERSION — the untrusted evaluator says yes, the kernel cannot

These two `example`s are the file's EXPECTED FAILURES.  They are why this file
carries no `#print axioms` (§0.1 II(a)); the clean axiom print lives in
`probe_es_unblock_axioms.lean`, which contains only the landed shape.
-/
#guard numberStringPreUnblock 42.0 == some "42"                  -- untrusted evaluator
example : numberStringPreUnblock 42.0 = some "42" := rfl          -- expected FAIL
example : numberStringPreUnblock 42.0 = some "42" := by decide    -- expected FAIL

/-! ## THE LANDED VERSION — kernel-strength on every arm -/
#guard numberStringLanded 42.0 == some "42"
example : numberStringLanded 42.0 = some "42" := rfl
example : numberStringLanded 42.0 = some "42" := by decide

/-! ## The rows the ES tier pins, on the landed version -/
example : numberStringLanded (0.0 / 0.0) = some "NaN" := rfl
example : numberStringLanded (1.0 / 0.0) = some "Infinity" := rfl
example : numberStringLanded (-1.0 / 0.0) = some "-Infinity" := rfl
example : numberStringLanded (-0.0) = some "0" := rfl
example : numberStringLanded 0.0 = some "0" := rfl

/-! ## More integer rows, kernel-strength -/
example : numberStringLanded 7.0 = some "7" := rfl
example : numberStringLanded (-7.0) = some "-7" := rfl
example : numberStringLanded 1000.0 = some "1000" := rfl

/-! ## The shape the WITHDRAWN `%` arm would need

`LeanModels/Es/Convert.lean:315-324`.  The `%` arm is **withdrawn**, not
landed: it read `a - b * (a / b).toInt64.toFloat`, and `Float.toInt64` CLAMPS,
so a large quotient silently produced a wrong remainder that every in-range
test would have passed.  ES now refuses it by name, citing
`toInt_eq_truncate`.  The row below is what a correct arm would compute on an
in-range input — it does NOT claim the arm is landed.
-/
example : ((7.0 : Float) - 2.0 *
    ((7.0 / 2.0).toModel.toInt64 |> Float.Model.ofInt64 |> Float.ofModel)) == 1.0 := by
  decide

/-! ## And the arm that stays blocked: non-integer printing (SoftFloat step 3) -/
#guard numberStringLanded 2.5 == none
example : numberStringLanded 2.5 = none := rfl

-- NO `#print axioms` HERE.  This file is EXPECTED to report exactly two errors
-- (the two pre-unblock kernel rows), and an axiom print from a file that did
-- not elaborate cleanly is quoting the error recovery, not the tree
-- (§0.1 II(a)).  The clean print lives in probe_es_unblock_axioms.lean.
