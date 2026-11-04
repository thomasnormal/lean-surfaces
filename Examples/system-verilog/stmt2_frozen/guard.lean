import LeanModels.Sv.Sem2

/-!
# `Stmt2` is frozen: a build guard

Thomas, 2026-11-02 (`svgolf/design/architecture/ARCH-NOTE.md`, decision 7: one AST, `Stmt2` frozen). `Stmt2` keeps its
six constructors. It survives as the legacy view behind R-DESIGN2 until its estate is transported to the exact semantics,
and a new construct lands in the exact semantics first (`docs/sv-kernel.md`), not as a seventh `Stmt2` constructor.
Changing an existing constructor's fields (as `caseStmt`'s `inside : Bool` became `mode : CaseMode` for `casez`/`casex`)
is outside this guard.

`ctorIdx` lists every constructor and has no wildcard, so a seventh constructor fails to compile HERE, with Lean's
"Missing cases" error. Do not add an arm to make it compile: a new constructor is an architecture change, so take it to
the svGolf lead and Thomas first. The `#guard_msgs` below pins that the check is live: the same match with one arm
removed is rejected.
-/

namespace LeanModels.Sv.Stmt2Frozen

open LeanModels.Sv

/-- The constructor index of a `Stmt2`: exhaustive, no wildcard. -/
def ctorIdx : Stmt2 → Nat
  | .blockingAssign .. => 0
  | .nbaAssign .. => 1
  | .ifStmt .. => 2
  | .block .. => 3
  | .caseStmt .. => 4
  | .unsupported .. => 5

/-- error: Missing cases: -/
#guard_msgs (substring := true) in
def withoutUnsupported : Stmt2 → Nat
  | .blockingAssign .. => 0
  | .nbaAssign .. => 1
  | .ifStmt .. => 2
  | .block .. => 3
  | .caseStmt .. => 4

end LeanModels.Sv.Stmt2Frozen
