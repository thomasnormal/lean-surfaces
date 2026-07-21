def midpoint(a: int, b: int) -> int:
    return (a + b) // 2


# lean[
# /-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
# Surface.lean) — including the negative-operand cases where floor division
# (`Int.fdiv`) and Lean's truncating `Int.div` disagree: `midpoint(-3, -5)
# = -4`, `midpoint(3, -4) = -1` (CPython floors; truncation would give `0`). -/
# #py_check midpoint(3, 5) = 4
# #py_check midpoint(-3, -5) = -4
# #py_check midpoint(3, -4) = -1
# #py_check midpoint(0, 0) = 0
#
# /-- Total correctness (gallery example 2): the general theorem must say
# `Int.fdiv` — Python `//` floors, and the divergence from truncating
# division is visible in the statement, never buried in a translation.
# Straight-line body: `py_prove` closes it outright (`py_simp` reduces
# `evalBinOp .floorDiv` to `Int.fdiv` and discharges the `2 = 0` divisor
# guard). (Not `@[spec]`: the ∃-fuel arrow is not a Hoare-triple/simp
# shape — see Examples/python/add.py.) -/
# theorem midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2 := by
#   py_prove [midpoint]
#
# set_option linter.unusedVariables false in
# /-- The prettier `/` form under the gallery's sign hypotheses, derived
# from `midpoint_spec` by rewriting the returned value (`Int.fdiv (a + b) 2
# = (a + b) / 2` via `Int.fdiv_eq_ediv_of_nonneg`, passed to `py_corollary`
# as the value bridge) — NOT by re-executing the body. Note: core Lean's
# `Int` `/` is Euclidean division (`Int.ediv`), which already agrees with
# floor division for every *positive divisor*, so on this toolchain
# `ha`/`hb` are not load-bearing (recorded for the honest reading — hence
# the silenced unused-variable linter); the statement is the normative
# gallery one (docs/spec-surface.md §2). -/
# theorem midpoint_nonneg (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
#     midpoint(a, b) ==> (a + b) / 2 := by
#   py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]
#
# set_option warning.simp.varHead false in
# /-- `midpoint(a, b)` returns `⌊(a + b) / 2⌋` on int inputs: any successful
# run, at any fuel, yields exactly `.int (Int.fdiv (a + b) 2)`. A
# determinism corollary of `midpoint_spec` — one `py_corollary`
# (Surface.lean). -/
# @[spec] theorem midpoint_run_spec (a b : Int) {fuel : Nat} {r : Val}
#     (h : callFunction midpoint "midpoint" #[.int a, .int b] fuel = .ok r) :
#     r = .int (Int.fdiv (a + b) 2) := by
#   py_corollary [midpoint_spec]
# ]
