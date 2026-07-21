def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total


# lean[
# /-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
# Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
# #py_check tri(10) = 55
# #py_check tri(0) = 0
# #py_check tri(-3) = 0
#
# /-- Total correctness for `n ≥ 0`: `tri(n)` terminates and returns the
# `n`-th triangular number — in clause form (LoopTactic.lean). `py_begin`
# symbolically executes the entry up to the loop; `py_loop` proves the loop
# by the generic while rule from just two clauses — the invariant
# (`total = 0 + 1 + ⋯ + (i-1)`, stated multiplication-free as
# `2*total = i*(i-1)`, plus the range `0 ≤ i ≤ n + 1`) and the decreasing
# measure `n + 1 - i` — deriving the logical state, its environment
# rendering, the test value, and the body's step by unification. Residual
# goals are pure arithmetic on named atoms: the exit algebra (first bullet:
# `¬ i' ≤ n` and the range force `i' = n + 1`, then `grind` finishes the
# division), then invariant preservation, measure decrease, and the initial
# invariant, all closed by `grind`. No `Val`, no fuel, no AST anywhere. -/
# theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
#   py_begin [tri]
#   py_loop (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
#           (dec := fun (total i : Int) => (n + 1 - i).toNat)
#   · obtain rfl : i' = n + 1 := by omega
#     grind
#   all_goals grind
#
# /-- Total correctness for `n < 0`: the loop never runs and `tri(n)` returns
# `0`, all at constant fuel. -/
# theorem tri_neg_total (n : PyInt) (hn : n < 0) : tri(n) ==> (0 : Int) := by
#   have h0 : ¬ ((0 : Int) ≤ n) := by have hn' : (0 : Int) > n := hn; omega
#   exact CallsTo.intro 8 (by py_simp [callFunction, execWhile, tri, h0])
#
# set_option warning.simp.varHead false in
# /-- `tri(n)` returns the `n`-th triangular number `n*(n+1)/2` for `n ≥ 0`:
# any successful run, at any fuel, yields exactly `.int (n*(n+1)/2)`. A
# determinism corollary of `tri_total` — one `py_corollary` (Surface.lean). -/
# @[spec] theorem tri_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
#     (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
#     r = .int (n * (n + 1) / 2) := by
#   py_corollary [tri_total]
#
# set_option warning.simp.varHead false in
# /-- `tri(n)` returns `0` for `n < 0` (the loop body never runs). A
# determinism corollary of `tri_neg_total`. -/
# @[spec] theorem tri_neg_spec (n : Int) (hn : n < 0) {fuel : Nat} {r : Val}
#     (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
#     r = .int 0 := by
#   py_corollary [tri_neg_total]
#
# set_option warning.simp.varHead false in
# /-- The typed surface form of `tri_spec`: binders are `PyInt`, the result is
# bound relationally with `⇓`, and neither `Val` nor fuel appears. -/
# @[spec] theorem tri_correct (n r : PyInt) (hn : 0 ≤ n) (h : tri(n) ⇓ r) :
#     r = n * (n + 1) / 2 := by
#   py_corollary [tri_total]
# ]
