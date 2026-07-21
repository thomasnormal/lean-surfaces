def gcd(a: int, b: int) -> int:
    while b != 0:
        a, b = b, a % b
    return a


# lean[
# /-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
# Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
# #py_check gcd(12, 18) = 6
# #py_check gcd(18, 12) = 6
# #py_check gcd(5, 0) = 5
# #py_check gcd(0, 5) = 5
# #py_check gcd(7, 13) = 1
#
# /-! CPython-divergence documentation (why the sign hypotheses below are
# NOT optional): Python's `%` is `Int.fmod`, so a negative operand keeps the
# loop below zero and `gcd(4, -6)` terminates at `-2` — matching CPython
# (differentially tested, harness/cases.json) — while `Int.gcd 4 (-6) = 2`.
# The unguarded spec `gcd(a, b) ==> Int.gcd a b` is *false*
# (docs/spec-surface.md §3). (The second line is a spec-side math fact, not
# a call — raw `#guard`.) -/
# #py_check gcd(4, -6) = -2
# #guard Int.gcd 4 (-6) == 2
#
# /-- **Total correctness** (gallery example 3): for nonnegative inputs
# `gcd(a, b)` terminates and returns `Int.gcd a b` (Nat-valued, marshalled
# via `ToVal Nat`) — in clause form (LoopTactic.lean). The invariant is
# "both nonneg ∧ `Int.gcd` unchanged from the initial values", the measure
# is the divisor itself; `(state := [a, b])` names the loop's environment
# variables because the theorem binders `a b` shadow the Python names and
# the invariant must mention the *initial* values (this is exactly the
# escape hatch's purpose). Residual goals on named atoms (`x`/`y`, exit
# state `x'`/`y'`, invariant conjuncts `hinv1`–`hinv3`): exit algebra
# (`y' = 0` collapses the gcd, `grind` bridges `natAbs`), one Euclid step
# (`gcd_fmod_step` + `Int.fmod_nonneg`, Surface.lean), measure decrease
# (`0 ≤ x.fmod y < y`), and the initial invariant. (Not `@[spec]`: the
# ∃-fuel arrow is not a Hoare-triple/simp shape — see
# Examples/python/add.py.) -/
# theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b := by
#   py_begin [gcd]
#   py_loop (state := [a, b])
#           (inv := fun (x y : Int) => 0 ≤ x ∧ 0 ≤ y ∧ Int.gcd x y = Int.gcd a b)
#           (dec := fun (x y : Int) => y.toNat)
#   · grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]
#   · exact ⟨hinv2, Int.fmod_nonneg hinv1 hinv2, by rw [gcd_fmod_step hinv1 hinv2, hinv3]⟩
#   · have := Int.fmod_lt_of_pos x (show (0:Int) < y by omega)
#     have := Int.fmod_nonneg hinv1 hinv2
#     omega
#   · exact ⟨ha, hb, trivial⟩
#
# /-- **Strengthened partial correctness** (the `~~>` arrow, `PartialTo`):
# every run of `gcd(a, b)` at every fuel either times out or returns exactly
# `Int.gcd a b` — no exception, no `unsupported`, no other value. Free from
# `gcd_total` via `CallsTo.partialTo` (determinism modulo fuel): one
# induction serves both arrows, exactly like `add_partial`. The naive "if it
# returns `.ok` then `v`" reading would be vacuously provable here even on
# the (false) unguarded statement; `~~>` is the falsifiable form. -/
# theorem gcd_partial (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ~~> Int.gcd a b := by
#   py_corollary [gcd_total]
#
# set_option warning.simp.varHead false in
# /-- `gcd(a, b)` returns `Int.gcd a b` on nonneg int inputs: any successful
# run, at any fuel, yields exactly `.int (Int.gcd a b)`. A determinism
# corollary of `gcd_total` — one `py_corollary` (Surface.lean). -/
# @[spec] theorem gcd_spec (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) {fuel : Nat} {r : Val}
#     (h : callFunction gcd "gcd" #[.int a, .int b] fuel = .ok r) :
#     r = .int (Int.gcd a b) := by
#   py_corollary [gcd_total]
# ]
