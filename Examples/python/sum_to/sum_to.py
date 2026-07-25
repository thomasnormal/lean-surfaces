def sum_to(n: int) -> int:
    s = 0
    while n > 0:
        s += n
        n -= 1
    return s


# lean[
# /-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
# Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
# #py_check sum_to(10) = 55
# #py_check sum_to(0) = 0
#
# /-- `Int`-core of `sum_to_total`, by the VC walker (`py_vcgen`,
# VCTactic.lean). The loop counts *down*: the Python variable `n` is
# mutated, so it must be a clause binder — the initial value gets the
# capitalized binder `N` (the walker's counterpart of `py_loop`'s
# `(state := …)` shadowing escape hatch, cf. Examples/python/gcd/proof.lean).
# Invariant: `s` already holds the summed tail `(n+1) + ⋯ + N`, stated
# multiplication-free as `2*s = (N - n)*(N + n + 1)`, plus the range
# `0 ≤ n ≤ N`; the measure is `n` itself. Residuals: the `return` (the
# negated test and range force `n' = 0`, `grind` divides), rest `grind`. -/
# private theorem sum_to_core (N : PyInt) (hN : 0 ≤ N) : sum_to(N) ==> N * (N + 1) / 2 := by
#   py_vcgen [sum_to]
#     (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
#     (dec := fun (s n : Int) => n.toNat)
#   case ret =>
#     obtain rfl : n' = 0 := by omega
#     grind
#   all_goals grind
#
# /-- Total correctness for `n ≥ 0`: `sum_to(n)` terminates and returns the
# `n`-th triangular number — the `Int`-core above at the public binder. -/
# theorem sum_to_total (n : PyInt) (hn : 0 ≤ n) : sum_to(n) ==> n * (n + 1) / 2 :=
#   sum_to_core n hn
# ]
