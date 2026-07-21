def pymod(a, b):
    return a % b


def countdown(n):
    while n > 0:
        n -= 1
    return n


# lean[
# /-! Tutorial 05 (docs/tutorial/05-exceptions-and-partial.md): the `==>!`
# arrow for raising runs, the strengthened partial arrow `~~>`, and why
# the weak "if it returns then v" form is banned. -/
# #py_check tut_05.pymod(7, 3) = 1
# #py_check tut_05.pymod(-7, 3) = 2
# #py_check tut_05.pymod(7, -3) = -2
# #py_check tut_05.pymod(7, 0) raises .zeroDivisionError
# #py_check tut_05.countdown(5) = 0
# #py_check tut_05.countdown(0) = 0
# #py_check tut_05.countdown(-3) = -3
#
# /-- A raise as specified behavior: for every `a`, `pymod(a, 0)`
# terminates by raising `ZeroDivisionError`. `py_prove` closes `==>!`
# goals for loop-free bodies just like `==>` ones. -/
# theorem pymod_zero_raises (a : PyInt) : tut_05.pymod(a, 0) ==>! .zeroDivisionError := by
#   py_prove [tut_05]
#
# /-- Total correctness of the countdown for `n ≥ 0` — a single-clause
# loop proof. The theorem binder `n` shadows the mutated Python variable
# `n`, so `(state := [n])` names the environment slot and the lambda
# binder is free to be `k` (tutorial 04's shadowing trap). -/
# theorem countdown_total (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ==> (0 : Int) := by
#   py_begin [tut_05]
#   py_loop (state := [n])
#           (inv := fun (k : Int) => 0 ≤ k)
#           (dec := fun (k : Int) => k.toNat)
#   all_goals grind
#
# /-- The strengthened partial arrow: every run of `countdown(n)` with
# `n ≥ 0`, at every fuel, either times out or returns exactly `0` — no
# exception, no `unsupported`, no other value. Free from `countdown_total`
# by determinism modulo fuel (`CallsTo.partialTo`, via `py_corollary`). -/
# theorem countdown_partial (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ~~> (0 : Int) := by
#   py_corollary [countdown_total]
#
# /-- Why the weak reading is banned: `~~>` is *falsifiable* on raising
# programs. "If `pymod(7, 0)` returns, it returns 42" is vacuously true —
# the call raises. The strengthened `pymod(7, 0) ~~> 42` is refutable, and
# here is the refutation (`PartialTo.not_raises`, Surface.lean). -/
# theorem no_partial_spec_for_raising_call : ¬ (tut_05.pymod(7, 0) ~~> (42 : Int)) :=
#   fun h => h.not_raises (pymod_zero_raises 7)
# ]
