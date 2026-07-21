def my_abs(x: int) -> int:
    if x < 0:
        return -x
    return x


# lean[
# /-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
# Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
# #py_check my_abs(5) = 5
# #py_check my_abs(-5) = 5
# #py_check my_abs(0) = 0
#
# /-- Total correctness (gallery example 1): `my_abs(x)` terminates and
# returns `|x|` (`Int.natAbs`-based, LeanModels/Python/Surface.lean).
# `py_prove` handles the branch itself: its branch-splitting alternative
# `split`s the residual `ite` from the symbolic `if x < 0:` and finishes
# each side with `omega` (which understands `natAbs` natively). (Not
# `@[spec]`: that attribute takes Hoare-triple/simp shapes; the ∃-fuel
# arrow is neither — see Examples/python/add.py.) -/
# theorem my_abs_spec (x : PyInt) : my_abs(x) ==> |x| := by
#   py_prove [my_abs]
#
# set_option warning.simp.varHead false in
# /-- `my_abs(x)` returns `|x|` on int inputs: any successful run, at any
# fuel, yields exactly `.int |x|`. A determinism corollary of `my_abs_spec`
# — one `py_corollary` (Surface.lean). -/
# @[spec] theorem my_abs_run_spec (x : Int) {fuel : Nat} {r : Val}
#     (h : callFunction my_abs "my_abs" #[.int x] fuel = .ok r) :
#     r = .int |x| := by
#   py_corollary [my_abs_spec]
# ]
