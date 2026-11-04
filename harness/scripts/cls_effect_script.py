"""leanpy corpus: CLASS CREATION IS AN EFFECT — the executable row.

CPython runs a class body at the `class` statement, so this program
prints "creating C", then the computed class-local value, BEFORE
"after". The executable class-creation slice now evaluates these body
statements in a fresh class namespace while retaining stdout and heap
effects in the module world.

This row closes the class-body effect that `tools/leanpy` found: it was a
MISMATCH against CPython before the executable slice, the only silent
divergence the first completeness survey turned up.
"""


class C:
    print("creating C")
    x = 1
    y = x + 1
    print(y)


print("after")
