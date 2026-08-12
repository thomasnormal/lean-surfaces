"""leanpy corpus: the module-init rollback with an EXCEPTION.

CPython dies at `x = 1 // 0` with ZeroDivisionError and exits 1, having
printed nothing. The fold attempted the statement, the attempt raised, and
the rollback poisoned `x` — so leanpy used to print "done" and exit 0, the
worst kind of answer. `initNothingSkipped` refuses the program instead.
"""
x = 1 // 0

print("done")
