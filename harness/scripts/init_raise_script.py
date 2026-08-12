"""leanpy corpus: A TOP-LEVEL STATEMENT THAT RAISES — a payoff row of THE
ONE PIPELINE (docs/memory-model.md §the one pipeline).

CPython dies at `x = 1 // 0` with ZeroDivisionError and exits 1, having
printed nothing. Two pipelines ago the G1 fold ATTEMPTED this statement,
the attempt raised, and the rollback swallowed it — leanpy printed "done"
and exited 0, the worst kind of answer; `initNothingSkipped` then refused
the program instead. With one pipeline there is no fold and no rollback:
the statement executes, the exception propagates out of the top level, and
the runner boundary maps it to exit 1 with the class name — CPython's own
answer.
"""
x = 1 // 0

print("done")
