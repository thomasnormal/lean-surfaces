"""leanpy corpus: the exception MESSAGE, not just the class.

CPython maps every uncaught exception to exit 1, so stdout + exit code
alone cannot tell two apart; the harnesses gained a CLASS comparison on
2026-08-13 and caught a false agreement the same hour. This row is the
next resolution step down: the model's `NameError` carries the name, so
the whole `NameError: name 'nope' is not defined` line is compared.

Rows whose exception class carries NO payload in the model
(`ZeroDivisionError`, `IndexError`, `KeyError`, `AttributeError`,
`RecursionError`) are reported as `ABSENT` by the survey's message
telemetry and are NOT compared — inventing a text the semantics does not
claim would be exactly the kind of lie this project refuses.
"""

print("before")
print(nope)
