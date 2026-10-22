"""leanpy corpus: the exception MESSAGE, not just the class.

CPython maps every uncaught exception to exit 1, so stdout + exit code
alone cannot tell two apart; the harnesses gained a CLASS comparison on
2026-08-13 and caught a false agreement the same hour. This row is the
next resolution step down: the model's `NameError` carries the name, so
the whole `NameError: name 'nope' is not defined` line is compared.

Rows whose exception class carries no payload in the model remain an
honest `ABSENT` telemetry bucket. Condition-specific `IndexError`
constructors now carry their standard text and are compared exactly.
"""

print("before")
print(nope)
