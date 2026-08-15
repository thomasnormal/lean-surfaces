"""leanpy corpus: the message gap that is still OPEN, pinned as a gap.

CPython raises `IndexError: list index out of range`; the model raises
`IndexError` with NO message, because `PyErr.indexError` is payload-free
and its four measured texts (list / tuple / list-assignment / pop-from-
empty) are chosen by the raise site. So the CLASS agrees and the run is a
MATCH, while the survey's message telemetry reports ABSENT — nothing is
invented, and the gap is visible rather than silent.

This row exists to FAIL LOUDLY the day `IndexError` gains its texts and
someone forgets to check them: it is the documented counterpart to
`zerodiv_pow_script.py`, which pins a message that IS carried. The
priced plan for closing it is docs/backlog.md §the payload-free
constructors (IndexError is the next one, ~1-2 hours, and needs no
payload — three sibling constructors).
"""

xs = [1, 2]
print(len(xs))
print(xs[5])
