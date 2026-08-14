"""The f-string lowering's ONE new boundary: a module that BINDS the name
`str` (docs/memory-model.md §f-strings, the shadow census).

`f"{x}"` is lowered to `str(x)`, which spells the rendering as a call of
the NAME `str` -- a lookup the source never wrote. CPython's f-string
performs no such lookup: it calls the type's `__format__` directly, so a
shadowed `str` cannot affect it. The interpreter, however, reaches its
`str` builtin only AFTER every shadow-resolving arm, so the lowered call
would render through the shadow and be SILENTLY WRONG.

So the extractor censuses the whole module for a binding of `str` (any
scope, any binding form) and refuses every f-string in it, loudly. This
file is the row that would catch the census being dropped: without it
`shadowed(3)` answers '3' by accident and nothing fails.
"""


def shadowed(n):
    # The hazard in one function: a local `str` makes the name local
    # THROUGHOUT the body by CPython's static rule, so the lowered call
    # would find "SHADOW". CPython renders '3'. The model must be LOUD.
    str = "SHADOW"
    return f"{n}"


def elsewhere(n):
    # No shadow in THIS function -- refused anyway, because the census is
    # whole-module. Deciding it per scope would mean re-deciding CPython's
    # scoping rules inside the extractor, a second table; the conservative
    # refusal costs a file nobody writes.
    return f"{n}"


def plain_concat(n):
    # The control, and the point: an explicit `str()` call written in the
    # SOURCE is not refused. It is subject to CPython's real scoping (no
    # local `str` here, so it is the builtin) and agrees. Only the call
    # the LOWERING synthesizes needs the census.
    return "n=" + str(n)
