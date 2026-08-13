"""The starred-display lowering's ONE new boundary: a module that BINDS
`list` or `tuple` (docs/memory-model.md §starred displays, the shadow
census).

`[*a, 3]` is lowered to `list(tuple(a) + (3,))`, which spells the display
as calls of the NAMES `list` and `tuple` — lookups the source never
wrote. CPython's display performs no such lookup: BUILD_LIST_UNPACK is a
bytecode, so a shadowed `list` cannot affect it. The interpreter, though,
reaches its builtins only AFTER every shadow-resolving arm, so the
lowered calls would run through the shadow and be SILENTLY WRONG.

So the extractor censuses the whole module for a binding of either name
(any scope, any binding form) and refuses every starred display in it,
loudly. This file is the row that would catch the census being dropped:
without it `shadowed(3)` answers "SHADOW" instead of refusing, and
nothing else fails.
"""


def shadowed(n):
    # The hazard in one function: a local `list` makes the name local
    # THROUGHOUT the body by CPython's static rule, so the lowered call
    # would find "SHADOW". CPython builds [1, 2, 3]. The model must be
    # LOUD.
    list = "SHADOW"
    a = [1, 2]
    return [*a, n]


def elsewhere(n):
    # No shadow in THIS function — refused anyway, because the census is
    # whole-module. Deciding it per scope would mean re-deciding CPython's
    # scoping rules inside the extractor, a second table; the
    # conservative refusal costs a file nobody writes.
    a = [1, 2]
    return [*a, n]


def plain_display(n):
    # The control, and the point: a display with no star is untouched by
    # the lowering and by the census, so it still answers.
    return [1, 2, n]
