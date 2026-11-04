"""The starred-display lowering's shadowing boundary (docs/memory-model.md
§starred displays).

`[*a, 3]` is lowered to calls of unspellable internal `list`/`tuple` names,
which the source never writes. CPython's display performs no ordinary name
lookup: BUILD_LIST_UNPACK is a bytecode, so a shadowed `list` cannot affect
it. The internal names preserve that behavior after lowering.

Source-level shadows cannot affect the generated calls. This file pins that
behavior: `shadowed(3)` and `elsewhere(3)` both produce the same list as
CPython. The plain display below remains the no-star control.

The generated names are recognized only by the model's builtin dispatcher.
They cannot be written as Python identifiers, so module and local bindings
cannot collide with them. This keeps the lowering faithful without a
scope-sensitive refusal.
"""


def shadowed(n):
    # The hazard in one function: a local `list` makes the name local
    # THROUGHOUT the body by CPython's static rule, so the lowered call
    # would find "SHADOW". CPython builds [1, 2, 3], and so does the model;
    # the synthetic names make this ordinary local binding harmless.
    list = "SHADOW"
    a = [1, 2]
    return [*a, n]


def elsewhere(n):
    # No shadow in THIS function, so its synthetic calls still resolve to the
    # real builtins even though `shadowed` has a local named `list`.
    a = [1, 2]
    return [*a, n]


def plain_display(n):
    # The control, and the point: a display with no star is untouched by
    # the lowering and by the census, so it still answers.
    return [1, 2, n]
