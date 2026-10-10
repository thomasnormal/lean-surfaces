"""F-string conversions must bypass a shadowed str name.

The intrinsic field representation admits these formerly refused cases
without adding a synthesized name lookup. Explicit source calls still
obey ordinary Python name resolution.
"""


def shadowed(n):
    str = "SHADOW"
    return f"{n}"


def elsewhere(n):
    return f"{n}"


def plain_concat(n):
    return "n=" + str(n)
