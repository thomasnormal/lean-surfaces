"""Alias BEFORE the def: CPython raises NameError at the alias line; the
census rejects the candidate (target def ends later) and the ordered
admission (defsBoundBefore) refuses the script loudly — never a
position-independent dispatch CPython would contradict."""

early = late_def


def late_def(x):
    return x


print(early(1))
