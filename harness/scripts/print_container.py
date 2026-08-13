"""leanpy corpus: PRINTING A CONTAINER is loud (telemetry row).

`print` reaches the interpreter now, but its printable tier is the scalar
one: int, bool, `None`, str. A list's `repr` is not guessed — CPython
quotes strings inside containers and not outside them, and the model
never invents an output it has not specified. Loud, never a wrong line.
"""

xs = [1, 2, 3]
print(len(xs))
print(xs)
