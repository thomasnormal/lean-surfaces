"""Rebind after alias: CPython runs this (prints 7); the census rejects
the candidate (alias name bound twice), the surviving plain assign keeps
the loud function-as-value refusal — the decided REFUSE semantics of
docs/memory-model.md's aliasing section, loud, never wrong."""


def f(x):
    return x + 1


g = f
g = 7
print(g)
