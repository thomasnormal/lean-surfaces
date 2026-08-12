"""leanpy corpus: the OTHER side of the class-creation guard — classes
whose creation is observationally free still RUN.

Methods, `pass`, docstrings and LITERAL attribute bindings can neither
print nor raise at the `class` statement, so the model skipping the body
skips nothing: `ClassDefn.creationPure` stays true and the script runs to
completion, matching CPython. The guard is precise, not a blanket refusal
of every class with a body (docs/memory-model.md §class creation).

`Tag` also pins the layering: a literal class attribute keeps CREATION
pure (this script runs) while still leaving the class uninstantiable in
the H3 tier (`ok = false`) — the two questions are answered separately,
and `Tag()` would refuse loudly.
"""


class Tag:
    kind = "tag"


class Counter:
    """Docstring plus methods only — creation-free AND instantiable."""

    def __init__(self, start):
        self.n = start

    def bump(self):
        self.n = self.n + 2
        return self.n


def run(start, times):
    c = Counter(start)
    last = start
    while times > 0:
        last = c.bump()
        times = times - 1
    return last


print(run(0, 3))
print(run(10, 1))
