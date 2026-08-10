"""closure_lab — H7 nested defs and closures: the acceptance battery.

The snapshot tier (docs/memory-model.md §nested defs and closures):
a nested def captures enclosing locals AT DEF TIME, admitted exactly
when no capture is rebound after the def — where snapshot and CPython's
cell are observationally equal, generator bodies (which read captures
at RESUME time) included. Everything else refuses LOUDLY at extraction:
rebinding after the def, `nonlocal`, a def inside a loop, a call of the
nested name before its def (CPython's UnboundLocalError — a module
fallthrough would silently call the wrong function). CPython is the
oracle for every row.
"""


def basic(a):
    b = a + 1

    def inner(x):
        return x * b + a
    return inner(3)


def param_only(a):
    def f():
        return a * 2
    return f()


def with_default(a):
    def f(x, k=10):
        return a * k + x
    return f(1) + f(2, 3)


def chain(a):
    # a closure CAPTURING an earlier closure
    def f():
        return a + 1

    def g():
        return f() * 10
    return g()


def _mk(a):
    def f():
        return a * 3
    return f


def escape(a):
    # the closure outlives its creator's frame; the snapshot survives
    g = _mk(a)
    return g()


def identity_pair(a):
    def f():
        return a

    def g():
        return a
    return (f == g, f == f, g is g)


def truthy_closure(a):
    def f():
        return a
    if f:
        return 1
    return 0


def len_of_closure():
    def f():
        return 0
    return len(f)


def gen_closure(n):
    lim = n * 2

    def g():
        i = 0
        while i < lim:
            yield i * i
            i = i + 1
    t = 0
    for v in g():
        t = t + v
    return t


def gen_closure_sorted(n):
    def g():
        i = n
        while i > 0:
            yield i % 3
            i = i - 1
    return sorted(g(), reverse=True)


def gen_closure_any(n):
    def g():
        i = 0
        while i < 5:
            yield i == n
            i = i + 1
    return any(g())


def rebound_after(a):
    # the row that would EXPOSE snapshot-vs-cell: CPython's f() sees the
    # rebound a (cell), a snapshot would see the old one — REFUSED at
    # extraction, never translated
    def f():
        return a
    a = a + 1
    return f()


def uses_nonlocal(a):
    c = a

    def f():
        nonlocal c
        c = c + 1
    f()
    return c


def def_in_loop(a):
    t = 0
    while a > 0:
        def f():
            return a
        t = t + f()
        a = a - 1
    return t


def early_call(a):
    r = f()

    def f():
        return a
    return r


def lam_basic(s, i, p):
    # the shipped Position.move shape: a capture-free lambda assigned
    # once, called after — H7's lambda-as-nested-def
    put = lambda board, i, p: board[:i] + p + board[i + 1:]
    board = put(s, i, p)
    return put(board, 0, "X")


def lam_capture(a):
    k = a * 2
    f = lambda x: x + k
    return f(5)


def lam_rebound(a):
    # the exposing row again, lambda flavor: CPython's cell sees the
    # rebound a — refused at extraction
    f = lambda: a
    a = a + 1
    return f()


class TreeCounter:
    """bound() arc pass 2 (docs/memory-model.md §nested defs and
    closures, recursion addendum): the bound() SHAPE — a nested
    generator yielding recursive results THROUGH the captured self,
    folded below with a cutoff that abandons the drain. Each depth
    executes its own `def kids():` (a fresh closure, a fresh generator);
    `nodes` is the laziness observable — subtrees behind an abandoned
    yield never run."""

    def __init__(self):
        self.nodes = 0

    def tree(self, n, cut):
        self.nodes = self.nodes + 1
        if n == 0:
            return 1

        def kids():
            k = 0
            while k < 3:
                yield self.tree(n - 1, cut)
                k = k + 1

        t = 0
        for v in kids():
            t = t + v
            if t >= cut:
                break
        return t


def gen_rec(n, cut):
    c = TreeCounter()
    t = c.tree(n, cut)
    return (t, c.nodes)


def rec_nested_name(n):
    # REFUSAL: a nested def calling ITSELF by its own name — `f` is an
    # enclosing local bound BY the def, not textually before it, so the
    # capture census refuses ("no binding before the def"); CPython's
    # cell resolves the recursion and answers n. sunfish never does
    # this: bound() recurses through the METHOD name on self, which is
    # Module.functions dispatch, not a captured cell.
    def f(k):
        if k == 0:
            return 0
        return 1 + f(k - 1)
    return f(n)
