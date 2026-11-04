"""walrus_lab — the WALRUS operator in general expression position.

`(x := e)` evaluates `e`, BINDS `x` in the frame that is running, and
answers the same value (docs/memory-model.md §the walrus operator). The
rows below pin the three things that are easy to get wrong: the binding
ESCAPES the expression, the binding happens in evaluation ORDER, and a
short-circuited walrus never binds at all. CPython is the oracle for
every row.

The comprehension flavour keeps its own lowering (pass 7, §the walrus
filter): a comprehension is its own scope and PEP 572 leaks the binding
to the ENCLOSING one, which `Expr.namedExpr` would re-scope, so the
extractor emits the general node only outside a comprehension.
"""


def w_basic(n):
    # the binding outlives the expression that made it
    if (m := n * 2) > 4:
        return m
    return -m


def w_reuse(n):
    # bound once, read twice, in one expression and after it
    a = (b := n + 1) + b
    return a * 10 + b


def w_short_circuit(n):
    # `and` short-circuits BEFORE the walrus, so `q` never binds and the
    # read below is CPython's UnboundLocalError
    if n and (q := n + 1) > 2:
        return 1
    return q


def w_while(n):
    # the loop-condition idiom the operator was added for
    t = 0
    while (n := n - 1) >= 0:
        t = t + n
    return t


def w_call_arg(n):
    # a walrus inside a CALL argument, read after the call returns
    r = max(0, (h := n - 3))
    return r * 100 + h


def w_order(n):
    # left-to-right: the second operand sees the first one's binding
    return (p := n + 1) + (p * 2)


def w_genexp_filter(a, b, c):
    # the shipped ordering line's shape: the filter's LEFTMOST walrus is
    # hoisted into the synthesized generator body (pass 7), and `v` is
    # never read outside the genexp
    return sorted(((v, m) for m in (a, b, c) if (v := m * m) >= 4 or m),
                  reverse=True)
