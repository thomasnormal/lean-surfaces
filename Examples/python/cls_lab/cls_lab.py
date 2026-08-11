"""H3 class-tier acceptance battery (checks-only example, the list_lab
analog): instantiation, mutable self across method calls, aliasing of
instance refs, default-object protocol (identity equality, truthiness,
is), the faithful AttributeError/TypeError frontier, and the loud
refusals (inheritance, extra dunders, class-as-value). Every function
returns boundary scalars/tuples so the public freeze stays in tier."""


class Cell:
    def __init__(self, x):
        self.x = x

    def get(self):
        # a user method named like the dict builtin: instance dispatch
        # goes through the CLASS, never the builtin method tier
        return self.x

    def set(self, v):
        self.x = v

    def bump2(self):
        # methods calling methods through self
        self.set(self.x + 1)
        self.set(self.x + 1)
        return self.x


class Bag:
    def __init__(self):
        self.items = []
        self.meta = {}

    def add(self, v):
        self.items.append(v)
        self.meta[v] = len(self.items)
        return len(self.items)


class NoInit:
    def ping(self):
        return 42


class Weird:
    def __init__(self):
        self.x = 1

    def __eq__(self, other):
        return True


class Sub(Cell):
    pass


def make_get(a):
    c = Cell(a)
    return c.get()


def set_then_get(a, b):
    c = Cell(a)
    c.set(b)
    return (c.get(), c.x)


def bump_twice(a):
    c = Cell(a)
    return c.bump2()


def alias_mutation(a, b):
    c = Cell(a)
    d = c
    d.set(b)
    return (c.x, d.x, c is d, c is not d)


def two_instances(a):
    c = Cell(a)
    d = Cell(a)
    return (c is d, c == d, c == c, c != d)


def instance_truthy(a):
    c = Cell(a)
    if c:
        return 1
    return 0


def bag_flow(a, b):
    g = Bag()
    g.add(a)
    g.add(b)
    return (g.add(a + b), len(g.items), g.meta[a], a in g.meta)


def no_init_ping():
    n = NoInit()
    return n.ping()


def no_init_arity():
    n = NoInit(3)
    return 0


def init_arity(a):
    c = Cell(a, a)
    return 0


def missing_attr(a):
    c = Cell(a)
    return c.gone


def missing_method(a):
    c = Cell(a)
    return c.gone_method()


def store_before_read(a):
    c = Cell(a)
    c.fresh = a + 1
    return (c.fresh, c.x)


def len_of_instance(a):
    c = Cell(a)
    return len(c)


def subscript_instance(a):
    c = Cell(a)
    return c[0]


def iterate_instance(a):
    c = Cell(a)
    for v in c:
        return v
    return 0


def attr_on_int(a):
    return a.x


def store_attr_on_dict(a):
    d = {}
    d.x = a
    return 0


def weird_eq(a):
    w = Weird()
    return w.x


def sub_inherits(a):
    s = Sub(a)
    return s.get()


def class_as_value():
    f = Cell
    return 0


class Rec:
    """bound() arc pass 2 (docs/memory-model.md §nested defs and
    closures, recursion addendum): recursion through the RECEIVER —
    every depth re-enters callIn with the same `self` ref, and the
    `nodes` attribute mutates one shared instance across the nest."""

    def __init__(self):
        self.nodes = 0

    def down(self, n):
        # direct method self-recursion
        self.nodes = self.nodes + 1
        if n == 0:
            return 0
        return 1 + self.down(n - 1)

    def odd(self, n):
        # mutual method recursion, odd half
        if n == 0:
            return False
        return self.even(n - 1)

    def even(self, n):
        # mutual method recursion, even half
        if n == 0:
            return True
        return self.odd(n - 1)


def method_rec(n):
    r = Rec()
    return (r.down(n), r.nodes)


def method_mutual(n):
    r = Rec()
    return (r.odd(n), r.even(n))


class Counter:
    # pass 4 (docs/memory-model.md, "bound() end-to-end"): the attribute
    # += and the tuple-attribute-unpack acceptance surface
    def __init__(self):
        self.n = 0
        self.xs = []


def aug_attr(k):
    # attribute augmented assignment, sunfish's `self.nodes += 1`
    c = Counter()
    i = 0
    while i < k:
        c.n += 2
        i = i + 1
    return c.n


def aug_attr_missing(k):
    # the LOAD fires before the value evaluates: AttributeError, and the
    # value expression (which would divide by zero) never runs
    c = Counter()
    c.m += 1 // 0
    return 0


def aug_attr_list(k):
    # a list-valued attribute's += mutates in place -- loud, never wrong
    c = Counter()
    c.xs += [k]
    return 0


def unpack_attrs(k):
    # the tuple target with ATTRIBUTE elements, Searcher.__init__'s shape
    c = Counter()
    c.a, c.b = k, k + 1
    return c.a * 100 + c.b


def unpack_attrs_mixed(k):
    # names and attributes mixed in one target
    c = Counter()
    x, c.b = k + 5, k
    return x * 100 + c.b


def unpack_attrs_swap(k):
    # the RHS reads BEFORE any store runs
    c = Counter()
    c.a, c.b = k, 2
    c.a, c.b = c.b, c.a
    return c.a * 100 + c.b


def unpack_arity(k):
    # the faithful unpack ValueError through the attribute path
    c = Counter()
    c.a, c.b = (k,)
    return 0


def unpack_subscript_elem(k):
    # a subscript ELEMENT inside a tuple target stays loud
    c = Counter()
    d = {}
    d[0], c.a = 1, k
    return 0
