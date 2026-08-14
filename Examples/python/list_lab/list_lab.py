"""H2 list-tier laboratory: heap lists — aliasing, in-place mutation,
methods, membership, equality, live-cursor iteration, module-level
tables. The observable behaviors Val.listV could never express: two
references to one list seeing each other's writes."""

TABLE = [1, 2, 3]


def read_table(i):
    return TABLE[i]


def bump_table():
    TABLE[0] = TABLE[0] + 1
    return TABLE[0]


def bump_twice():
    bump_table()
    bump_table()
    return TABLE[0]


def alias_write():
    xs = [1, 2, 3]
    ys = xs
    ys[0] = 5
    return xs[0]


def alias_append_len(n):
    xs = []
    ys = xs
    ys.append(n)
    ys.append(n + 1)
    return len(xs)


def poke(xs, v):
    xs[1] = v
    return None


def callee_mutates(v):
    xs = [0, 0]
    poke(xs, v)
    return xs[1]


def fresh_identity():
    xs = [1, 2]
    ys = [1, 2]
    return (xs is ys, xs is xs, xs == ys)


def neg_index():
    xs = [10, 20, 30]
    return xs[-1] + xs[-3]


def index_error(i):
    xs = [1, 2]
    return xs[i]


def store_error():
    xs = [1]
    xs[3] = 0
    return xs[0]


def append_pop(n):
    xs = [n]
    xs.append(n + 1)
    xs.append(n + 2)
    a = xs.pop()
    b = xs.pop(0)
    return (a, b, len(xs))


def pop_empty():
    xs = []
    return xs.pop()


def membership(n):
    xs = [1, 2, 3]
    return (n in xs, n not in xs)


def eq_nested():
    return [[1, 2], [3]] == [[1, 2], [3]]


def eq_mixed():
    return [1, 2] == (1, 2)


def loop_sum():
    xs = [1, 2, 3, 4]
    s = 0
    for x in xs:
        s = s + x
    return s


def loop_mutate_during():
    xs = [1, 2, 3]
    s = 0
    for x in xs:
        s = s + x
        if x == 1:
            xs[2] = 100
    return s


def loop_append_grows():
    xs = [1]
    n = 0
    for x in xs:
        n = n + 1
        if n < 3:
            xs.append(x + 1)
    return n


def sorted_fresh():
    xs = [3, 1, 2]
    ys = sorted(xs)
    return (ys[0], xs[0], ys is xs)


def max_min_list():
    xs = [3, 1, 4]
    return (max(xs), min(xs))


def truthy_list():
    if []:
        return 1
    if [0]:
        return 2
    return 3


def unpack_list():
    a, b = [1, 2]
    return a * 10 + b


def return_list(n):
    return [n, n + 1, [n + 2]]


def return_self_cycle():
    xs = [1]
    xs.append(xs)
    return xs


def shared_tail():
    inner = [7]
    outer = [inner, inner]
    outer[0][0] = 9
    return outer[1][0]


def eq_selfref():
    xs = [1]
    xs.append(xs)
    return xs == xs


def eq_two_cycles():
    xs = [1]
    xs.append(xs)
    ys = [1]
    ys.append(ys)
    return xs == ys


def list_in_dict(n):
    d = {0: [1, n]}
    d[0].append(n + 1)
    return (len(d[0]), d[0][2])


def dict_unhashable_key():
    d = {}
    return d[[1]]


def loop_pop_skips():
    xs = [1, 2, 3]
    seen = 0
    for x in xs:
        seen = seen + 1
        xs.pop()
    return seen


def store_exc_state(v):
    xs = [0]
    xs[0] = v
    return xs[0] // 0


def ins_at(i, v):
    xs = [1, 2, 3]
    xs.insert(i, v)
    return xs


def ins_empty(v):
    xs = []
    xs.insert(5, v)
    return xs


def ins_alias(v):
    xs = [1, 2]
    ys = xs
    ys.insert(0, v)
    return xs[0]


def ins_ret():
    xs = [1]
    return xs.insert(0, 0)


def ins_badidx():
    xs = [1]
    xs.insert("a", 1)
    return xs


def ins_arity():
    xs = [1]
    xs.insert(1)
    return xs


def insort_right(a, x, lo=0, hi=None):
    if hi is None:
        hi = len(a)
    while lo < hi:
        mid = (lo + hi) // 2
        if x < a[mid]:
            hi = mid
        else:
            lo = mid + 1
    a.insert(lo, x)


def ins_insort(x):
    a = [1, 3, 5, 7]
    insort_right(a, x)
    return a
