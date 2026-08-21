"""seq_lab — pass 3's value tiers at FUNCTION level (checks-only).

Tuple/namedtuple slices, tuple repetition, sum(it[, start]), tuple(it),
and range as an immediate value (materialize-per-use). The loud frontier
is pinned by refusal probes: range ==/indexing/membership/unpacking/
boundary, list slices, str repetition.
"""

from collections import namedtuple

Move = namedtuple("Move", "i j prom")


def slice_tuple(a, b):
    t = (10, 20, 30, 40, 50, 60, 70, 80)
    return t[a:b]


def slice_computed(i):
    # the padding loop's shape: computed bounds into an 8-wide row
    t = (10, 20, 30, 40, 50, 60, 70, 80)
    return t[i * 2 : i * 2 + 2]


def slice_step(k):
    t = (1, 2, 3, 4, 5, 6)
    return (t[::k], t[4:1:-1], t[-3:])


def slice_move(i):
    # a namedtuple slice is a PLAIN tuple (the class does not survive)
    m = Move(i, i + 7, "q")
    return m[0:2]


def repeat(n):
    return (0,) * n + (7,) * 2


def repeat_left(n):
    return n * (1, 2)


def repeat_bool():
    return (1, 2) * True


def sum_ints(n):
    return sum((1, 2, 3, n))


def sum_start(n):
    return sum([1, 2], n)


def sum_tuples():
    # the padding loop's fold: tuple concatenation from an empty start
    return sum(((1,), (2, 3)), ())


def sum_gen(n):
    return sum(i * i for i in range(n))


def sum_str_start():
    return sum([1], "x")


def sum_str_elems():
    return sum("ab")


def sum_arity():
    return sum(1, 2, 3)


def tuple_of_str(s):
    return tuple(s)


def tuple_of_list(n):
    xs = [1, 2, n]
    xs.append(4)
    return tuple(xs)


def tuple_of_gen(n):
    return tuple(2 * i for i in range(n))


def tuple_of_range(n):
    return tuple(range(n, 0, -1))


def tuple_of_int():
    return tuple(7)


def range_len(a, b, s):
    return len(range(a, b, s))


def range_for(n):
    acc = 0
    for i in range(n):
        acc = acc + i * i
    return acc


def range_reiter(n):
    # a range is RE-ITERABLE (it is not an iterator): both loops see the
    # full sequence — materialize-per-use is what makes this exact
    r = range(n)
    a = 0
    for i in r:
        a = a + i
    b = 0
    for i in r:
        b = b + i
    return (a, b)


def range_truthy(n):
    if range(n):
        return 1
    return 0


def range_zero_step():
    return range(1, 5, 0)


def range_next():
    return next(range(3))


def range_extremum(n):
    return (max(range(n)), min(range(n)))


def range_empty_max():
    return max(range(0))


def enum_range(n):
    acc = 0
    for i, v in enumerate(range(3, 3 + n)):
        acc = acc + i * v
    return acc


def range_eq(n):
    return range(n) == range(n)


def range_index(n):
    return range(n)[0]


def range_in(n):
    return 2 in range(n)


def range_boundary(n):
    return range(n)


def range_unpack():
    a, b = range(2)
    return a


def list_slice_loud(n):
    return [1, 2, 3][0:n]


def str_repeat_loud(n):
    return "ab" * n


# pass 5 (docs/memory-model.md "Left shift and bitwise or"): the
# post-#158 shipped file's integer ops -- `1 << 63` (the deadline
# sentinel) and `live |= ...` (bound()'s fold).

def shl(a, b):
    return a << b


def shl_deadline():
    # the shipped __init__ line's shape
    nodes, deadline = 0, 1 << 63
    return deadline - nodes


def bor(a, b):
    # bool|bool returns a BOOL, any int operand an int -- the harness's
    # typed JSON pins the type, not just the value
    return a | b


def bor_aug(n):
    # bound()'s fold shape: `live |= <bool>` stays a bool throughout
    live = False
    for i in range(n):
        live |= i == 2
    return live


def bor_neg(a):
    # a negative operand COMPUTES -- pass 5's refusal ("infinite two's
    # complement is not guessed") was a design-time prediction, and the
    # measurement retired it: Lean's `Int.negSucc n` IS the complement
    # representation, so `-1 | 4` is exact, not guessed
    return a | 4


def band(a, b):
    # `&` with the full int semantics, negatives included; bool&bool is a
    # BOOL and any int operand makes it an int (the typed JSON pins the
    # type, not just the value)
    return a & b


def band_aug(n):
    # `&=` rides the SAME operator entry as `&` (one ALLOWED_BINOPS row
    # buys both forms), and folds a shrinking mask
    mask = 0b1111
    for i in range(n):
        mask &= 0b0111 << i
    return mask


def band_big():
    # unbounded ints: no word size anywhere in the construction
    return ((1 << 100) - 1) & 0xFF


def band_set():
    # `{1} & {2}` is set INTERSECTION, not a TypeError -- and the model
    # already survives it: a set operand is a heap ref, so evalBinOp's
    # `.ref` arm refuses LOUDLY before the TypeError fallback
    return set([1, 2]) & set([2, 3])


def fmt_spread(i, j):
    # a namedtuple IS a tuple (PyTuple_Check succeeds on the subclass),
    # so `%` SPREADS it -- treating it as one argument would fabricate
    # an arity error for a program CPython runs
    return "%s/%s/%r" % Move(i, j, "")


def fmt_spread_arity(i, j):
    # the spread's other half: three arguments, one conversion
    return "%s" % Move(i, j, "")


# The arity TypeError in CPython's OWN two shapes (2026-08-16). A
# namedtuple's `__new__` is an eval'd LAMBDA whose first parameter is
# `_cls`, so CPython names `<lambda>` and counts one higher than the field
# count -- the model used to say `Move() takes 3 positional arguments but
# 1 were given`, which is the wrong callee, the wrong shape AND the wrong
# counts. Measured live on 3.9.19.


def move_few(i):
    # too FEW is the MISSING form, naming the parameters not reached
    return Move(i)


def move_none():
    # three names, so the Oxford comma appears
    return Move()


def move_many(i):
    # too MANY is the TAKES form, and the counts include `_cls`
    return Move(i, i, i, i)


# `range()` names the OFFENDING OBJECT's type, never its own requirements
# (the three-argument arm used to answer `range() arguments must be
# integers`, a sentence CPython 3.9 does not produce), and it names the
# FIRST bad argument left to right.


def range3_step(n):
    return range(1, n, [3])


def range3_first(n):
    return range([n], [n], [n])


def range3_str(n):
    return range(1, n, "a")


def range1_dict():
    # a HEAP operand: the type name must be resolved through the heap, or
    # the message carries `typeName`'s "object" placeholder
    return range({1: 2})


# §L39 rung 1 (docs/completeness.md): the four operators the grammar
# census measured REFUSED while their siblings ran. `<<`, `|` and `&`
# landed in the tail batch; `>>`, `^`, unary `+` and unary `~` were left
# out with nothing recorded about it, and one `print(5 ^ 3)` found it.


def shr(a, b):
    # `>>` is CPython's ARITHMETIC shift: it rounds toward -inf, which is
    # `Int.fdiv` by `2 ** b` (`-5 >> 1 == -3`, not -2). bool operands DROP
    # boolness -- the typed JSON pins the type, not just the value
    return a >> b


def shr_aug(n):
    # `>>=` rides the SAME operator entry as `>>` (one ALLOWED_BINOPS row
    # buys both forms)
    x = 1 << n
    for i in range(n):
        x >>= 1
    return x


def bxor(a, b):
    # `^` with the full int semantics, negatives included; bool^bool is a
    # BOOL and any int operand makes it an int
    return a ^ b


def bxor_aug(n):
    # the checksum fold: `h ^= i` over a range
    h = 0
    for i in range(n):
        h ^= i
    return h


def bxor_big():
    # unbounded ints: no word size anywhere in the construction
    return ((1 << 100) - 1) ^ 0xFF


def uadd(a):
    # unary `+` is the identity on an int and DROPS boolness (`+True` is
    # 1, an int) -- `bool` has no `__pos__`, so int's slot runs
    return +a


def invert(a):
    # `~x` is `-x - 1`, two's complement by definition rather than a
    # bit-level guess; `~True` is -2
    return ~a


def invert_mask(a):
    # the mask idiom the rung exists for
    return a & ~0b1010


def bitwise_all(a, b):
    # the four together, in the shape hashing code writes them
    return ((a ^ b) >> 2) & ~(+b)
