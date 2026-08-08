"""The namedtuple sunfish artifact: the REAL Position/Move/Entry SHAPES
(sunfish.py lines 172/303 — Move and Entry are plain namedtuples;
Position is the shipped shape, `class Position(namedtuple(...))` with a
method: instantiation builds the IMMEDIATE value through the subclass —
H5 — and METHOD CALLS dispatch through the flattened qualified functions
with self bound to the immutable VALUE) flowing through construction, field access,
equality, iteration, unpacking, and — the transposition-table pattern —
dict-keying by tuples CONTAINING a Position. Every in-tier function
returns boundary scalars/tuples (namedtuple results themselves refuse
the public freeze loudly — the recorded boundary decision)."""
from collections import namedtuple

Move = namedtuple("Move", "i j prom")
Entry = namedtuple("Entry", "lower upper")


class Position(namedtuple("Position", "board score wc bc ep kp")):
    """The real sunfish shape: a namedtuple SUBCLASS carrying methods."""

    def mirror(self):
        return Position(self.board, -self.score, self.bc, self.wc,
                        self.ep, self.kp)


def move_fields(i, j):
    m = Move(i, j, "q")
    return (m.i, m.j, m.prom)


def move_eq(i, j):
    m = Move(i, j, "")
    return (m == (i, j, ""), (i, j, "") == m, m == Move(i, j, ""), m != Move(j, i, ""))


def entry_window(lo, hi):
    e = Entry(lo, hi)
    return e.upper - e.lower


def mk_move(i, j):
    return Move(i, j, "")


def position_fields(score, ep):
    pos = Position("board", score, (True, True), (False, True), ep, 0)
    return (pos.score, pos.board, pos.wc[0], pos.bc[0], pos.ep, len(pos))


def tp_score_flow(score, depth):
    pos = Position("brd", score, (True, True), (True, True), 0, 0)
    tp = {}
    tp[(pos, depth, True)] = Entry(score - 1, score + 1)
    e = tp.get((pos, depth, True), Entry(-10, 10))
    miss = tp.get((pos, depth, False), Entry(-10, 10))
    hit2 = tp[(Position("brd", score, (True, True), (True, True), 0, 0), depth, True)]
    return (e.lower, e.upper, miss.lower, miss.upper, hit2.upper,
            (pos, depth, True) in tp, len(tp))


def unpack_move(i, j):
    m = Move(i, j, "p")
    a, b, c = m
    return (a, b, c)


def iterate_entry(lo, hi):
    s = 0
    for v in Entry(lo, hi):
        s = s + v
    return s


def move_index(i, j):
    m = Move(i, j, "n")
    return (m[0], m[-1], max(Entry(i, j)))


def bad_arity(i):
    m = Move(i)
    return 0


def missing_field(i, j):
    m = Move(i, j, "")
    return m.k


def asdict_is_loud(i, j):
    m = Move(i, j, "")
    return m._asdict()


def fields_are_loud(i, j):
    m = Move(i, j, "")
    return m._fields


def mirror_is_loud(score):
    # the METHOD works; returning its Position RESULT refuses the boundary
    pos = Position("brd", score, (True, True), (False, False), 0, 0)
    return pos.mirror()


def bound_method_is_loud(score):
    pos = Position("brd", score, (True, True), (False, False), 0, 0)
    return pos.mirror


def mirror_score(score):
    pos = Position("brd", score, (True, True), (False, False), 3, 4)
    m = pos.mirror()
    return (m.score, m.board, m.wc[0], m.bc[0], m.ep, m.kp)


def ep_flip(ep, nullmove):
    # rotate's exact conditional subexpression shape (IfExp + and/not)
    return 119 - ep if ep and not nullmove else 0
