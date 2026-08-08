"""sunfish's `Searcher` shape through the H3 class tier: `__init__`
creating the transposition tables as heap dicts on `self`, and `bound`
mutating `self` across calls — the persistent-state pattern `CallsIn`
was built for (one search writes `tp_score`, the next call reads the
entry back instead of recomputing).

`pos`/`gamma` are ints here — sunfish's real `Position` is a namedtuple,
and H3 records the namedtuple decision (VALUE-like, immutable) without
implementing it yet; the SHAPE under proof is the real one: instance
dicts keyed by tuples, written by one method call, read by the next,
`self.nodes` counting every entry."""

MATE_UPPER = 69290


class Searcher:
    def __init__(self):
        self.tp_score = {}
        self.tp_move = {}
        self.nodes = 0

    def bound(self, pos, gamma):
        self.nodes = self.nodes + 1
        entry = self.tp_score.get((pos, gamma))
        if entry is not None:
            return entry
        if pos == 0:
            score = -MATE_UPPER
        else:
            score = gamma - 1
        self.tp_score[(pos, gamma)] = score
        self.tp_move[pos] = gamma
        return score

    def visited(self):
        return self.nodes


def bound_twice(pos, gamma):
    # the acceptance behavior: the second call is a table HIT — same
    # score, one more node, no new entry
    s = Searcher()
    a = s.bound(pos, gamma)
    b = s.bound(pos, gamma)
    return (a, b, s.visited(), len(s.tp_score))


def bound_two_positions(p1, p2, gamma):
    s = Searcher()
    a = s.bound(p1, gamma)
    b = s.bound(p2, gamma)
    return (a, b, s.nodes, len(s.tp_score))


def fresh_searchers(pos, gamma):
    # two searchers do not share tables (distinct instances)
    s = Searcher()
    t = Searcher()
    a = s.bound(pos, gamma)
    return (a, s.nodes, t.nodes, len(t.tp_score))
