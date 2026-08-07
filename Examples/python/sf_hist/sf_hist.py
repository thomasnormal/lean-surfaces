"""sunfish's history/list patterns, at the slice the H2 tier admits.

The driving loop keeps a LIST of positions and threads it BY REFERENCE
into the search machinery (sunfish.py: `hist.append(pos.move(move))` in
the main loop; `hist[-1]` for the current position; `self.history =
set(hist)` and the searcher's list arguments). Positions are namedtuples
(H3); here the history entries are their int scores — the LIST mechanics
(append through an alias, negative indexing, in-place update seen by
every holder of the reference) are exactly sunfish's, and they are what
`Val.listV` could never express.
"""


def push(hist, score):
    # driving loop: hist.append(...) — mutates the CALLER's list
    hist.append(score)
    return len(hist)


def current(hist):
    # sunfish everywhere: hist[-1] is the position to move from
    return hist[-1]


def drive(n):
    # the driving-loop shape: seed history, push a move, read it back
    hist = [n]
    push(hist, n + 1)
    push(hist, n + 2)
    return (len(hist), current(hist))


def poke_first(a, b):
    # the aliasing acceptance: if a and b are the SAME list, the write
    # through a is visible through b — unstatable under value semantics
    a[0] = 99
    return b[0]


def rotate_scores(hist):
    # in-place update pattern (sunfish's tp_score-style overwrites,
    # list-shaped): negate every entry, in place, visible to the caller
    i = 0
    while i < len(hist):
        hist[i] = -hist[i]
        i = i + 1
    return None
