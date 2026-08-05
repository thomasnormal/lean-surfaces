def bound(tree, gamma, depth):
    # sunfish.py, Searcher.bound stripped to its logical skeleton -- the
    # exact object formal/Sunfish/Bound.lean models as `bound`/`searchMoves`:
    # depth-limited fail-soft negamax with the null-window flip 1-gamma and
    # the early cutoff on best >= gamma. No TT, no null move, no killer.
    # A game tree is a pair  tree = (eval, children).
    # Transliteration notes:
    #   * -MATE_UPPER -> literal -69290 (no module globals in v0)
    #   * max(...)    -> if  (no call:max)
    #   * s = 0 pre-declared before the loop: a variable first created
    #     inside a loop body defeats the loop tactics (fix F-2)
    if depth <= 0:
        return tree[0]
    kids = tree[1]
    best = -69290
    s = 0
    i = 0
    while i < len(kids):
        s = -bound(kids[i], 1 - gamma, depth - 1)
        if s > best:
            best = s
        if best >= gamma:
            break
        i += 1
    return best
