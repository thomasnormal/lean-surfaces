MATE_UPPER = 69290


def bound(tree, gamma, depth):
    # sunfish.py, Searcher.bound stripped to its logical skeleton -- the
    # exact object formal/Sunfish/Bound.lean models as `bound`: depth-limited
    # fail-soft negamax with the null-window flip 1 - gamma and the
    # beta cutoff on best >= gamma. No TT, no null move, no killer.
    # A game tree is a pair  tree = (eval, children).
    # Sole transliteration vs the shipped loop: the generator moves() is the
    # precomputed children list tree[1] (generators are the last ladder
    # step). MATE_UPPER, `for`, and max() are all in tier now -- compare
    # Examples/python/sf_bound/sf_bound.py, the pre-step-2 form.
    if depth <= 0:
        return tree[0]
    best = -MATE_UPPER
    for kid in tree[1]:
        s = -bound(kid, 1 - gamma, depth - 1)
        best = max(best, s)
        if best >= gamma:
            break
    return best
