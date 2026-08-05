def bound_rec(scores, gamma, i, best):
    # sunfish.py, Searcher.bound: the fail-soft best loop with beta cutoff
    #     best = -MATE_UPPER
    #     for move, score in moves():
    #         best = max(best, score)
    #         if best >= gamma:
    #             break
    # written as index-carrying recursion (the children's negated search
    # results are precomputed in `scores`). This is the exact object
    # sunfish's formal/Sunfish/Bound.lean models as `searchMoves`.
    # Transliteration notes (out-of-tier constructs replaced):
    #   * for-over-generator  ->  recursion over an index (no For, no
    #     generators; the while-loop form is Examples/python/sf_bound_loop,
    #     currently stuck on py_vcgen's symbolic-subscript gap)
    #   * max(best, score)    ->  if scores[i] > b  (no call:max)
    #   * -MATE_UPPER is inlined at the call site (no module globals in v0)
    if i >= len(scores):
        return best
    b = best
    if scores[i] > b:
        b = scores[i]
    if b >= gamma:
        return b
    return bound_rec(scores, gamma, i + 1, b)
