MATE_UPPER = 69290


def bound_loop(scores, gamma):
    # sunfish.py, Searcher.bound -- the fail-soft cutoff loop. Original:
    #     best = -MATE_UPPER
    #     for move, score in moves():
    #         best = max(best, score)
    #         if best >= gamma:
    #             ...store killer, tp_score...
    #             break
    #     return best
    # The SOLE remaining transliteration: the generator moves() is
    # precomputed into the list `scores` (generators are the last sunfish
    # ladder step). MATE_UPPER resolves from the module constant (G1),
    # `for` and max() are in tier (step 2) -- compare sf_bound_loop /
    # sf_bound_rec, whose pre-step-2 forms had to inline the constant,
    # index-loop the list, and if/else the max.
    best = -MATE_UPPER
    for score in scores:
        best = max(best, score)
        if best >= gamma:
            break
    return best
