def bound_loop(scores, gamma):
    # sunfish.py, Searcher.bound: the fail-soft best loop (the model of
    # formal/Sunfish/Bound.lean's searchMoves), stripped of recursion --
    # the children's negated search results are precomputed in `scores`.
    # Original:
    #     best = -MATE_UPPER
    #     for move, score in moves():
    #         best = max(best, score)
    #         if best >= gamma:
    #             ...store killer...
    #             break
    # Transliteration notes (out-of-tier constructs replaced):
    #   * -MATE_UPPER is the literal -69290 (module-level constants are out
    #     of tier: no globals in v0)
    #   * for-over-generator  ->  while over an index (no For, no generators)
    #   * max(best, score)    ->  if scores[i] > best  (no call:max)
    #   * n = len(scores) hoisted out of the loop test: `while i < len(scores)`
    #     defeats py_vcgen -- the builtin lookup consults the loop's symbolic
    #     env tail (`Env.lookup tl "len"`) and the test gets stuck (fix
    #     candidate for lean-surfaces)
    best = -69290
    i = 0
    n = len(scores)
    while i < n:
        if scores[i] > best:
            best = scores[i]
        if best >= gamma:
            break
        i += 1
    return best
