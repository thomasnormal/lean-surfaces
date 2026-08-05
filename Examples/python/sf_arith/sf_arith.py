def child_score(score, val):
    # sunfish.py, Position.move + rotate: the child position is built with
    # score identity  child.score = -(pos.score + pos.value(move))
    # (move() computes score + value, rotate() negates). This is the ValGame
    # structural property that formal/Sunfish/Tricks.lean's
    # futilityOK_discharged rests on.
    return -(score + val)


def futility_margin(score, val, gamma):
    # sunfish.py, Searcher.bound futility pruning. The code tests
    #   depth <= 1 and pos.score + val < gamma
    # and the comment claims
    #   "pos.score + val < gamma === -(pos.score + val) >= 1-gamma".
    # Returns 1 when the pruning branch is taken, else 0.
    if score + val < gamma:
        return 1
    return 0


def lmr_amount(depth, i_m, val):
    # sunfish.py, Searcher.bound deterministic LMR:
    #   LMR = int(depth >= 4 and i_m >= 8 and val < 0)
    # NOTE: int() in call position is out of the v0 tier (call:int, fix F-5),
    # so the truthiness cast is transliterated as if/else. Everything else is
    # verbatim.
    if depth >= 4 and i_m >= 8 and val < 0:
        return 1
    return 0
