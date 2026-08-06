def lmr_amount(depth, i_m, val):
    # sunfish.py, Searcher.bound, VERBATIM:
    #     LMR = int(depth >= 4 and i_m >= 8 and val < 0)
    # (sf_arith carries the pre-B1 if/else transliteration of this line —
    # call:int was out of tier, benchmark fix F-5. Now provable as written.)
    return int(depth >= 4 and i_m >= 8 and val < 0)


def clamp_window(x, lo, hi):
    # The MTD-bi window clamp shape: max(lo, min(hi, x)).
    return max(lo, min(hi, x))


def dist(a, b):
    return abs(a - b)
