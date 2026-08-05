A1, H1, A8, H8 = 91, 98, 21, 28
N, E, S, W = -10, 1, 10, -1
MATE_UPPER = 69290
QS = 40
QS_A = 140
EVAL_ROUGHNESS = 15


def rotate_sq(i):
    # sunfish.py, Position.rotate: the 120-board point reflection 119 - i.
    return 119 - i


def corners_sum():
    return A1 + H1 + A8 + H8


def is_back_rank_white(i):
    # sunfish.py, gen_moves promotion test: A8 <= j <= H8.
    return A8 <= i and i <= H8


def loss():
    # sunfish.py, Searcher.bound: best = -MATE_UPPER.
    return -MATE_UPPER
