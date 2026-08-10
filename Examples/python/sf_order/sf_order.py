"""sf_order — sunfish's MOVE-ORDERING surface, end to end (H6).

`Position.gen_moves` and `Position.value` are VERBATIM from the shipped
sunfish.py (byte-identical method bodies), `directions`/`piece`/the
constants likewise; `pst` is the PADDED table — CPython's own output of
the shipped padding loop (`for k, table in pst.items(): ...`), generated
by importing the shipped file and dumping `sf.pst`, because the padding
loop itself (lambda + genexp over `.items()`) is still outside the
module-init tier. CPython remains the oracle for every row.

`order_from` carries the shipped ordering line verbatim
(sunfish.py line 412):

    sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)

— a generator expression DRAINED by `sorted`, ordered by CPython's
tuple comparison on `(value, Move)` pairs (ties fall to the Move tuple),
descending and STABLE. `move_order` flattens the result to boundary
scalars for the differential battery.
"""
from collections import namedtuple
from itertools import count

A1, H1, A8, H8 = 91, 98, 21, 28
N, E, S, W = -10, 1, 10, -1
directions = {
    "P": (N, N+N, N+W, N+E),
    "N": (N+N+E, E+N+E, E+S+E, S+S+E, S+S+W, W+S+W, W+N+W, N+N+W),
    "B": (N+E, S+E, S+W, N+W),
    "R": (N, E, S, W),
    "Q": (N, E, S, W, N+E, S+E, S+W, N+W),
    "K": (N, E, S, W, N+E, S+E, S+W, N+W)
}

piece = {"P": 100, "N": 280, "B": 320, "R": 479, "Q": 929, "K": 60000}
pst = {
    "P": (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 100, 100, 100, 100, 100, 100, 100, 100, 0,
        0, 178, 183, 186, 173, 202, 182, 185, 190, 0,
        0, 107, 129, 121, 144, 140, 131, 144, 107, 0,
        0, 83, 116, 98, 115, 114, 100, 115, 87, 0,
        0, 74, 103, 110, 109, 106, 101, 100, 77, 0,
        0, 78, 109, 105, 89, 90, 98, 103, 81, 0,
        0, 69, 108, 93, 63, 64, 86, 103, 69, 0,
        0, 100, 100, 100, 100, 100, 100, 100, 100, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
    "N": (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 214, 227, 205, 205, 270, 225, 222, 210, 0,
        0, 277, 274, 380, 244, 284, 342, 276, 266, 0,
        0, 290, 347, 281, 354, 353, 307, 342, 278, 0,
        0, 304, 304, 325, 317, 313, 321, 305, 297, 0,
        0, 279, 285, 311, 301, 302, 315, 282, 280, 0,
        0, 262, 290, 293, 302, 298, 295, 291, 266, 0,
        0, 257, 265, 282, 280, 282, 280, 257, 260, 0,
        0, 206, 257, 254, 256, 261, 245, 258, 211, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
    "B": (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 261, 242, 238, 244, 297, 213, 283, 270, 0,
        0, 309, 340, 355, 278, 281, 351, 322, 298, 0,
        0, 311, 359, 288, 361, 372, 310, 348, 306, 0,
        0, 345, 337, 340, 354, 346, 345, 335, 330, 0,
        0, 333, 330, 337, 343, 337, 336, 320, 327, 0,
        0, 334, 345, 344, 335, 328, 345, 340, 335, 0,
        0, 339, 340, 331, 326, 327, 326, 340, 336, 0,
        0, 313, 322, 305, 308, 306, 305, 310, 310, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
    "R": (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 514, 508, 512, 483, 516, 512, 535, 529, 0,
        0, 534, 508, 535, 546, 534, 541, 513, 539, 0,
        0, 498, 514, 507, 512, 524, 506, 504, 494, 0,
        0, 479, 484, 495, 492, 497, 475, 470, 473, 0,
        0, 451, 444, 463, 458, 466, 450, 433, 449, 0,
        0, 437, 451, 437, 454, 454, 444, 453, 433, 0,
        0, 426, 441, 448, 453, 450, 436, 435, 426, 0,
        0, 449, 455, 461, 484, 477, 461, 448, 447, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
    "Q": (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 935, 930, 921, 825, 998, 953, 1017, 955, 0,
        0, 943, 961, 989, 919, 949, 1005, 986, 953, 0,
        0, 927, 972, 961, 989, 1001, 992, 972, 931, 0,
        0, 930, 913, 951, 946, 954, 949, 916, 923, 0,
        0, 915, 914, 927, 924, 928, 919, 909, 907, 0,
        0, 899, 923, 916, 918, 913, 918, 913, 902, 0,
        0, 893, 911, 929, 910, 914, 914, 908, 891, 0,
        0, 890, 899, 898, 916, 898, 893, 895, 887, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
    "K": (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 60004, 60054, 60047, 59901, 59901, 60060, 60083, 59938, 0,
        0, 59968, 60010, 60055, 60056, 60056, 60055, 60010, 60003, 0,
        0, 59938, 60012, 59943, 60044, 59933, 60028, 60037, 59969, 0,
        0, 59945, 60050, 60011, 59996, 59981, 60013, 60000, 59951, 0,
        0, 59945, 59957, 59948, 59972, 59949, 59953, 59992, 59950, 0,
        0, 59953, 59958, 59957, 59921, 59936, 59968, 59971, 59968, 0,
        0, 59996, 60003, 59986, 59950, 59943, 59982, 60013, 60004, 0,
        0, 60017, 60030, 59997, 59986, 60006, 59999, 60040, 60018, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ),
}

Move = namedtuple("Move", "i j prom")


class Position(namedtuple("Position", "board score wc bc ep kp")):
    """The shipped shape; gen_moves/value verbatim."""

    def gen_moves(self):
        # For each of our pieces, iterate through each possible 'ray' of moves,
        # as defined in the 'directions' map. The rays are broken e.g. by
        # captures or immediately in case of pieces such as knights.
        # NB: `in <literal-str>` is ~30% faster than the equivalent .isupper() /
        # .isspace() / .islower() method calls in CPython; this matters because
        # these checks run millions of times per search.
        for i, p in enumerate(self.board):
            if p not in "PNBRQK":
                continue
            for d in directions[p]:
                for j in count(i + d, d):
                    q = self.board[j]
                    # Stay inside the board, and off friendly pieces
                    if q in " \nPNBRQK":
                        break
                    # Pawn move, double move and capture
                    if p == "P":
                        if d in (N, N + N) and q != ".": break
                        if d == N + N and (i < A1 + N or self.board[i + N] != "."): break
                        if (
                            d in (N + W, N + E)
                            and q == "."
                            and j not in (self.ep, self.kp, self.kp - 1, self.kp + 1)
                            #and j != self.ep and abs(j - self.kp) >= 2
                        ):
                            break
                        # If we move to the last row, we can be anything
                        if A8 <= j <= H8:
                            for prom in "NBRQ":
                                yield Move(i, j, prom)
                            break
                    # Move it
                    yield Move(i, j, "")
                    # Stop crawlers from sliding, and sliding after captures
                    if p in "PNK" or q in "pnbrqk":
                        break
                    # Castling, by sliding the rook next to the king
                    if i == A1 and self.board[j + E] == "K" and self.wc[0]:
                        yield Move(j + E, j + W, "")
                    if i == H1 and self.board[j + W] == "K" and self.wc[1]:
                        yield Move(j + W, j + E, "")

    def value(self, move):
        i, j, prom = move
        p, q = self.board[i], self.board[j]
        # Actual move
        score = pst[p][j] - pst[p][i]
        # Capture
        if q.islower():
            score += pst[q.upper()][119 - j]
        # Castling check detection
        if abs(j - self.kp) < 2:
            score += pst["K"][119 - j]
        # Castling
        if p == "K" and abs(i - j) == 2:
            score += pst["R"][(i + j) // 2]
            score -= pst["R"][A1 if j < i else H1]
        # Special pawn stuff
        if p == "P":
            if A8 <= j <= H8:
                score += pst[prom][j] - pst["P"][j]
            if j == self.ep:
                score += pst["P"][119 - (j + S)]
        return score

    def king_capture(self):
        """The move that takes the opponent king, if any - i.e. the proof
        that this position was reached by an illegal move. Same test as
        gen_moves/value: the target is the king, or within one of the
        king-passant square (kp == 0 is safe: targets are >= A8 > 1).
        Serves double duty: found from a position it is the sentinel
        witness the search substitutes for a virtual cutoff; found from
        the null-rotation it says the side to move is in check."""
        return next((m for m in self.gen_moves()
                     if self.board[m.j] == "k" or abs(m.j - self.kp) < 2), None)


def order_from(pos):
    # the shipped ordering line, verbatim (sunfish.py line 412)
    return sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)


def move_order(board, ep, kp):
    pos = Position(board, 0, (True, True), (True, True), ep, kp)
    out = []
    for val, move in order_from(pos):
        out.append((val, move.i, move.j, move.prom))
    return out


def value_of(board, i, j, prom, ep, kp):
    pos = Position(board, 0, (True, True), (True, True), ep, kp)
    return pos.value(Move(i, j, prom))


def best_move(board, ep, kp):
    pos = Position(board, 0, (True, True), (True, True), ep, kp)
    val, move = order_from(pos)[0]
    return (val, move.i, move.j, move.prom)
