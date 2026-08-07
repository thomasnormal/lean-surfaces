"""leanpy v0 corpus: the dict tier from a script."""
piece = {"P": 100, "N": 280, "B": 320, "R": 479, "Q": 929, "K": 60000}
MATE_LOWER = piece["K"] - 10 * piece["Q"]
MATE_UPPER = piece["K"] + 10 * piece["Q"]
print("window", MATE_LOWER, MATE_UPPER)
tt = {}
tt[1] = MATE_UPPER
tt[2] = tt.get(1, 0) - 1
print(tt[2], len(tt), 3 in tt)
