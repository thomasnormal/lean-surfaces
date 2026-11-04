"""leanpy v0 corpus: functions reading module-global dicts (the sunfish
shape) — prefix-bound tables, live suffix driving them."""
piece = {"P": 100, "N": 280, "B": 320, "R": 479, "Q": 929, "K": 60000}
MATE_LOWER = piece["K"] - 10 * piece["Q"]
MATE_UPPER = piece["K"] + 10 * piece["Q"]


def val(p):
    return piece[p]


def clamp_score(s):
    if s < MATE_LOWER:
        return MATE_LOWER
    if s > MATE_UPPER:
        return MATE_UPPER
    return s


print("window", MATE_LOWER, MATE_UPPER)
print(val("K"), val("P"))
print(clamp_score(999999), clamp_score(-999999), clamp_score(1234))
