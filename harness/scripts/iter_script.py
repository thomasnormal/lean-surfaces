"""leanpy v0 corpus (H5 iteration): container membership, `for` over a
str, and the ord/chr code-point pair, driven from the live suffix."""


def piece_test(q):
    return q in " \nPNBRQK"


def count_char(s, c):
    n = 0
    for ch in s:
        if ch == c:
            n += 1
    return n


def shift(s, k):
    out = ""
    for ch in s:
        out = out + chr(ord(ch) + k)
    return out


print(piece_test("P"))
print(piece_test("."))
print(count_char("banana", "a"))
print(shift("abc", 1))

# (prints inside a top-level `for` are loud in leanpy v0 — the shell has
# a `while` case only; collect instead and print the result)
proms = ""
for ch in "NBRQ":
    proms = proms + ch
print(proms)

d = 10
if d in (1, 10, 100):
    print("in the ray table")

board = "KQkq"
n = 0
while n < 4:
    if board[n] in "PNBRQK":
        print(ord(board[n]))
    n = n + 1
