"""leanpy v0 corpus (H5 strings): slices and the swapcase/isupper/index
trio driven from the live suffix — rotate's flip chain and move's put
shape included."""


def flip(s):
    return s[::-1].swapcase()


def put(board, i, p):
    return board[:i] + p + board[i + 1 :]


def find(s, t):
    return s.index(t)


print(flip("RNBQKBNRrnbqkbnr"))
print(put("abcde", 2, "X"))
print(find("abcab", "ab"))

board = "KQkq"
if board.isupper():
    print("all-upper")
else:
    print(board[1:3])

n = 0
while n < 3:
    print("abcdef"[n::2])
    n = n + 1
