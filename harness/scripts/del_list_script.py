"""H2 heap-list deletion at module scope."""

xs = [1, 2, 3]
del xs[-1]
print(xs)
del xs[0]
print(xs)
