"""leanpy v0 corpus: a constant bound before a def that reads it — the
G1-faithful prefix makes this exact interleaving faithful (the def
precedes all LIVE statements, which is what matters)."""
x = 1


def f():
    return x


print(f())
