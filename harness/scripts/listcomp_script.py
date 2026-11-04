"""leanpy corpus: LIST COMPREHENSIONS — a payoff row.

`ListComp` was the top in-repo construct on the static ladder and shipped
as a loud `Unsupported` leaf. It is now the SAME node as a generator
expression under a different `kind`, desugared at ingestion into
`list(<the genexp>)` — CPython's own compilation, so the capture census,
the walrus filter and the drain gate carry over verbatim, and the only
new interpreter piece is the `list(iterable)` constructor.

The old row printed the list itself, which is still loud (a container's
`repr` is not guessed — `print_container.py` pins that separately).
"""

xs = [i * i for i in range(10)]
print(len(xs))
print(xs[3])
print(sum(xs))

evens = [i for i in range(10) if i % 2 == 0]
print(len(evens))
print(evens[4])


def scaled(s, k):
    # a capture: `k` is a parameter the body never rebinds
    return [ord(c) + k for c in s]


print(scaled("abc", 1)[2])
print(len(list("hello")))
