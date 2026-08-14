"""Module-level def aliasing, happy path (docs/memory-model.md)."""


def greet(n):
    return n * 2 + 1


def flip(s):
    return s[::-1]


hail = greet
rev = flip
also = hail

print(hail(3))
print(also(4))
print(rev("abc"))
print(greet(3) == hail(3))
