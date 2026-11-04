"""leanpy v0 corpus (H4 generators): a suspended frame driven from the
live suffix -- lazy consumption of an infinite generator, abandonment by
`break`, and resumption by a second consumer."""


def naturals():
    i = 0
    while True:
        yield i
        i += 1


def upto(n):
    i = 0
    while i < n:
        yield i
        i += 1


def first_over(k):
    # terminates only because the generator is lazy
    for x in naturals():
        if x > k:
            return x
    return -1


def two_phase(n):
    g = upto(n)
    a = -1
    for x in g:
        a = x
        break
    b = -1
    for y in g:
        b = y
        break
    return a * 100 + b


def total(n):
    s = 0
    for x in upto(n):
        s += x
    return s


print(first_over(4))
print(two_phase(5))
print(total(6))
print(next(upto(3)))
print(next(upto(0), -1))

g = upto(3)
n = 0
while n < 2:
    print(next(g))
    n = n + 1
print(next(g, 99))
print(next(g, 99))

# H4: genexps and the builtin iterators
print(next((x * x for x in upto(4) if x > 1), -1))

tot = 0
for i, c in enumerate("PNBRQK"):
    tot += i * ord(c)
print(tot)

# (`itertools.count` is exercised by the gen_lab differential rows and
# `#py_check`s instead: leanpy v0 cannot run a module containing an
# import at all, so a corpus script cannot import it -- recorded,
# docs/backlog.md.)
