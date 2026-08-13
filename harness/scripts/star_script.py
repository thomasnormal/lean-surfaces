"""star_script — starred DISPLAYS at the top level, run end to end.

Every display here is lowered by the extractor into `list(…)`/`tuple(…)`
concatenation (docs/memory-model.md §starred displays). The stdout is
compared byte-for-byte against CPython 3.9, which is what pins the two
things a lowering most easily breaks: the ORDER the operands run in, and
the freshness of the list a display builds.
"""


def p(x):
    print("eval", x)
    return x


a = [1, 2]
t = (3, 4)

print([*a, 5])
print([0, *a])
print((*t, 5))
print([*a, *t])
print([*"ab"])
print([*range(3)])
print([*[]])
print([1, *a, 9, *a])

# evaluation order: left to right, straight across the star
print([p(0), *a, p(9)])

# the display ALLOCATES — `b` is a copy, so `a` is untouched
b = [*a]
b.append(7)
print(a)
print(b)

total = 0
for x in [*a, *t]:
    total += x
print("total", total)
