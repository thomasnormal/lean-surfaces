"""H2 list script: a module-scope heap list, mutated by the live suffix
(append/pop/subscript-store) and threaded by reference through a
function call — the aliasing the value tier could not run."""

xs = [3, 1, 2]


def total(v):
    s = 0
    i = 0
    while i < len(v):
        s = s + v[i]
        i = i + 1
    return s


xs.append(5)
print(len(xs))
print(xs[-1])
print(total(xs))
xs.pop()
print(total(xs))
xs[0] = 40
print(total(xs))
