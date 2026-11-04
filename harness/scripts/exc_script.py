"""leanpy corpus: the exceptions tier at module level -- a top-level
try/except (delegated whole to the interpreter by the live-suffix
shell), raise-through-call, and the retained-state covenant."""


class Boom(Exception): pass


def f(n):
    if n > 3:
        raise Boom
    return n * 2


total = 0
i = 0
while i < 6:
    try:
        total = total + f(i)
    except Boom:
        total = total + 100
    i = i + 1
print(total)
