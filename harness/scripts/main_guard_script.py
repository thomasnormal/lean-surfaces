"""leanpy corpus: `if __name__ == "__main__":` — the guard that every real
Python program is wrapped in.

`__name__` is bound by CPython's import machinery, not by a statement, so
reading it used to refuse loudly and this shape was unreachable. leanpy
runs a FILE AS A PROGRAM, where the answer is fixed: `__main__`. The
runner supplies it as a marshalled global (docs/memory-model.md §effects,
the `argv` family) by prepending the binding to the prefix view the module
fold sees, so the guard is TRUE here exactly as under CPython — and the
`else` arm below stays dead in both.
"""


def triangle(n):
    total = 0
    i = 1
    while i <= n:
        total = total + i
        i = i + 1
    return total


if __name__ == "__main__":
    print(triangle(4))
    print(triangle(10))
else:
    print("imported")
