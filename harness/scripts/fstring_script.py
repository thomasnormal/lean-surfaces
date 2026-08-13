"""End-to-end f-string script (tail batch, construct 2).

Exercises the lowering through the control shell: a top-level `for` writes
a binding, an f-string built from it is printed, and a field holds a call
whose result is interpolated. If the lowering to `"a" + str(x) + "b"` is
faithful, stdout here is byte-identical to CPython 3.9.
"""


def label(n):
    return f"item-{n}"


total = 0
for i in range(3):
    total = total + i
    print(f"{label(i)}: running total {total}")

xs = ["a", "b"]
print(f"list={xs} count={len(xs)}")
print(f"{{literal}} and empty:{''}")
print(f"done, total={total}")
