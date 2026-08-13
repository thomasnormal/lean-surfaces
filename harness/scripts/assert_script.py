"""assert as a PROGRAM: the statement at module top level, inside a
top-level loop (through the `for` control shell), and inside a function
called from the top level -- then the failing one that ends the run, so
stdout up to the raise, the exit code, and the `AssertionError: message`
line are all differential at once.
"""


def check(n):
    assert n >= 0, "negative: " + str(n)
    return n * 2


print(check(3))

total = 0
for i in [1, 2, 3]:
    assert i < 10
    total = total + i
print(total)

assert total == 6, "top-level assert sees the loop's binding"
print("guards passed")

print(check(-1))
print("never reached")
