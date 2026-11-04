"""leanpy v0 corpus: defs first, then a top-level loop driving them."""


def fib(n):
    a = 0
    b = 1
    i = 0
    while i < n:
        t = a + b
        a = b
        b = t
        i = i + 1
    return a


n = 0
while n <= 10:
    print(n, fib(n))
    n = n + 2
print("fib(20) =", fib(20))
