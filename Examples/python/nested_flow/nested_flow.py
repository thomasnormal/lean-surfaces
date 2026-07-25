def first_factor(n: int) -> int:
    """Smallest prime factor of n (n itself when n is prime), for n >= 2.

    Trial division where the divisibility test is itself a loop:
    the inner while subtracts i from a copy of n until it drops below i
    (break) or hits zero, so ``m == 0`` afterwards means ``i divides n``.
    Control flow is deliberately layered: a while nested in a while, a
    break inside an if in the inner loop, and a return out of the middle
    of the outer loop.
    """
    i = 2
    while i * i <= n:
        m = n
        while 0 < m:
            if m < i:
                break
            m = m - i
        if m == 0:
            return i
        i = i + 1
    return n
