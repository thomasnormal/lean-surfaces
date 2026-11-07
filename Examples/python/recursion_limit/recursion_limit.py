def depth(n):
    if n == 0:
        return 0
    return depth(n - 1) + 1
