"""leanpy v0 corpus (H3): a class with mutable self driven from the live
suffix through a module function — instance state persists across the
whole script run (one world)."""


class Acc:
    def __init__(self, start):
        self.total = start
        self.hits = 0

    def add(self, v):
        self.total = self.total + v
        self.hits = self.hits + 1
        return self.total


def drive(a, x, y):
    a.add(x)
    a.add(y)
    return (a.total, a.hits)


def fresh_sum(x, y):
    a = Acc(0)
    a.add(x)
    a.add(y)
    return a.total


print(fresh_sum(2, 3))
print(fresh_sum(10, -4))
