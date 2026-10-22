"""`__slots__` stores only declared attributes on each instance.

The successful write/read path and the faithful AttributeError for a name
outside the slot set are both observed through the script surface.  The
class itself remains a default-protocol H3 instance; slots only change its
storage rule.
"""


class Cell:
    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value


def read(value):
    c = Cell(value)
    return c.value


def rejected(value):
    c = Cell(value)
    c.other = value
    return 0


print(read(7))
try:
    rejected(3)
except AttributeError:
    print("blocked")
