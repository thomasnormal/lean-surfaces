from collections import namedtuple

Pair = namedtuple("Pair", "x y")


def rendered_lengths(value):
    return (
        len(str(value)),
        len("%s" % (value,)),
        len("%r" % (value,)),
        len("%d" % (value,)),
        len(str((value,))),
        len(str([value])),
        len(str({value: 7})),
        len(str({"value": value})),
        len(str(range(value))),
        len(str(range(value, value))),
        len(str(range(0, 2, value))),
        len(str(Pair(value, 7))),
        len(f"{value}"),
    )


print(str(0), str(-27), str(True), str(False), str(None))
print("%s|%r|%d" % (True, False, True))
print(str((1, -2)), str([True, 0, -2]), str({0: -2}))
print(str(range(0)), str(range(-2, -2)), str(range(0, 2, -2)))
print(str(Pair(-27, 7)))
print(rendered_lengths(10 ** 640 - 1))
print(rendered_lengths(-(10 ** 640 - 1)))
