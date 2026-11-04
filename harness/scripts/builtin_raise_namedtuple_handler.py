from collections import namedtuple

ValueError = namedtuple("ValueError", "x")

try:
    print("body succeeded")
except ValueError:
    print("wrong handler")

try:
    print("before exception")
    raise TypeError
except ValueError:
    print("wrong handler")
