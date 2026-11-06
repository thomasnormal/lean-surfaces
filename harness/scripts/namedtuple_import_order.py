"""A static namedtuple table must not move its import before the call."""

P = namedtuple("P", "x")
from collections import namedtuple
print(P(1).x)
