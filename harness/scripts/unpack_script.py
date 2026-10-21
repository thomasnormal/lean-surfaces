"""Top-level starred assignment targets execute in module scope."""

a, *middle, z = (1, 2, 3, 4)
print(a)
print(middle)
print(z)

head, *tail = "abc"
print(head)
print(tail)
