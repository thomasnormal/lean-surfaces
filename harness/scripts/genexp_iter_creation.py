"""A genexp performs GET_ITER when its object is created."""


def make(value):
    g = (x for x in value)
    return 1


print(make(5))
