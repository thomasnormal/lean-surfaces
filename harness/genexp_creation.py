"""Generator-expression creation checks run before the first iteration."""


def gen_iter_deferred(value):
    g = (x for x in value)
    return 1
