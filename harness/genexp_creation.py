"""Generator-expression creation checks run before the first iteration."""


def gen_iter_deferred(value):
    g = (x for x in value)
    return 1


def gen_iter_live_list():
    values = [1, 2]
    g = (x for x in values)
    values.append(3)
    return next(g) + next(g) + next(g)


def gen_values():
    yield 1
    yield 2


def gen_iter_generator():
    g = (x for x in gen_values())
    return next(g) + next(g)


def gen_iter_dict():
    values = {"a": 1}
    g = (x for x in values)
    return 1
