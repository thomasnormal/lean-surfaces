def literal():
    return ...


def builtin():
    return Ellipsis


def identity(value):
    return value is ..., value is not ..., ... is value, ... is not value


def equal(value):
    return value == ..., value != ..., ... == value, ... != value


def rendering():
    return str(...), repr(...), f"{...}|{...!s}|{...!r}", "%s/%r" % (..., ...)


def truth(value):
    return bool(value), not value, value or 17, value and 23


def default(value=...):
    return value


def branch(value):
    if value:
        return ...
    return None


def keys():
    table = {...: 3}
    table[Ellipsis] = 4
    table[(...,)] = 5
    return len(table), table[...], table[(Ellipsis,)], ... in table, {...: 4} == {Ellipsis: 4}


def containers():
    values = [..., (...,), {...: ...}]
    return str(values), ... in [...], (...) in (...,), len(set((..., ...)))


def parameter_shadow(Ellipsis):
    return Ellipsis, ... is Ellipsis, str(...)


def generator():
    yield ...
    yield Ellipsis


def drain():
    return list(generator())


def sum_start():
    return sum((), ...)


def sum_bad():
    return sum((1,), ...)


def noniterable():
    return list(...)


def nonnumeric():
    return ... + 1
