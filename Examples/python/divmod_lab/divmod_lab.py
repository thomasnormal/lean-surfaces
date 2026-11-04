def pair(left, right):
    return divmod(left, right)


def by_one(value):
    return divmod(value, 1)


def generated():
    return tuple(divmod(value, 3) for value in range(-4, 5))


def generator_parameter(divmod):
    return tuple(divmod(value, 2) for value in range(2))


def generator_nested():
    def divmod(left, right):
        return 77
    return tuple(divmod(value, 2) for value in range(2))


def generator_local():
    divmod = 5
    return tuple(divmod(value, 2) for value in range(2))


def generator_bool(bool):
    return tuple(bool(value) for value in range(2))


def arity_zero():
    return divmod()


def arity_one():
    return divmod(1)


def arity_three():
    return divmod(1, 2, 3)


def shadow(value):
    def divmod(left, right):
        return left + right
    return divmod(value, 2)


def arity_effects():
    values = []
    try:
        divmod(values.append(0), values.append(1), values.append(2))
    except TypeError:
        return values


def exception_before_arity():
    return divmod(1, 1 // 0, 3)


def kwargs():
    return divmod(a=7, b=3)


def first_class():
    operation = divmod
    return operation(7, 3)
