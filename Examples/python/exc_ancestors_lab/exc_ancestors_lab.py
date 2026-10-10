class Signal(Exception):
    pass


class Box:
    pass


def empty_generator():
    if False:
        yield 1


def caught_arithmetic_identity(value):
    try:
        return 1 // 0
    except ArithmeticError:
        return value


def base_inventory(kind):
    try:
        if kind == 0:
            return len(0)
        if kind == 1:
            return int("bad")
        if kind == 2:
            return missing_ancestor_value
        if kind == 3:
            return ()[0]
        if kind == 4:
            return {1: 7}[2]
        if kind == 5:
            return Box().missing
        if kind == 6:
            assert False
        if kind == 7:
            return next(empty_generator())
        if kind == 8:
            left = []
            right = []
            left.append(left)
            right.append(right)
            return left == right
        if kind == 9:
            return 1 // 0
        if kind == 10:
            return 0 ** -1
        if kind == 11:
            raise Signal
        return 17
    except BaseException:
        return kind + 100


def arithmetic_quotient(left, right):
    try:
        return left // right
    except ArithmeticError:
        return 0


def base_runtime():
    mapping = {1: 7}
    cursor = iter(mapping)
    mapping[2] = 8
    try:
        return next(cursor)
    except BaseException:
        return len(mapping)


def system_exit_loud():
    try:
        raise SystemExit
    except BaseException:
        return 31


def keyboard_interrupt_loud():
    try:
        raise KeyboardInterrupt
    except BaseException:
        return 32


def generator_exit_loud():
    try:
        raise GeneratorExit
    except BaseException:
        return 33


def arithmetic_power():
    try:
        return 0 ** -1
    except ArithmeticError:
        return 21


def arithmetic_type_nonmatch():
    try:
        return len(0)
    except ArithmeticError:
        return 22


def arithmetic_user_nonmatch():
    try:
        raise Signal
    except ArithmeticError:
        return 23


def lookup_index(index):
    try:
        return (7, 8)[index]
    except LookupError:
        return -1


def lookup_key(key):
    mapping = {1: 10}
    try:
        return mapping[key]
    except LookupError:
        return -1


def lookup_arithmetic_nonmatch():
    try:
        return 1 // 0
    except LookupError:
        return 24


def lookup_type_nonmatch():
    try:
        return len(0)
    except LookupError:
        return 25


def lookup_user_nonmatch():
    try:
        raise Signal
    except LookupError:
        return 26


def arithmetic_mutation():
    values = [0]
    try:
        values.append(1)
        divmod(7, 0)
        values.append(2)
    except ArithmeticError:
        values.append(3)
    return values


def lookup_mutation():
    values = [0]
    mapping = {1: 7}
    try:
        values.append(1)
        mapping[2]
        values.append(2)
    except LookupError:
        values.append(3)
    return values


def nested_fallthrough():
    values = [0]
    try:
        try:
            values.append(1)
            len(0)
        except LookupError:
            values.append(2)
    except BaseException:
        values.append(3)
    return values


def handler_raises():
    try:
        return 1 // 0
    except ArithmeticError:
        return ()[0]


def nested_handler_raises():
    values = [0]
    try:
        try:
            values.append(1)
            1 // 0
        except ArithmeticError:
            values.append(2)
            len(0)
    except BaseException:
        values.append(3)
    return values


def parameter_shadow(BaseException):
    try:
        return len(0)
    except BaseException:
        return 27


def body_shadow():
    try:
        ArithmeticError = 1
        return 1 // 0
    except ArithmeticError:
        return 28


def body_shadow_nonmatch():
    try:
        LookupError = 1
        return 1 // 0
    except LookupError:
        return 29


def late_shadow():
    try:
        return ()[0]
    except LookupError:
        return 30
    LookupError = 1


def os_ancestor():
    try:
        return 1 // 0
    except OSError:
        return 31


def environment_ancestor():
    try:
        return 1 // 0
    except EnvironmentError:
        return 32


def first_class_base():
    return BaseException


def raise_base_instance():
    try:
        raise BaseException()
    except BaseException:
        return 34


def raise_arithmetic_class():
    raise ArithmeticError


def loud_body():
    try:
        return float(1)
    except BaseException:
        return 33
