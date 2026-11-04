class BaseException(Exception):
    pass


class ArithmeticError(Exception):
    pass


class LookupError(Exception):
    pass


def base_user():
    try:
        raise BaseException
    except BaseException:
        return 41


def base_builtin():
    try:
        return len(0)
    except BaseException:
        return 42


def arithmetic_user():
    try:
        raise ArithmeticError
    except ArithmeticError:
        return 43


def arithmetic_builtin():
    try:
        return 1 // 0
    except ArithmeticError:
        return 44


def lookup_user():
    try:
        raise LookupError
    except LookupError:
        return 45


def lookup_builtin():
    try:
        return ()[0]
    except LookupError:
        return 46
