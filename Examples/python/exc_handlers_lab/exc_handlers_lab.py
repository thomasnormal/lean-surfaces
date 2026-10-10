class Signal(Exception):
    pass


class Box:
    pass


def caught_type_identity(value):
    try:
        len(0)
        return 0
    except TypeError:
        return value


def loud_body():
    try:
        return float(1)
    except Exception:
        return 99


def quotient_or_zero(left, right):
    try:
        return left // right
    except ZeroDivisionError:
        return 0


def power_zero():
    try:
        return 0 ** -1
    except ZeroDivisionError:
        return 2


def value_error(text):
    try:
        return int(text)
    except ValueError:
        return -1


def index_error(index):
    try:
        return (7, 8)[index]
    except IndexError:
        return -1


def key_error(key):
    mapping = {1: 10}
    try:
        return mapping[key]
    except KeyError:
        return -1


def name_error():
    try:
        return missing_handler_value
    except NameError:
        return 3


def attribute_error():
    value = Box()
    try:
        return value.missing
    except AttributeError:
        return 4


def assertion_error(value):
    try:
        assert value
        return 5
    except AssertionError:
        return -5


def empty_generator():
    if False:
        yield 1


def stop_iteration():
    cursor = empty_generator()
    try:
        return next(cursor)
    except StopIteration:
        return 6


def runtime_catches_recursion():
    left = []
    right = []
    left.append(left)
    right.append(right)
    try:
        return left == right
    except RuntimeError:
        return 7


def recursion_exact():
    left = []
    right = []
    left.append(left)
    right.append(right)
    try:
        return left == right
    except RecursionError:
        return 8


def exception_user():
    try:
        raise Signal
    except Exception:
        return 9


def exception_builtin():
    try:
        return 1 // 0
    except Exception:
        return 10


def nonmatching_builtin():
    try:
        return 1 // 0
    except TypeError:
        return -1


def nonmatching_user():
    try:
        raise Signal
    except TypeError:
        return -1


def nested_nonmatching():
    values = []
    try:
        try:
            values.append(1)
            return 1 // 0
        except TypeError:
            values.append(2)
    except ZeroDivisionError:
        values.append(3)
    return values


def type_mutation():
    values = [7]
    try:
        divmod(values.append(8), values.append(9), values.append(10))
    except TypeError:
        values.append(11)
    return values


def subscript_mutation():
    values = [0]
    try:
        values.append(1)
        values[8] = 2
    except IndexError:
        values.append(3)
    return values


def handler_raises():
    try:
        return len(0)
    except TypeError:
        return 1 // 0


def nested_handler_raises():
    try:
        try:
            return len(0)
        except TypeError:
            return 1 // 0
    except ZeroDivisionError:
        return 12


def handler_binding():
    try:
        return 1 // 0
    except ZeroDivisionError as error:
        return error


def tuple_handler():
    try:
        return 1 // 0
    except (TypeError, ZeroDivisionError):
        return 13


def shadowed_handler(TypeError):
    try:
        return len(0)
    except TypeError:
        return 14


def local_shadowed_handler():
    TypeError = 5
    try:
        return 1
    except TypeError:
        return 15


def body_shadowed_handler():
    try:
        TypeError = 5
        return len(0)
    except TypeError:
        return 15


def body_shadowed_nonmatching():
    try:
        TypeError = 5
        return 1 // 0
    except TypeError:
        return 15


def late_shadowed_handler():
    try:
        return len(0)
    except TypeError:
        return 15
    TypeError = 5


def nested_def_handler():
    def TypeError():
        return 5
    try:
        return len(0)
    except TypeError:
        return 15


def base_exception():
    try:
        return 1 // 0
    except BaseException:
        return 16


def arithmetic_ancestor():
    try:
        return 1 // 0
    except ArithmeticError:
        return 17


def lookup_ancestor():
    try:
        return ()[0]
    except LookupError:
        return 18


def else_clause():
    try:
        value = 1
    except TypeError:
        return 0
    else:
        return value


def finally_clause():
    values = []
    try:
        return values
    except TypeError:
        return []
    finally:
        values.append(19)


def multiple_handlers():
    try:
        return 1 // 0
    except TypeError:
        return 20
    except ZeroDivisionError:
        return 21


def bare_handler():
    try:
        return 1 // 0
    except:
        return 22


def exception_value():
    return TypeError
