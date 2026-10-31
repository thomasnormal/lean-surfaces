"""Bare builtin exception classes, hierarchy, retained effects and PEP 479."""


def raise_BaseException():
    raise BaseException


def catch_BaseException(value):
    try:
        raise BaseException
    except BaseException:
        return value


def raise_Exception():
    raise Exception


def catch_Exception(value):
    try:
        raise Exception
    except Exception:
        return value


def raise_ArithmeticError():
    raise ArithmeticError


def catch_ArithmeticError(value):
    try:
        raise ArithmeticError
    except Exception:
        return value


def raise_LookupError():
    raise LookupError


def catch_LookupError(value):
    try:
        raise LookupError
    except Exception:
        return value


def raise_TypeError():
    raise TypeError


def catch_TypeError(value):
    try:
        raise TypeError
    except Exception:
        return value


def raise_NameError():
    raise NameError


def catch_NameError(value):
    try:
        raise NameError
    except Exception:
        return value


def raise_ZeroDivisionError():
    raise ZeroDivisionError


def catch_ZeroDivisionError(value):
    try:
        raise ZeroDivisionError
    except ArithmeticError:
        return value


def raise_OverflowError():
    raise OverflowError


def catch_OverflowError(value):
    try:
        raise OverflowError
    except ArithmeticError:
        return value


def raise_IndexError():
    raise IndexError


def catch_IndexError(value):
    try:
        raise IndexError
    except LookupError:
        return value


def raise_ValueError():
    raise ValueError


def catch_ValueError(value):
    try:
        raise ValueError
    except Exception:
        return value


def raise_KeyError():
    raise KeyError


def catch_KeyError(value):
    try:
        raise KeyError
    except LookupError:
        return value


def raise_RuntimeError():
    raise RuntimeError


def catch_RuntimeError(value):
    try:
        raise RuntimeError
    except Exception:
        return value


def raise_RecursionError():
    raise RecursionError


def catch_RecursionError(value):
    try:
        raise RecursionError
    except RuntimeError:
        return value


def raise_AttributeError():
    raise AttributeError


def catch_AttributeError(value):
    try:
        raise AttributeError
    except Exception:
        return value


def raise_AssertionError():
    raise AssertionError


def catch_AssertionError(value):
    try:
        raise AssertionError
    except Exception:
        return value


def raise_StopIteration():
    raise StopIteration


def catch_StopIteration(value):
    try:
        raise StopIteration
    except Exception:
        return value


def raise_ImportError():
    raise ImportError


def catch_ImportError(value):
    try:
        raise ImportError
    except Exception:
        return value


def raise_ModuleNotFoundError():
    raise ModuleNotFoundError


def catch_ModuleNotFoundError(value):
    try:
        raise ModuleNotFoundError
    except Exception:
        return value


def raise_EnvironmentError():
    raise EnvironmentError


def catch_EnvironmentError(value):
    try:
        raise OSError
    except EnvironmentError:
        return value


def raise_IOError():
    raise IOError


def catch_IOError(value):
    try:
        raise OSError
    except IOError:
        return value


def raise_StopAsyncIteration():
    raise StopAsyncIteration


def catch_StopAsyncIteration(value):
    try:
        raise StopAsyncIteration
    except Exception:
        return value


def raise_Warning():
    raise Warning


def catch_Warning(value):
    try:
        raise Warning
    except Exception:
        return value


def raise_UnicodeError():
    raise UnicodeError


def catch_UnicodeError(value):
    try:
        raise UnicodeError
    except Exception:
        return value


def raise_UnicodeWarning():
    raise UnicodeWarning


def catch_UnicodeWarning(value):
    try:
        raise UnicodeWarning
    except Warning:
        return value


def raise_UserWarning():
    raise UserWarning


def catch_UserWarning(value):
    try:
        raise UserWarning
    except Warning:
        return value


def base_not_exception():
    try:
        try:
            raise BaseException
        except Exception:
            return 1
    except BaseException:
        return 2


def wrong_sibling():
    try:
        try:
            raise ValueError
        except TypeError:
            return 1
    except ValueError:
        return 2


def retained_state():
    data = [0]
    try:
        data.append(1)
        raise KeyError
    except LookupError:
        data.append(2)
    return data


def through_call():
    try:
        raise_OverflowError()
    except ArithmeticError:
        return 9


def stop_generator():
    yield 1
    raise StopIteration


def empty_generator():
    if False:
        yield 0


def next_stop_generator():
    yield 1
    next(empty_generator())


def generator_closed():
    g = stop_generator()
    first = next(g)
    try:
        next(g)
    except RuntimeError:
        return first * 10 + next(g, 7)


def generator_escape():
    return list(stop_generator())


def exhaustion_escape():
    return list(next_stop_generator())


def catches_stop():
    try:
        raise StopIteration
    except StopIteration:
        value = 5
    yield value


def caught_inside_generator():
    return next(catches_stop())


def parameter_shadow(ValueError):
    raise ValueError


def late_shadow():
    raise ValueError
    ValueError = 1


def raised_instance():
    # A zero-argument constructor has the same observable class identity as
    # the admitted bare raise; payload-bearing constructors remain loud.
    raise ValueError()


def chained():
    raise ValueError from None


def unsupported_class():
    # OSError has an empty class identity just like the already admitted
    # builtin raises; OS-derived and payload-bearing constructors stay loud.
    raise OSError
