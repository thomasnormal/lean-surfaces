class UserError(Exception):
    pass


def bare(n):
    def leaf():
        raise ValueError
    try:
        if n:
            return bare(n - 1)
        return leaf()
    except ValueError:
        return 42


def explicit(n):
    def leaf():
        raise ValueError()
    try:
        if n:
            return explicit(n - 1)
        return leaf()
    except ValueError:
        return 42


def message(n):
    def leaf():
        raise ValueError('bad')
    try:
        if n:
            return message(n - 1)
        return leaf()
    except ValueError:
        return 42


def user_bare(n):
    def leaf():
        raise UserError
    try:
        if n:
            return user_bare(n - 1)
        return leaf()
    except UserError:
        return 42


def user_explicit(n):
    def leaf():
        raise UserError('bad')
    try:
        if n:
            return user_explicit(n - 1)
        return leaf()
    except UserError:
        return 42


def assertion(n):
    def leaf():
        assert False
    try:
        if n:
            return assertion(n - 1)
        return leaf()
    except AssertionError:
        return 42


def assertion_message(n):
    def leaf():
        assert False, 'bad'
    try:
        if n:
            return assertion_message(n - 1)
        return leaf()
    except AssertionError:
        return 42


def raise_argument_first(n):
    def leaf():
        try:
            raise ValueError(missing_name)
        except NameError:
            return 23
    if n:
        return raise_argument_first(n - 1)
    return leaf()


def assert_argument_first(n):
    def leaf():
        try:
            assert False, missing_name
        except NameError:
            return 23
    if n:
        return assert_argument_first(n - 1)
    return leaf()


def catch_recursion_and_retry(n):
    def leaf():
        try:
            try:
                raise ValueError
            except RecursionError:
                return 31
        except ValueError:
            return 32
    def identity(value):
        return value
    if n:
        return catch_recursion_and_retry(n - 1)
    result = leaf()
    return identity(result)


def raise_argument_effect(n):
    def leaf():
        value = 'before'
        try:
            try:
                raise ValueError((value := 'after'))
            except RecursionError:
                return value
        except ValueError:
            return value
    if n:
        return raise_argument_effect(n - 1)
    return leaf()


def assert_argument_effect(n):
    def leaf():
        value = 'before'
        try:
            try:
                assert False, (value := 'after')
            except RecursionError:
                return value
        except AssertionError:
            return value
    if n:
        return assert_argument_effect(n - 1)
    return leaf()
