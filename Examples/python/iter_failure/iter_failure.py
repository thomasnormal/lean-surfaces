def native_failure_with_default():
    mapping = {"a": 1}
    cursor = iter(mapping)
    next(cursor)
    mapping["b"] = 2
    try:
        next(cursor)
    except RuntimeError:
        pass
    return next(cursor, 99)


def native_failure_without_default():
    mapping = {"a": 1}
    cursor = iter(mapping)
    next(cursor)
    mapping["b"] = 2
    try:
        next(cursor, 99)
    except RuntimeError:
        pass
    return next(cursor)

def native_restored_failure():
    mapping = {"a": 1}
    cursor = iter(mapping)
    next(cursor)
    mapping["b"] = 2
    failures = 0
    try:
        next(cursor)
    except RuntimeError:
        failures += 1
    mapping.clear()
    mapping["a"] = 1
    for attempt in range(3):
        try:
            next(cursor, 99)
        except RuntimeError:
            failures += 1
    return failures


def native_alias_failure():
    mapping = {"a": 1}
    cursor = iter(mapping)
    alias = cursor
    next(cursor)
    mapping["b"] = 2
    failures = 0
    try:
        next(cursor)
    except RuntimeError:
        failures += 1
    mapping.clear()
    mapping["a"] = 1
    try:
        next(alias, 99)
    except RuntimeError:
        failures += 1
    return failures


def native_fresh_cursor():
    mapping = {"a": 1}
    cursor = iter(mapping)
    next(cursor)
    mapping["b"] = 2
    try:
        next(cursor)
    except RuntimeError:
        pass
    mapping.clear()
    mapping["a"] = 1
    fresh = iter(mapping)
    return next(fresh), next(fresh, 99)


def native_failure_before_first():
    mapping = {"a": 1}
    cursor = iter(mapping)
    mapping["b"] = 2
    failures = 0
    try:
        next(cursor)
    except RuntimeError:
        failures += 1
    mapping.clear()
    mapping["a"] = 1
    try:
        next(cursor, 99)
    except RuntimeError:
        failures += 1
    return failures


def enumerate_restored_failure():
    mapping = {"a": 1}
    cursor = enumerate(mapping)
    next(cursor)
    mapping["b"] = 2
    failures = 0
    try:
        next(cursor)
    except RuntimeError:
        failures += 1
    mapping.clear()
    mapping["a"] = 1
    for attempt in range(3):
        try:
            next(cursor, 99)
        except RuntimeError:
            failures += 1
    return failures


def enumerate_alias_failure():
    mapping = {"a": 1}
    cursor = enumerate(mapping, 7)
    alias = cursor
    next(cursor)
    mapping["b"] = 2
    failures = 0
    try:
        next(cursor)
    except RuntimeError:
        failures += 1
    mapping.clear()
    mapping["a"] = 1
    try:
        next(alias, 99)
    except RuntimeError:
        failures += 1
    return failures


def dict_stream(mapping):
    for key in mapping:
        yield key


def generator_closed_default():
    mapping = {"a": 1}
    cursor = dict_stream(mapping)
    next(cursor)
    mapping["b"] = 2
    try:
        next(cursor)
    except RuntimeError:
        pass
    mapping.clear()
    mapping["a"] = 1
    return next(cursor, 99), next(cursor, 99)


def generator_closed_without_default():
    mapping = {"a": 1}
    cursor = dict_stream(mapping)
    next(cursor)
    mapping["b"] = 2
    try:
        next(cursor)
    except RuntimeError:
        pass
    return next(cursor)
