"""Single-item synchronous context-manager acceptance battery."""


class Marker:
    def __enter__(self):
        return 40

    def __exit__(self, exc_type, exc, tb):
        return None


def bound_value():
    with Marker() as value:
        return value + 2


def unbound_value():
    with Marker():
        return 7


def fallthrough():
    value = 1
    with Marker() as entered:
        value = entered
    return value


def multiple_items():
    with Marker(), Marker():
        return 0


class ExplicitInit:
    def __init__(self):
        pass

    def __enter__(self):
        return 1

    def __exit__(self, exc_type, exc, tb):
        return None


def explicit_init():
    with ExplicitInit():
        return 0


def body_exception():
    with Marker():
        1 // 0


def body_exception_target():
    with Marker() as value:
        1 // 0


class SuppressingExit:
    def __enter__(self):
        return 1

    def __exit__(self, exc_type, exc, tb):
        return True


def suppressed_exception():
    with SuppressingExit():
        1 // 0
    return 7


class ExtraDunder:
    def __enter__(self):
        return 1

    def __exit__(self, exc_type, exc, tb):
        return None

    def __repr__(self):
        return "ExtraDunder()"


def extra_dunder():
    with ExtraDunder():
        return 0
