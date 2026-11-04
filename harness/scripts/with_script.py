"""leanpy corpus: module-scope synchronous context-manager publication."""


class Marker:
    def __enter__(self):
        return 40

    def __exit__(self, exc_type, exc, tb):
        return None


class InitMarker:
    def __init__(self):
        pass

    def __enter__(self):
        return 7

    def __exit__(self, exc_type, exc, tb):
        return None


def read_value():
    return value


with Marker() as value:
    print(read_value())

with Marker():
    value = 41
    print(read_value())

with InitMarker() as initialized:
    print(initialized)

with Marker() as first, InitMarker() as second:
    print(first + second)

print(value)
