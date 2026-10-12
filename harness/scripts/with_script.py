"""leanpy corpus: module-scope synchronous context-manager publication."""


class Marker:
    def __enter__(self):
        return 40

    def __exit__(self, exc_type, exc, tb):
        return None


def read_value():
    return value


with Marker() as value:
    print(read_value())

with Marker():
    value = 41
    print(read_value())

print(value)
