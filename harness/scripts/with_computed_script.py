"""leanpy corpus: a computed truthy __exit__ result suppresses an error."""


class ComputedSuppressingExit:
    def __enter__(self):
        return 1

    def __exit__(self, exc_type, exc, tb):
        return not False


with ComputedSuppressingExit():
    1 // 0

print(43)
