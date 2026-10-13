"""leanpy corpus: a literal True __exit__ suppresses a body exception."""


class SuppressingExit:
    def __enter__(self):
        return 1

    def __exit__(self, exc_type, exc, tb):
        return True


with SuppressingExit():
    1 // 0

print(42)
