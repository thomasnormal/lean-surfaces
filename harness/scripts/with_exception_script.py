"""leanpy corpus: synchronous with calls __exit__ before re-raising."""


class Marker:
    def __enter__(self):
        return 40

    def __exit__(self, exc_type, exc, tb):
        return False


with Marker():
    1 // 0
