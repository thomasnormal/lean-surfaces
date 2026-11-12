"""The closed-function tier does not model the runner's live __main__ module."""
def probe():
    from __main__ import __name__
    return __name__
