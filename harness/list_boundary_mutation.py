"""Boundary list mutation probe for the heap-threaded argument path."""
def left(values):
    values.insert(1, 2)
    return values
