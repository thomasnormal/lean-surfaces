"""Rows for the distinct Python-frame and nested C-call recursion units."""

def frame_then_int(n):
    try:
        if n:
            return frame_then_int(n - 1)
        return int("1")
    except RecursionError:
        return 11


def frame_then_str(n):
    try:
        if n:
            return frame_then_str(n - 1)
        return str(1)
    except RecursionError:
        return 11
