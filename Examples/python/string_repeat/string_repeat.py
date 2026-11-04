def repeat_right(text, count):
    return text * count


def repeat_left(count, text):
    return count * text


def repeat_aug(text, count):
    text *= count
    return text


def decorated(text, count):
    return "[" + text * count + "]"


def width_offset(offset):
    return len("ab" * 3) + offset


def repeat_live_list(count):
    return [1, 2] * count


def repeat_aug_live_list(count):
    xs = [1, 2]
    ys = xs
    xs *= count
    return (xs is ys, ys)


def repeat_boundary_list(values, count):
    # A boundary list is an immutable snapshot inside the isolated value
    # surface; multiplication returns a fresh list without exposing heap
    # aliasing to the caller.
    return values * count


def repeat_boundary_list_length(values, count):
    return len(values * count)


def repeat_right_length(text, count):
    result = text * count
    return len(result)


def repeat_left_length(count, text):
    result = count * text
    return len(result)


def repeat_aug_length(text, count):
    text *= count
    return len(text)
