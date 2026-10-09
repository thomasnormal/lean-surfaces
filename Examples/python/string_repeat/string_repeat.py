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
