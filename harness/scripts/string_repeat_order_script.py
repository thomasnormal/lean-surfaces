def left_text():
    print("left text")
    return "ab"


def right_count():
    print("right count")
    return 2


def left_count():
    print("left count")
    return 3


def right_text():
    print("right text")
    return "xy"


def bad_count():
    print("bad count")
    return None


def augmented():
    text = left_text()
    text *= right_count()
    return text


print(left_text() * right_count())
print(left_count() * right_text())
print(augmented())
try:
    print(left_text() * bad_count())
except TypeError:
    print("caught right count")
try:
    print(bad_count() * right_text())
except TypeError:
    print("caught left count")
