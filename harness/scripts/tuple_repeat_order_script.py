def left_tuple():
    print("left tuple")
    return (7, 8)


def right_count():
    print("right count")
    return 2


def left_count():
    print("left count")
    return 3


def right_tuple():
    print("right tuple")
    return (1, 2)


def bad_count():
    print("bad count")
    return None


def empty_tuple():
    print("empty tuple")
    return ()


def oversized_count():
    print("oversized count")
    return 1267650600228229401496703205376


def augmented():
    values = left_tuple()
    values *= right_count()
    return values


print(left_tuple() * right_count())
print(left_count() * right_tuple())
print(augmented())
try:
    print(left_tuple() * bad_count())
except TypeError:
    print("caught right count")
try:
    print(bad_count() * right_tuple())
except TypeError:
    print("caught left count")
print(empty_tuple() * oversized_count())
