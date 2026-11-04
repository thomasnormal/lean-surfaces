def values():
    print("advanced")
    yield 7


def iterable():
    print("iterable")
    return 1


def initial():
    print("start")
    return ""


for start in ("", b""):
    cursor = values()
    try:
        sum(cursor, start)
    except TypeError:
        print("rejected")
    print(next(cursor))

sum(iterable(), initial())
