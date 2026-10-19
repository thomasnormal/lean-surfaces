class StopIteration(Exception):
    pass


def g():
    yield 1
    raise StopIteration


try:
    try:
        print(list(g()))
    except RuntimeError:
        print("wrong runtime")
except StopIteration:
    print("user exception")
