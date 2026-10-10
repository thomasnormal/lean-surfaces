print(repr("quoted"))
print(repr([1, "x", None]))
values = []
values.append(values)
print(repr(values))


def effect(value):
    print(value)
    return value


try:
    repr(effect("first"), effect("second"))
except TypeError:
    print("arity after arguments")

try:
    repr(effect("before error"), 1 // 0)
except ZeroDivisionError:
    print("argument error before arity")
