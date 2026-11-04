def arg(value):
    print(value)
    return value


def fail(value):
    print(value)
    return value // 0


def shadow(value):
    def divmod(left, right):
        return left + right
    return divmod(value, 2)


print(divmod(7, 3), divmod(-7, 3), divmod(7, -3), divmod(-7, -3))
print(divmod(6, 3), divmod(-6, 3), divmod(6, -3), divmod(-6, -3))
print(divmod(False, True), divmod(True, True), divmod(7, True))
print(divmod(True, -3), divmod(2 ** 100, 1))
print(tuple(divmod(value, 3) for value in range(-4, 5)))
print(shadow(3))
try:
    divmod()
except TypeError:
    print("arity zero")
try:
    divmod(arg(7))
except TypeError:
    print("arity one")
try:
    divmod(arg(7), arg(3), arg(2))
except TypeError:
    print("arity three")
try:
    divmod(arg(7), fail(3), arg(2))
except ZeroDivisionError:
    print("argument before arity")
try:
    divmod(fail(7))
except ZeroDivisionError:
    print("argument before missing operand")
try:
    divmod(arg(7), arg(0))
except ZeroDivisionError:
    print("zero divisor")
try:
    divmod(True, False)
except ZeroDivisionError:
    print("Boolean zero divisor")
