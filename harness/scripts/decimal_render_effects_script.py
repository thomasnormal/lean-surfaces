def observed(label, value):
    print(label)
    return value


def fail(label):
    print(label)
    return 1 // 0


print(str(observed("scalar argument", -27)))
print("%d %s" % (observed("first format argument", 7), observed("second format argument", -27)))
print(str({observed("dict key", -27): observed("dict value", 7)}))
print(str(range(observed("range start", 1), observed("range stop", 5), observed("range step", 2))))

try:
    str(fail("scalar argument fails"))
except ZeroDivisionError:
    print("caught scalar argument")

try:
    "%d %d" % (fail("first format argument fails"), observed("suppressed second argument", 2))
except ZeroDivisionError:
    print("caught first format argument")

try:
    "%d %d" % (observed("first format argument survives", 7), fail("second format argument fails"))
except ZeroDivisionError:
    print("caught second format argument")

try:
    "%d %d" % (observed("bad first conversion", "x"), observed("evaluated second argument", 7))
except TypeError:
    print("caught first conversion")
