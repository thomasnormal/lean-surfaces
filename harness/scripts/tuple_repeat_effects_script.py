def observed(label, value):
    print(label)
    return value


def fail(label):
    print(label)
    return 1 // 0


print(observed("left tuple", (7, 8)) * observed("right count", 2))
print(observed("left count", 2) * observed("right tuple", (7, 8)))
values = (7, 8)
values *= observed("augmented count", 2)
print(values)

try:
    fail("first operand fails") * observed("suppressed operand", 2)
except ZeroDivisionError:
    print("caught first operand")

try:
    observed("first operand", (7, 8)) * fail("second operand fails")
except ZeroDivisionError:
    print("caught second operand")
