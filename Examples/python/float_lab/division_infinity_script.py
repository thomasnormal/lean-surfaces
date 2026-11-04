def read():
    return value


def left():
    print("left")
    return float("inf")


def right():
    print("right")
    return -0.0


value = -0.0
value /= float("-inf")
print(read())
print(float("inf") / -2.0, float("-inf") / -5e-324)
print(1e308 / float("-inf"), -5e-324 / float("inf"))
print(True / float("-inf"), float("inf") / True)
try:
    left() / right()
except ZeroDivisionError:
    print("zero denominator")
try:
    10 ** 400 / float("inf")
except OverflowError:
    print("conversion overflow")
