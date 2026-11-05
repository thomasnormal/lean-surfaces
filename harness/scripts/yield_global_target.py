"""Expression-yield stores under global declarations remain loud."""


value = 0


def producer():
    global value
    value = yield 5


g = producer()
next(g)
next(g, None)
print(value)
