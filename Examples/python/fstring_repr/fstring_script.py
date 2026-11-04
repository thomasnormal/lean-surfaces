str = 7
repr = 8
print(f"{'x'!r}/{None!s}/{True}")
print(f"{str=}/{repr=}")


def shadowed_builtin_call():
    return str(3)


try:
    shadowed_builtin_call()
except TypeError:
    print("shadowed str call")


values = []
print(f"{values.append(1)!r}:{values!r}:{values.append(2)!r}:{values!r}")
values.append(values)
print(f"{values!r}")


def effect(value):
    print(value)
    return value


try:
    print(f"{effect('first')!r}:{1 // 0!r}:{effect('never')!r}")
except ZeroDivisionError:
    print("field error before later field")

print(f"{'quoted'!r:}")
