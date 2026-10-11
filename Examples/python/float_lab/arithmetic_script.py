def read():
    return value


value = 0.5
value += 0.25
print(read())
value -= 0.125
value *= -2.0
print(read())
print(0.1 + 0.2, -0.0 + -0.0, -0.0 - 0.0, 0.0 * -2.0)
print(1e308 + 1e308, 1e308 * -2.0, 1e999 - 2.0)
