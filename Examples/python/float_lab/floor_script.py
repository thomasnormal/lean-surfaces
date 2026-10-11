def read():
    return value


value = 1.0
value //= 0.1
print(read())
value %= 4.0
print(read())
print(divmod(1.0, 0.1), divmod(-1.0, 0.1))
print(divmod(5.0, float("-inf")), divmod(-0.0, float("-inf")))
print([divmod(1.0, divisor) for divisor in (0.1, 0.3)])
for mode in (0, 1, 2):
    try:
        if mode == 0:
            1.0 // 0.0
        elif mode == 1:
            1.0 % 0.0
        else:
            divmod(1.0, 0.0)
    except ArithmeticError:
        print("zero", mode)
