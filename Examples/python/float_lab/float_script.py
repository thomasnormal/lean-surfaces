def quotient(left, right):
    return left / right


value = quotient(1, 10)
print(value, repr(-0.0), [value, 5e-324, 1e999])
print(f"{value!r}", "%d" % 1.5)
print(9007199254740992.0 < 9007199254740993)
for mode in range(3):
    try:
        if mode == 0:
            quotient(1, 0)
        elif mode == 1:
            quotient(1.0, 0.0)
        else:
            quotient(10 ** 400, 0.0)
    except ArithmeticError:
        print("caught", mode)
