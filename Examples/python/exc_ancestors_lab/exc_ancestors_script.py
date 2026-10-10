values = [0]

try:
    from zzz_no_such_ancestor_module import missing
except BaseException:
    values.append(1)

try:
    try:
        from zzz_no_such_ancestor_module import missing
    except ArithmeticError:
        values.append(9)
except BaseException:
    values.append(2)

try:
    try:
        from zzz_no_such_ancestor_module import missing
    except LookupError:
        values.append(9)
except BaseException:
    values.append(3)

mapping = {1: 7}
try:
    for key, value in mapping.items():
        mapping[2] = 8
except BaseException:
    values.append(4)

print(values)
