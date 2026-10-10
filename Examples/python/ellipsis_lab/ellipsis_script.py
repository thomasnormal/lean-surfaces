print(..., Ellipsis, ... is Ellipsis)
print(str(...), repr(...), f"{...!r}", "%s" % (...,))
print(bool(...), not ..., ... == ..., ... != None)
table = {...: 1}
table[Ellipsis] = 2
print(table, table[...], len(table), ... in table)
print([..., (...,), {(...,): ...}])


def singleton(value=...):
    return value is ...


print(singleton(), singleton(Ellipsis), singleton(3))
Ellipsis = 7
print(Ellipsis, ... is Ellipsis, str(...))
del Ellipsis
print(Ellipsis, singleton(Ellipsis))
try:
    for value in ...:
        print(value)
except TypeError:
    print("ellipsis is not iterable")
print(sum((), ...))
