"""Non-simple annotated assignments follow CPython's evaluation order."""


def tag(label):
    print(label)
    return None


d = {}
d["module"]: tag("ann") = tag("val")


def run():
    d["function"]: tag("ann") = tag("val")


run()
print(1)
