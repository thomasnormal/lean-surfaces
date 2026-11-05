"""Rebinding forms omitted by the old generator capture census stay loud."""


def unpack_case():
    p = 3
    g = (p for _ in (1,))
    p, *rest = (9, 8)
    return list(g)


def delete_case():
    p = 3
    g = (p for _ in (1,))
    del p
    return list(g)


print(unpack_case(), delete_case())
