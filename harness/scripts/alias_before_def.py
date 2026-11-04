"""Alias BEFORE the def: CPython and leanpy raise NameError at the alias
line.  The ingestion pass cannot admit a target definition that ends later,
so this remains an ordinary assignment and the script executor reports the
runtime error at its source position."""

early = late_def


def late_def(x):
    return x


print(early(1))
