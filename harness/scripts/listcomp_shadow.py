"""A list comprehension does not look up a user binding named list."""


def list(value):
    return "shadow"


def local_shadow():
    list = 3
    return [y for y in (1, 2)]


print(local_shadow())
