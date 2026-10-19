def g():
    yield 1
    raise StopIteration
print(list(g()))
