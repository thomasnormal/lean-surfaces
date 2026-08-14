# NON-trailing del of a def name: a static table entry no runtime arm
# can remove -- refused LOUDLY (CPython prints 1 and exits 0).
def f():
    return 3


del f
print(1)
