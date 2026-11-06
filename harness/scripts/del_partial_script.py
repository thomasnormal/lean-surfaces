# the PARTIAL left-to-right effect at module scope: f and x really go before
# `nosuch` raises under CPython. The model reaches the loud static-definition
# deletion boundary before it can observe the later NameError.
def f():
    return 3


x = 1
print(f())
del f, x, nosuch
