# the PARTIAL left-to-right effect at module scope: f (a def name, in
# trailing position -- dropped at ingestion) and x really go before
# `nosuch` raises; stdout up to the raise is compared byte-for-byte.
def f():
    return 3


x = 1
print(f())
del f, x, nosuch
