def gen_ascii(a):
    yield a


def gen_unicode(é):
    yield é


def ascii_keyword(n):
    if n:
        return ascii_keyword(n - 1)
    gen_ascii(a=7)
    return 7


def unicode_keyword(n):
    if n:
        return unicode_keyword(n - 1)
    gen_unicode(é=7)
    return 7
