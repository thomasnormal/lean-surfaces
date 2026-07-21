"""Modular inverse from python-rsa, vendored verbatim for Lean verification.

Provenance:
  package : rsa (python-rsa), https://pypi.org/project/rsa/
  version : 4.9.1 (pip download --no-deps rsa, 2026-07-21; wheel
            rsa-4.9.1-py3-none-any.whl, sha256
            68635866661c6836b8d39430f97a996acbd61bfa49406748ea243539fe239762)
  file    : rsa/common.py, sha256
            c3452e5791cdbe4142e2c04c8cc0cef094d4242a17bec2f372826b02eab32e90
  license : Apache-2.0. The functions below are Copyright 2011 Sybren
            A. Stuvel <sybren@stuvel.eu>, licensed under the Apache License,
            Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Vendoring rules (real-world demo, Examples/rsa_inverse):
  * extended_gcd and inverse are BYTE-VERBATIM copies of rsa/common.py
    4.9.1 lines 105-126 and 129-143 (sha256 of the two segments:
    f7efc7b4b654d11c93bc7b1e01ba8a641bfe22f85cd356c1ddc20904cbc66027 and
    16048fb54fbfcdf0005bd250b0cc09994458e8ed048b39f83bbd5df9fb75d907).
    Do NOT edit their bodies.
  * "import typing" is retained from the original module: the eagerly
    evaluated return annotation of extended_gcd needs the name at def time.
  * NotRelativePrimeError (a ValueError subclass in rsa/common.py) is NOT
    vendored: it occurs only inside the raise statement of inverse -- the
    single out-of-tier node, covered by the proof's unreachability argument
    for coprime inputs; no in-tier run evaluates the name.

Authenticity (2026-07-21, Python 3.9.25): inverse(3, 7) = 5,
inverse(7, 40) = 23, extended_gcd(12, 18) = (6, 17, 1) computed against
this file AND against the installed rsa==4.9.1 package -- both agree.
"""

import typing


def extended_gcd(a: int, b: int) -> typing.Tuple[int, int, int]:
    """Returns a tuple (r, i, j) such that r = gcd(a, b) = ia + jb"""
    # r = gcd(a,b) i = multiplicitive inverse of a mod b
    #      or      j = multiplicitive inverse of b mod a
    # Neg return values for i or j are made positive mod b or a respectively
    # Iterateive Version is faster and uses much less stack space
    x = 0
    y = 1
    lx = 1
    ly = 0
    oa = a  # Remember original a/b to remove
    ob = b  # negative values from return results
    while b != 0:
        q = a // b
        (a, b) = (b, a % b)
        (x, lx) = ((lx - (q * x)), x)
        (y, ly) = ((ly - (q * y)), y)
    if lx < 0:
        lx += ob  # If neg wrap modulo original b
    if ly < 0:
        ly += oa  # If neg wrap modulo original a
    return a, lx, ly  # Return only positive values


def inverse(x: int, n: int) -> int:
    """Returns the inverse of x % n under multiplication, a.k.a x^-1 (mod n)

    >>> inverse(7, 4)
    3
    >>> (inverse(143, 4) * 143) % 4
    1
    """

    (divider, inv, _) = extended_gcd(x, n)

    if divider != 1:
        raise NotRelativePrimeError(x, n, divider)

    return inv
