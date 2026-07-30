"""Luhn check digits (PyPI package `luhn`), vendored verbatim for the Lean
verification benchmark (Band C marker: negative-step slices + map/sum).

Provenance:
  package : luhn, https://pypi.org/project/luhn/
            (https://github.com/mmcloughlin/luhn)
  version : 0.2.0 (pip download --no-deps luhn, 2026-07-21; sdist
            luhn-0.2.0.tar.gz, sha256
            917174cecce8bcbbe56ac0d904dbedd06594b21b6f31d5a3ec161d455b0e59f7)
  file    : luhn.py, sha256
            c6e9aadd736116ff52b7e59c0f8e8d753278a85eafcd1ca2b423b2939498ad36
  license : MIT; Copyright (c) 2014 Michael McLoughlin.

Vendoring rules (python benchmark, Examples/python/bench_luhn):
  * checksum, verify, generate and append are BYTE-VERBATIM copies of
    luhn.py 0.2.0 lines 3-11, 13-22, 24-34 and 36-43 (sha256 of the four
    segments:
    b1cfc3a0df8bcdb570f6c4aa719b4f155039f79b41f2fbbd702b7acef64218ec
    170554f805d06e53b3dc8ece2fcce5433309c4b30fb28158cf0bac67c0bf285f
    afcc82d54ef92ecb27aba30fb8671cad7bf10c2149662ce474e261d7e9373ab3
    9690f8eba61630ffb09fb7432aa973ba71ba38efd1da7c8ca397834f09a86fc3). Do NOT edit their bodies.
  * The module-level `__version__ = '0.2.0'` line is NOT vendored (this
    docstring carries the version); the functions reference nothing else
    at module level.

Authenticity (2026-07-29, Python 3.9.25): verify('356938035643809') =
True, verify('534618613411236') = False, generate('35693803564380') = 9,
append('53461861341123') = '534618613411234' computed against this file
AND against the unpacked luhn-0.2.0 sdist module -- both agree.
"""

def checksum(string):
    """
    Compute the Luhn checksum for the provided string of digits. Note this
    assumes the check digit is in place.
    """
    digits = list(map(int, string))
    odd_sum = sum(digits[-1::-2])
    even_sum = sum([sum(divmod(2 * d, 10)) for d in digits[-2::-2]])
    return (odd_sum + even_sum) % 10

def verify(string):
    """
    Check if the provided string of digits satisfies the Luhn checksum.

    >>> verify('356938035643809')
    True
    >>> verify('534618613411236')
    False
    """
    return (checksum(string) == 0)

def generate(string):
    """
    Generate the Luhn check digit to append to the provided string.

    >>> generate('35693803564380')
    9
    >>> generate('53461861341123')
    4
    """
    cksum = checksum(string + '0')
    return (10 - cksum) % 10

def append(string):
    """
    Append Luhn check digit to the end of the provided string.

    >>> append('53461861341123')
    '534618613411234'
    """
    return string + str(generate(string))
