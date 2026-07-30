"""Luhn / Luhn mod N (python-stdnum), vendored verbatim for the Lean
verification benchmark (Band B: the credit-card check-digit algorithm).

Provenance:
  package : python-stdnum, https://pypi.org/project/python-stdnum/
  version : 2.2 (pip download --no-deps python-stdnum, 2026-07-21; sdist
            python_stdnum-2.2.tar.gz, sha256
            e95fcfa858a703d4a40130cb3eaac133c60d8808a7f3c98efeedac968c2479b9)
  file    : stdnum/luhn.py, sha256
            ac87edae3e770d11a508c9a15bb4c80abb34772cc3044c34aa4ca85e647594d8
  license : LGPL-2.1-or-later. The functions below are Copyright (C)
            2010-2021 Arthur de Jong, licensed under the GNU Lesser
            General Public License version 2.1 or later.

Vendoring rules (python benchmark, Examples/python/bench_stdnum_luhn):
  * checksum, validate, is_valid and calc_check_digit are BYTE-VERBATIM
    copies of stdnum/luhn.py 2.2 lines 52-60, 63-73, 76-81 and 84-88
    (sha256 of the four segments:
    7e11a3fedee946be4a84b45a054c04637a184116c9dc7e13542b817c959419c2
    520a4bbe569aefd60ec16fb019ed38353916fcd3aa1e4973fc0eabebb723097d
    b64c83e7cb727bf1bfea1858eb944a765d0d13d9cf7dce2b0b995d331abd9e78
    7a3e5da5652b643c1621c090af7b08964d37370123d41d22538159c26227de36). Do NOT edit their bodies.
  * The stdnum exception classes (InvalidFormat, InvalidChecksum,
    ValidationError; from `from stdnum.exceptions import *`) are NOT
    vendored: each occurs only inside a raise statement or an except
    clause, i.e. on invalid-input or error paths -- no valid-input run
    evaluates the names (same rule as Examples/python/rsa_inverse and its
    NotRelativePrimeError).
  * `from __future__ import annotations` IS retained from the original
    module (its own line-range segment below): it makes the `str`/`int`
    parameter annotations lazy at def time, exactly as in the original.
  * All four functions take `alphabet: str = '0123456789'` -- a constant
    string default (the Luhn mod N generalization).

Authenticity (2026-07-29, Python 3.9.25): checksum('7894') = 6,
calc_check_digit('7894') = '9', validate('78949') = '78949',
checksum('1234', alphabet='0123456789abcdef') = 14 computed against this
file AND against the unpacked python_stdnum-2.2 sdist package -- both
agree.
"""

from __future__ import annotations

def checksum(number: str, alphabet: str = '0123456789') -> int:
    """Calculate the Luhn checksum over the provided number. The checksum
    is returned as an int. Valid numbers should have a checksum of 0."""
    n = len(alphabet)
    values = tuple(alphabet.index(i)
                   for i in reversed(str(number)))
    return (sum(values[::2]) +
            sum(sum(divmod(i * 2, n))
                for i in values[1::2])) % n

def validate(number: str, alphabet: str = '0123456789') -> str:
    """Check if the number provided passes the Luhn checksum."""
    if not bool(number):
        raise InvalidFormat()
    try:
        valid = checksum(number, alphabet) == 0
    except Exception:  # noqa: B902
        raise InvalidFormat()
    if not valid:
        raise InvalidChecksum()
    return number

def is_valid(number: str, alphabet: str = '0123456789') -> bool:
    """Check if the number passes the Luhn checksum."""
    try:
        return bool(validate(number, alphabet))
    except ValidationError:
        return False

def calc_check_digit(number: str, alphabet: str = '0123456789') -> str:
    """Calculate the extra digit that should be appended to the number to
    make it a valid number."""
    ck = checksum(str(number) + alphabet[0], alphabet)
    return alphabet[-ck]
